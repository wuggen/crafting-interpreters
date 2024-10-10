//! Arena allocation.

use std::alloc::{self, Layout};
use std::marker::PhantomData;
use std::mem::{self, MaybeUninit};
use std::ptr::{self, NonNull};
use std::slice::SliceIndex;
use std::sync::Mutex;

const MIN_ALIGN: usize = mem::align_of::<usize>();
const MIN_CHUNK_SIZE: usize = 4096;
const MAX_CHUNK_SIZE: usize = 2 << 20;

#[cfg(test)]
mod test;

struct ArenaChunk<T> {
    storage: NonNull<[MaybeUninit<T>]>,
    occupied: usize,
}

impl<T> ArenaChunk<T> {
    fn layout(capacity: usize) -> Layout {
        Layout::new::<T>()
            .repeat(capacity)
            .unwrap()
            .0
            .align_to(MIN_ALIGN)
            .unwrap()
    }

    fn alloc_aligned(capacity: usize) -> NonNull<[MaybeUninit<T>]> {
        unsafe {
            let layout = Self::layout(capacity);
            let ptr = alloc::alloc(layout);
            if ptr.is_null() {
                alloc::handle_alloc_error(layout);
            }

            let ptr = ptr::slice_from_raw_parts_mut(ptr as *mut MaybeUninit<T>, capacity);
            NonNull::new_unchecked(ptr)
        }
    }

    fn new(capacity: usize) -> Self {
        Self {
            storage: Self::alloc_aligned(capacity),
            occupied: 0,
        }
    }

    /// Safety: `self.occupied` must accurately reflect the number of occupied items
    unsafe fn drop_occupied(&mut self) {
        if mem::needs_drop::<T>() {
            for occupied in self.get(..self.occupied) {
                occupied.assume_init_drop();
            }
            self.occupied = 0;
        }
    }

    /// Safety: the index must not exceed the bounds of the chunk's capacity.
    unsafe fn get<I: SliceIndex<[MaybeUninit<T>]>>(&mut self, index: I) -> &mut I::Output {
        &mut *self.storage.get_unchecked_mut(index).as_ptr()
    }

    /// Safety: the index must not exceed the bounds of the chunk's capacity.
    unsafe fn ptr_to_index(&mut self, index: usize) -> *mut T {
        self.storage.as_non_null_ptr().add(index).as_ptr() as *mut T
    }

    fn start(&mut self) -> *mut T {
        unsafe { self.ptr_to_index(0) }
    }
}

unsafe impl<#[may_dangle] T> Drop for ArenaChunk<T> {
    fn drop(&mut self) {
        unsafe {
            let layout = Layout::for_value_raw(self.storage.as_ptr())
                .align_to(MIN_ALIGN)
                .unwrap();
            alloc::dealloc(self.storage.as_ptr() as *mut u8, layout);
        }
    }
}

struct ArenaCore<T> {
    chunks: Vec<ArenaChunk<T>>,
    cursor: *mut T,
    end: *mut T,
}

impl<T> Default for ArenaCore<T> {
    fn default() -> Self {
        Self {
            chunks: Vec::new(),
            cursor: ptr::null_mut(),
            end: ptr::null_mut(),
        }
    }
}

impl<T> ArenaCore<T> {
    fn prev_size(&self) -> usize {
        self.chunks.last().map(|ch| ch.storage.len()).unwrap_or(0)
    }

    fn remaining(&self) -> usize {
        unsafe { self.end.sub_ptr(self.cursor) }
    }

    fn next_chunk_size(&self, min: usize) -> usize {
        let aligned_min = min.next_power_of_two();

        let tentative = MIN_CHUNK_SIZE.max(self.prev_size() * 2);
        let default = if tentative > MAX_CHUNK_SIZE {
            MAX_CHUNK_SIZE
        } else {
            tentative
        };

        let next_size = default.max(aligned_min);
        debug_assert!(next_size.is_power_of_two());
        next_size
    }

    fn grow(&mut self, min_size: usize) {
        if mem::needs_drop::<T>() {
            if let Some(last) = self.chunks.last_mut() {
                unsafe {
                    let start = last.start();
                    last.occupied = self.cursor.sub_ptr(start);
                }
            }
        }

        let next_size = self.next_chunk_size(min_size);
        let mut chunk = ArenaChunk::<T>::new(next_size);
        let start = chunk.start();
        let end = unsafe { start.add(chunk.storage.len()) };
        self.cursor = start;
        self.cursor = end;
        self.chunks.push(chunk);
    }

    fn allocate(&mut self, item: T) -> *mut T {
        if self.cursor >= self.end {
            self.grow(1);
        }

        unsafe {
            let item_ptr = self.cursor;
            self.cursor = self.cursor.add(1);
            ptr::write(item_ptr, item);
            item_ptr
        }
    }

    fn allocate_from_iterator(&mut self, iter: impl IntoIterator<Item = T>) -> *mut [T] {
        let items = iter.into_iter().collect::<Vec<_>>();
        let num = items.len();

        if self.remaining() < num {
            self.grow(num);
        }

        let item_ptr = self.cursor;

        for item in items {
            self.allocate(item);
        }

        ptr::slice_from_raw_parts_mut(item_ptr, num)
    }

    fn allocate_from_slice(&mut self, items: &[T]) -> *mut [T]
    where
        T: Copy,
    {
        unsafe {
            if self.remaining() < items.len() {
                self.grow(items.len());
            }
            let item_ptr = self.cursor;
            ptr::copy_nonoverlapping(items.as_ptr(), self.cursor, items.len());
            self.cursor = self.cursor.add(items.len());
            ptr::slice_from_raw_parts_mut(item_ptr, items.len())
        }
    }

    fn drop_all(&mut self) {
        if !mem::needs_drop::<T>() {
            return;
        }

        self.drop_last_chunk();

        unsafe {
            if self.chunks.len() > 1 {
                let len = self.chunks.len();
                for chunk in &mut self.chunks[..len - 1] {
                    chunk.drop_occupied();
                }
            }
        }
    }

    fn drop_last_chunk(&mut self) {
        if !mem::needs_drop::<T>() {
            return;
        }

        unsafe {
            if let Some(last) = self.chunks.last_mut() {
                let start = last.start() as *mut T;
                let occupied = self.cursor.sub_ptr(start);
                for item in last.get(..occupied) {
                    item.assume_init_drop();
                }
            }
        }
    }
}

impl ArenaCore<u8> {
    /// Safety: adjusting the alignment up must not push the cursor past the end pointer.
    unsafe fn align_cursor_up(&mut self, align: usize) {
        let addr = self.cursor.addr();
        let new_addr = align_up(addr, align);
        self.cursor = self.cursor.with_addr(new_addr);
        debug_assert!(self.cursor <= self.end);
    }

    fn allocate_copy<T: Copy>(&mut self, item: T) -> *mut T {
        debug_assert!(self.remaining() <= mem::size_of::<T>());
        let layout = Layout::new::<T>();
        self.align_and_grow(layout);

        unsafe {
            let item_ptr = self.cursor as *mut T;
            debug_assert!(item_ptr.is_aligned());
            self.cursor = self.cursor.add(mem::size_of::<T>());

            ptr::write(item_ptr, item);
            item_ptr
        }
    }

    fn copy_from_slice<T: Copy>(&mut self, items: &[T]) -> *mut [T] {
        let layout = Layout::for_value(items);
        self.align_and_grow(layout);

        unsafe {
            let item_ptr = self.cursor as *mut T;
            debug_assert!(item_ptr.is_aligned());
            self.cursor = self.cursor.add(layout.size());

            ptr::copy_nonoverlapping(items.as_ptr(), item_ptr, items.len());
            ptr::slice_from_raw_parts_mut(item_ptr, items.len())
        }
    }

    fn align_and_grow(&mut self, layout: Layout) {
        unsafe {
            loop {
                self.align_cursor_up(layout.align());
                if self.remaining() < layout.size() {
                    self.grow(layout.pad_to_align().size());
                } else {
                    break;
                }
            }
        }
    }
}

fn align_up(addr: usize, align: usize) -> usize {
    assert!(align.is_power_of_two());
    (addr + align - 1) & !(align - 1)
}

#[derive(Default)]
pub struct DroplessArena {
    core: Mutex<ArenaCore<u8>>,
}

impl DroplessArena {
    pub fn new() -> Self {
        Self::default()
    }

    fn check_drop<T: Copy>() {
        assert!(
            !mem::needs_drop::<T>(),
            "cannot allocate {} on a dropless arena because it has drop glue",
            std::any::type_name::<T>(),
        )
    }

    fn with_core<R>(&self, f: impl FnOnce(&mut ArenaCore<u8>) -> R) -> R {
        f(&mut self.core.lock().unwrap())
    }

    pub fn allocate<T: Copy>(&self, item: T) -> &T {
        Self::check_drop::<T>();
        self.with_core(|core| unsafe { &*core.allocate_copy(item) })
    }

    pub fn allocate_bytes(&self, bytes: &[u8]) -> &[u8] {
        self.with_core(|core| unsafe { &*core.allocate_from_slice(bytes) })
    }

    pub fn allocate_from_slice<T: Copy>(&self, items: &[T]) -> &[T] {
        Self::check_drop::<T>();
        self.with_core(|core| unsafe { &*core.copy_from_slice(items) })
    }

    pub fn allocate_str(&self, s: &str) -> &str {
        unsafe { std::str::from_utf8_unchecked(self.allocate_bytes(s.as_bytes())) }
    }
}

pub struct TypedArena<T> {
    core: Mutex<ArenaCore<T>>,
    _drops_t: PhantomData<T>,
}

impl<T> Default for TypedArena<T> {
    fn default() -> Self {
        Self {
            core: Mutex::default(),
            _drops_t: PhantomData,
        }
    }
}

impl<T> Drop for TypedArena<T> {
    fn drop(&mut self) {
        if mem::needs_drop::<T>() {
            self.core.lock().unwrap().drop_all();
        }
    }
}

impl<T> TypedArena<T> {
    pub fn new() -> Self {
        Self::default()
    }

    fn with_core<R>(&self, f: impl FnOnce(&mut ArenaCore<T>) -> R) -> R {
        f(&mut self.core.lock().unwrap())
    }

    pub fn allocate(&self, item: T) -> &T {
        self.with_core(|core| unsafe { &*core.allocate(item) })
    }

    pub fn allocate_from_iter(&self, items: impl IntoIterator<Item = T>) -> &[T] {
        self.with_core(|core| unsafe { &*core.allocate_from_iterator(items) })
    }

    pub fn allocate_from_slice(&self, items: &[T]) -> &[T]
    where
        T: Copy,
    {
        self.with_core(|core| unsafe { &*core.allocate_from_slice(items) })
    }
}

