//! Arena allocation.

use std::alloc::{self, Layout};
use std::cell::UnsafeCell;
use std::fmt::Debug;
use std::marker::PhantomData;
use std::mem::{self, MaybeUninit};
use std::ops::Mul;
use std::ptr::{self, NonNull};
use std::sync::RwLock;
use std::sync::atomic::{AtomicPtr, AtomicUsize, Ordering};

#[cfg(test)]
mod test;

const MIN_CHUNK_BYTES: ByteSize = ByteSize(4096); // 4 KiB
const MAX_CHUNK_BYTES: ByteSize = ByteSize(1 << 22); // 4 MiB
const MIN_ALIGN: usize = mem::align_of::<usize>();

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct ByteSize(usize);

impl ByteSize {
    fn min_with_capacity<T>(cap: Capacity<T>) -> Self {
        Self(cap.layout_for().size())
    }

    fn max_capacity<T>(self) -> Capacity<T> {
        Capacity::max_within_bytes(self)
    }
}

impl Mul<usize> for ByteSize {
    type Output = Self;

    fn mul(self, rhs: usize) -> Self::Output {
        Self(self.0 * rhs)
    }
}

struct Capacity<T>(usize, PhantomData<fn(T)>);

impl<T> Capacity<T> {
    fn new(cap: usize) -> Self {
        Self(cap, PhantomData)
    }

    fn max_within_bytes(bytes: ByteSize) -> Self {
        let size = Layout::new::<T>().pad_to_align().size();
        Self::new(bytes.0 / size)
    }

    fn layout_for(self) -> Layout {
        Layout::new::<T>()
            .repeat(self.0)
            .unwrap()
            .0
            .align_to(MIN_ALIGN)
            .unwrap()
    }

    fn byte_size(self) -> ByteSize {
        ByteSize::min_with_capacity(self)
    }
}

trait PtrAddCap<T> {
    unsafe fn add_capacity(self, capacity: Capacity<T>) -> Self;
    unsafe fn add_bytes(self, bytes: ByteSize) -> Self;
    unsafe fn sub_ptr_capacity(self, other: Self) -> Capacity<T>;
}

impl<T> PtrAddCap<T> for *mut T {
    unsafe fn add_capacity(self, capacity: Capacity<T>) -> Self {
        unsafe { self.add(capacity.0) }
    }

    unsafe fn add_bytes(self, bytes: ByteSize) -> Self {
        unsafe { self.byte_add(bytes.0) }
    }

    unsafe fn sub_ptr_capacity(self, other: Self) -> Capacity<T> {
        unsafe { Capacity::new(self.offset_from_unsigned(other)) }
    }
}

impl<T> Debug for Capacity<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("Capacity").field(&self.0).finish()
    }
}

impl<T> Clone for Capacity<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for Capacity<T> {}

impl<T> PartialEq for Capacity<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<T> Eq for Capacity<T> {}

impl<T> PartialOrd for Capacity<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.0.cmp(&other.0))
    }
}

impl<T> Ord for Capacity<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.cmp(&other.0)
    }
}

struct ArenaChunk<T> {
    storage: NonNull<[MaybeUninit<T>]>,
    occupied: usize,
}

fn alloc_chunk<T>(capacity: Capacity<T>) -> NonNull<[MaybeUninit<T>]> {
    debug_assert!(mem::size_of::<T>() > 0);
    unsafe {
        let layout = capacity.layout_for();
        let storage_ptr = alloc::alloc(layout);
        if storage_ptr.is_null() {
            alloc::handle_alloc_error(layout);
        }
        let storage_ptr =
            ptr::slice_from_raw_parts_mut(storage_ptr as *mut MaybeUninit<T>, capacity.0);
        debug_println!(@"allocated chunk {capacity:?}, storage {storage_ptr:p}");
        NonNull::new_unchecked(storage_ptr)
    }
}

unsafe fn dealloc_chunk<T>(storage: NonNull<[MaybeUninit<T>]>) {
    debug_assert!(mem::size_of::<T>() > 0);
    debug_println!(@"deallocating chunk, storage {storage:p}");
    let storage_ptr = storage.as_ptr();
    let capacity = Capacity::<T>::new(ptr::metadata(storage_ptr));
    debug_println!(@"=> found to be {capacity:?}");
    let layout = capacity.layout_for();

    unsafe {
        alloc::dealloc(storage_ptr as *mut u8, layout);
    }
}

impl<T> ArenaChunk<T> {
    fn new(capacity: Capacity<T>) -> Self {
        Self {
            storage: alloc_chunk(capacity),
            occupied: 0,
        }
    }

    fn get_storage_ptr(&mut self) -> *mut T {
        self.get_storage()[0].as_mut_ptr()
    }

    fn get_storage(&mut self) -> &mut [MaybeUninit<T>] {
        unsafe { &mut *self.storage.as_ptr() }
    }

    fn capacity(&self) -> Capacity<T> {
        Capacity::new(ptr::metadata(self.storage.as_ptr()))
    }

    unsafe fn drop_occupied(&mut self) {
        unsafe {
            for item in &mut (*self.storage.as_ptr())[..self.occupied] {
                item.assume_init_drop();
            }
        }
    }
}

impl<T> Drop for ArenaChunk<T> {
    fn drop(&mut self) {
        unsafe {
            debug_println!(@"dropping chunk {:p} {:?}", self.storage, self.capacity());
            dealloc_chunk(self.storage);
        }
    }
}

struct RangePointers<T> {
    start: AtomicPtr<T>,
    end: *mut T,
}

impl<T> RangePointers<T> {
    fn new() -> Self {
        Self {
            start: AtomicPtr::new(ptr::null_mut()),
            end: ptr::null_mut(),
        }
    }

    fn item_ptr(&self, min_cap: Capacity<T>) -> Option<*mut T> {
        debug_assert!(mem::size_of::<T>() > 0);
        debug_println!(@
            "getting item ptr for {min_cap:?} {}",
            std::any::type_name::<T>()
        );
        self.start
            .fetch_update(Ordering::AcqRel, Ordering::Acquire, |start| unsafe {
                if self.end.offset_from_unsigned(start) < min_cap.0 {
                    debug_println!(@"=> insufficient capacity");
                    None
                } else {
                    Some(start.add_capacity(min_cap))
                }
            })
            .ok()
    }

    /// Returns the previous value of the start pointer
    fn set_new_chunk(&mut self, new_chunk: &mut ArenaChunk<T>) -> *mut T {
        let start = self.start.get_mut();
        let prev_start = *start;
        *start = new_chunk.get_storage_ptr();
        self.end = unsafe { start.add_capacity(new_chunk.capacity()) };
        debug_println!(@"=> new start {:p} end {:p}", *start, self.end,);
        debug_println!(@"=> prev start {prev_start:p}");
        prev_start
    }

    fn current_capacity(&mut self) -> Capacity<T> {
        unsafe { self.end.sub_ptr_capacity(*self.start.get_mut()) }
    }

    fn current_start(&mut self) -> *mut T {
        *self.start.get_mut()
    }
}

impl RangePointers<u8> {
    fn item_ptr_aligned<T: Copy>(&self, min_cap: Capacity<T>) -> Option<*mut T> {
        debug_assert!(mem::size_of::<T>() > 0);
        let align = const { mem::align_of::<T>() };
        debug_println!(@
            "getting aligned item ptr for {min_cap:?} {} (align {align})",
            std::any::type_name::<T>(),
        );
        let mut aligned_addr = 0;
        let unaligned_ptr = self
            .start
            .fetch_update(Ordering::AcqRel, Ordering::Acquire, |start| unsafe {
                aligned_addr = align_up(start.addr(), align);
                let aligned_start = start.with_addr(aligned_addr);
                if self.end.sub_ptr_capacity(aligned_start).byte_size() < min_cap.byte_size() {
                    debug_println!(@"=> insufficient capacity");
                    None
                } else {
                    Some(aligned_start.add_bytes(min_cap.byte_size()))
                }
            })
            .ok()?;
        debug_println!(@"=> unaligned {unaligned_ptr:p}");
        Some(unaligned_ptr.with_addr(aligned_addr) as *mut T)
    }
}

struct ArenaCore<T> {
    chunks: UnsafeCell<Vec<ArenaChunk<T>>>,
    prev_cap: AtomicUsize,
    pointers: RwLock<RangePointers<T>>,
}

unsafe impl<T: Send> Send for ArenaCore<T> {}
unsafe impl<T: Sync> Sync for ArenaCore<T> {}

impl<T> ArenaCore<T> {
    fn new() -> Self {
        Self {
            chunks: UnsafeCell::new(Vec::new()),
            prev_cap: AtomicUsize::new(0),
            pointers: RwLock::new(RangePointers::new()),
        }
    }

    fn grow(&self, min_capacity: Capacity<T>) {
        debug_println!(@"growing arena, min additional {min_capacity:?}");
        debug_assert!(mem::size_of::<T>() > 0);
        unsafe {
            // TODO? Probably not worth it, but could potentially allow other threads to allocate in
            // the old chunk while we work out all this arithmetic?
            let mut pointers = self.pointers.write().unwrap();

            if pointers.current_capacity() >= min_capacity {
                return;
            }

            let chunks = &mut *self.chunks.get();
            let prev_bytes = if let Some(last) = chunks.last() {
                last.capacity().byte_size()
            } else {
                ByteSize(0)
            };
            let min_bytes = min_capacity.byte_size();

            let next_bytes = (prev_bytes * 2)
                .clamp(MIN_CHUNK_BYTES, MAX_CHUNK_BYTES)
                .max(min_bytes);

            debug_assert!(next_bytes >= MIN_CHUNK_BYTES);
            debug_assert!(min_bytes > MAX_CHUNK_BYTES || next_bytes <= MAX_CHUNK_BYTES);

            let next_capacity = next_bytes.max_capacity::<T>();
            debug_println!(@"=> next {next_capacity:?} {next_bytes:?}");

            let mut chunk = ArenaChunk::new(next_capacity);

            let prev_start = pointers.set_new_chunk(&mut chunk);

            if mem::needs_drop::<T>() {
                if let Some(last) = chunks.last_mut() {
                    let storage_start = last.get_storage_ptr();
                    last.occupied = prev_start.offset_from_unsigned(storage_start);
                    debug_println!(@
                        "=> prev chunk ({:p}) {} occupied",
                        last.get_storage_ptr(),
                        last.occupied,
                    );
                }
            }

            chunks.push(chunk);
        }
    }

    fn item_ptr(&self, min_capacity: Capacity<T>) -> *mut T {
        loop {
            // Do this in two steps to make sure the read guard is dropped before we grow
            let start_pointer = self.pointers.read().unwrap().item_ptr(min_capacity);
            if let Some(start) = start_pointer {
                debug_println!(@"item ptr {start:p}");
                break start;
            } else {
                self.grow(min_capacity);
            }
        }
    }

    fn alloc(&self, item: T) -> *const T {
        if mem::size_of::<T>() == 0 {
            #[allow(unused_variables)]
            let prev_cap = self.prev_cap.fetch_add(1, Ordering::AcqRel);
            debug_println!(@"allocating ZST, prev cap {prev_cap}");
            if mem::needs_drop::<T>() {
                mem::forget(item); // Will be dropped later
            }
            return ptr::dangling();
        }

        unsafe {
            let item_ptr = self.item_ptr(Capacity::new(1));
            ptr::write(item_ptr, item);
            item_ptr
        }
    }

    fn alloc_from_iter(&self, iter: impl IntoIterator<Item = T>) -> *const [T] {
        let items = iter.into_iter().collect::<Vec<_>>();

        if mem::size_of::<T>() == 0 {
            #[allow(unused_variables)]
            let prev_cap = self.prev_cap.fetch_add(items.len(), Ordering::AcqRel);
            debug_println!(@"allocating {} ZSTs, prev cap {prev_cap}", items.len());
            let res = ptr::slice_from_raw_parts(ptr::dangling(), items.len());
            if mem::needs_drop::<T>() {
                for item in items {
                    mem::forget(item); // We'll summon them from the ether to drop later
                }
            }
            return res;
        }

        let cap = Capacity::new(items.len());
        unsafe {
            let start_ptr = self.item_ptr(cap);

            let mut item_ptr = start_ptr;
            for item in items {
                ptr::write(item_ptr, item);
                item_ptr = item_ptr.add(1);
            }

            ptr::slice_from_raw_parts(start_ptr, cap.0)
        }
    }

    fn drop_last_chunk(&mut self) {
        unsafe {
            let chunks = &mut *self.chunks.get();
            if let Some(last) = chunks.last_mut() {
                let mut item = last.get_storage_ptr();
                let first_unoccupied = self.pointers.get_mut().unwrap().current_start();
                while item < first_unoccupied {
                    ptr::drop_in_place(item);
                    item = item.add(1);
                }
            }
        }
    }

    fn drop_chunks(&mut self) {
        if !mem::needs_drop::<T>() {
            return;
        }

        if mem::size_of::<T>() == 0 {
            unsafe {
                debug_println!(@
                    "dropping arena of ZSTs, allocated cap is {}",
                    *self.prev_cap.get_mut(),
                );
                debug_assert!((*self.chunks.get()).is_empty());
                for _ in 0..*self.prev_cap.get_mut() {
                    ptr::drop_in_place(ptr::dangling_mut::<T>());
                }
                return;
            }
        }

        unsafe {
            self.drop_last_chunk();
            let chunks = &mut *self.chunks.get();
            let n_chunks = chunks.len();
            if n_chunks > 1 {
                for chunk in &mut chunks[..n_chunks - 1] {
                    chunk.drop_occupied();
                }
            }
        }
    }
}

impl<T: Copy> ArenaCore<T> {
    fn alloc_from_slice(&self, items: &[T]) -> *const [T] {
        if mem::size_of::<T>() == 0 {
            debug_println!(@"allocating {} Copy ZSTs, no change to cap", items.len());
            return ptr::slice_from_raw_parts(ptr::dangling(), items.len());
        }

        unsafe {
            let start_ptr = self.item_ptr(Capacity::new(items.len()));
            ptr::copy_nonoverlapping(items.as_ptr(), start_ptr, items.len());
            ptr::slice_from_raw_parts(start_ptr, items.len())
        }
    }
}

fn align_up(addr: usize, align: usize) -> usize {
    debug_assert!(align.is_power_of_two());
    (addr + align - 1) & !(align - 1)
}

#[inline(always)]
fn assert_nondrop<T>() {
    assert!(
        !mem::needs_drop::<T>(),
        "cannot allocate {} on dropless arena, since it needs drop",
        std::any::type_name::<T>(),
    );
}

impl ArenaCore<u8> {
    fn item_ptr_aligned<T: Copy>(&self, min_cap: Capacity<T>) -> *mut T {
        loop {
            // Do this in two steps to make sure the read guard is dropped before we grow
            let item_ptr = self.pointers.read().unwrap().item_ptr_aligned(min_cap);
            if let Some(item_ptr) = item_ptr {
                break item_ptr;
            } else {
                self.grow(min_cap.byte_size().max_capacity());
            }
        }
    }

    fn alloc_nondrop<T: Copy>(&self, item: T) -> *const T {
        assert_nondrop::<T>();

        if mem::size_of::<T>() == 0 {
            debug_println!(@"allocating nondrop ZST, returning dangling ptr");
            return ptr::dangling();
        }

        unsafe {
            let item_ptr = self.item_ptr_aligned(Capacity::<T>::new(1));
            debug_assert!(item_ptr.is_aligned());
            ptr::write(item_ptr, item);
            item_ptr
        }
    }

    fn alloc_nondrop_from_iter<T: Copy>(&self, items: impl IntoIterator<Item = T>) -> *const [T] {
        let items = items.into_iter().collect::<Vec<_>>();
        self.alloc_nondrop_from_slice(&items)
    }

    fn alloc_nondrop_from_slice<T: Copy>(&self, items: &[T]) -> *const [T] {
        assert_nondrop::<T>();

        if mem::size_of::<T>() == 0 {
            debug_println!(@
                "allocating slice of {} nondrop ZSTs, returning dangling ptr",
                items.len(),
            );
            return ptr::slice_from_raw_parts(ptr::dangling(), items.len());
        }

        unsafe {
            debug_println!(@
                "allocating nondrop {} from slice",
                std::any::type_name::<T>()
            );
            let item_ptr = self.item_ptr_aligned(Capacity::<T>::new(items.len()));
            debug_println!(@"=> aligned item ptr {item_ptr:p}");
            debug_assert!(item_ptr.is_aligned());
            ptr::copy_nonoverlapping(items.as_ptr(), item_ptr, items.len());
            ptr::slice_from_raw_parts(item_ptr, items.len())
        }
    }
}

pub struct DroplessArena {
    core: ArenaCore<u8>,
}

impl Default for DroplessArena {
    fn default() -> Self {
        Self::new()
    }
}

impl DroplessArena {
    pub fn new() -> Self {
        Self {
            core: ArenaCore::new(),
        }
    }

    pub fn alloc<T: Copy>(&self, item: T) -> &T {
        unsafe { &*self.core.alloc_nondrop(item) }
    }

    pub fn alloc_from_iter<T: Copy>(&self, items: impl IntoIterator<Item = T>) -> &[T] {
        unsafe { &*self.core.alloc_nondrop_from_iter(items) }
    }

    pub fn alloc_from_slice<T: Copy>(&self, items: &[T]) -> &[T] {
        unsafe { &*self.core.alloc_nondrop_from_slice(items) }
    }

    pub fn alloc_bytes(&self, bytes: &[u8]) -> &[u8] {
        unsafe { &*self.core.alloc_from_slice(bytes) }
    }

    pub fn alloc_str(&self, s: &str) -> &str {
        unsafe {
            let bytes = self.alloc_bytes(s.as_bytes());
            std::str::from_utf8_unchecked(bytes)
        }
    }
}

pub struct TypedArena<T> {
    core: ArenaCore<T>,
}

impl<T> Default for TypedArena<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> TypedArena<T> {
    pub fn new() -> Self {
        Self {
            core: ArenaCore::new(),
        }
    }

    pub fn alloc(&self, item: T) -> &T {
        unsafe { &*self.core.alloc(item) }
    }

    pub fn alloc_from_iter(&self, items: impl IntoIterator<Item = T>) -> &[T] {
        unsafe { &*self.core.alloc_from_iter(items) }
    }
}

impl<T> Drop for TypedArena<T> {
    fn drop(&mut self) {
        self.core.drop_chunks();
    }
}
