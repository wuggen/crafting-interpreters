//! Interned data.

use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};
use std::any::{Any, TypeId};
use std::borrow::Borrow;
use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;
use std::mem::MaybeUninit;
use std::ops::{Deref, Range};
use std::ptr::NonNull;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Mutex, RwLock};

pub struct Interned<T: ?Sized> {
    item: NonNull<T>,
}

impl<T: ?Sized> Clone for Interned<T> {
    fn clone(&self) -> Self {
        Self { item: self.item }
    }
}

impl<T: ?Sized> Copy for Interned<T> {}

impl<T: ?Sized> PartialEq for Interned<T> {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.item.as_ptr(), other.item.as_ptr())
    }
}

impl<T: ?Sized> Eq for Interned<T> {}

impl<T: ?Sized> AsRef<T> for Interned<T> {
    fn as_ref(&self) -> &T {
        self
    }
}

impl<T: ?Sized> Deref for Interned<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { self.item.as_ref() }
    }
}

impl<T: ?Sized> Interned<T> {
    unsafe fn drop_item(&self) {
        self.item.drop_in_place();
    }
}

pub unsafe trait Internable: Any {
    fn bytes(&self) -> usize;

    fn alignment() -> usize;

    fn ptr(&self) -> *const u8;

    fn hash<H: Hasher>(&self, state: &mut H);

    fn eq(&self, other: &Self) -> bool;

    fn write(&self, buf: &mut [MaybeUninit<u8>]) {
        assert!(buf.len() >= self.bytes());
        let self_ptr = self.ptr();
        let buf_ptr = buf.as_mut_ptr() as *mut u8;
        unsafe {
            std::ptr::copy_nonoverlapping(self_ptr, buf_ptr, self.bytes());
        }
    }
}

unsafe impl<T> Internable for T
where
    T: Sized + Copy + Hash + Eq + Any,
{
    fn bytes(&self) -> usize {
        std::mem::size_of::<Self>()
    }

    fn alignment() -> usize {
        std::mem::align_of::<Self>()
    }

    fn ptr(&self) -> *const u8 {
        self as *const _ as *const u8
    }

    fn hash<H: Hasher>(&self, state: &mut H) {
        <Self as Hash>::hash(self, state)
    }

    fn eq(&self, other: &Self) -> bool {
        self == other
    }
}

unsafe impl Internable for str {
    fn bytes(&self) -> usize {
        self.len()
    }

    fn alignment() -> usize {
        1
    }

    fn ptr(&self) -> *const u8 {
        self.as_ptr()
    }

    fn hash<H: Hasher>(&self, state: &mut H) {
        <Self as Hash>::hash(self, state);
    }

    fn eq(&self, other: &Self) -> bool {
        self == other
    }
}

unsafe impl Internable for [u8] {
    fn bytes(&self) -> usize {
        self.len()
    }

    fn alignment() -> usize {
        1
    }

    fn ptr(&self) -> *const u8 {
        self.as_ptr()
    }

    fn hash<H: Hasher>(&self, state: &mut H) {
        <[u8] as Hash>::hash(self, state);
    }

    fn eq(&self, other: &Self) -> bool {
        self == other
    }
}

struct ArenaChunk<T: Internable + ?Sized> {
    mem: *mut MaybeUninit<u8>,
    size: usize,
    cursor: AtomicUsize,
    _dummy: PhantomData<[&'static T]>,
}

impl<T: Internable + ?Sized> Drop for ArenaChunk<T> {
    fn drop(&mut self) {
        let align = T::alignment();
        unsafe {
            let layout = Layout::from_size_align_unchecked(self.size, align);
            dealloc(self.mem as *mut u8, layout);
        }
    }
}

#[inline]
fn round_up_cursor(cursor: usize, align: usize) -> usize {
    (cursor + align - 1) & !(align - 1)
}

impl<T: Internable + ?Sized> ArenaChunk<T> {
    fn new(size: usize) -> Self {
        assert!(size > 0);
        let align = T::alignment();
        let size = round_up_cursor(size, align);
        unsafe {
            let layout = Layout::from_size_align_unchecked(size, align);
            let mem = alloc(layout) as *mut MaybeUninit<u8>;
            if mem.is_null() {
                handle_alloc_error(layout);
            }

            let cursor = AtomicUsize::new(0);

            Self {
                mem,
                size,
                cursor,
                _dummy: PhantomData,
            }
        }
    }

    fn buf(&self, range: Range<usize>) -> &mut [MaybeUninit<u8>] {
        assert!(range.start <= range.end && range.end <= self.size);
        unsafe {
            let ptr = self.mem.offset(range.start.try_into().unwrap());
            let len = range.len();
            std::slice::from_raw_parts_mut(ptr, len)
        }
    }

    fn cursor_advance_or_fail(&self, size: usize) -> Option<usize> {
        let align = T::alignment();
        self.cursor
            .fetch_update(Ordering::Release, Ordering::Acquire, |cursor| {
                let new_cursor = round_up_cursor(cursor + size, align);
                if new_cursor <= self.size {
                    Some(new_cursor)
                } else {
                    None
                }
            })
            .ok()
    }

    fn interned_at(&self, pos: usize) -> Interned<T> {
        unsafe {
            let item = NonNull::new_unchecked(self.mem.offset(pos.try_into().unwrap()) as *mut T);
            Interned { item }
        }
    }

    fn allocate(&self, item: &T) -> Option<Interned<T>> {
        let size = item.bytes();
        let cursor = self.cursor_advance_or_fail(size)?;
        let end = cursor + size;
        item.write(self.buf(cursor..end));
        Some(self.interned_at(cursor))
    }
}

/// Wrapper for `Internable`-supported `Hash` and `Eq` implementations.
#[repr(transparent)]
struct InternedInternal<T: Internable + ?Sized> {
    item: Interned<T>,
}

impl<T: Internable + ?Sized> PartialEq for InternedInternal<T> {
    fn eq(&self, other: &Self) -> bool {
        <T as Internable>::eq(&self.item, &other.item)
    }
}

impl<T: Internable + ?Sized> Eq for InternedInternal<T> {}

impl<T: Internable + ?Sized> Hash for InternedInternal<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        <T as Internable>::hash(&self.item, state);
    }
}

#[repr(transparent)]
struct InternedLookup<T: Internable + ?Sized>(T);

impl<T: Internable + ?Sized> PartialEq for InternedLookup<T> {
    fn eq(&self, other: &Self) -> bool {
        <T as Internable>::eq(&self.0, &other.0)
    }
}

impl<T: Internable + ?Sized> Eq for InternedLookup<T> {}

impl<T: Internable + ?Sized> Hash for InternedLookup<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        <T as Internable>::hash(&self.0, state);
    }
}

impl<T: Internable + ?Sized> InternedLookup<T> {
    fn new(item: &T) -> &Self {
        unsafe { &*(item as *const T as *const Self) }
    }
}

impl<T: Internable + ?Sized> Borrow<InternedLookup<T>> for InternedInternal<T> {
    fn borrow(&self) -> &InternedLookup<T> {
        InternedLookup::new(&*self.item)
    }
}

struct Arena<T: Internable + ?Sized> {
    chunks: Vec<ArenaChunk<T>>,
    items: HashSet<InternedInternal<T>>,
}

impl<T: Internable + ?Sized> Arena<T> {
    const DEFAULT_CHUNK_SIZE: usize = 1024;

    fn new() -> Self {
        Self {
            chunks: vec![ArenaChunk::new(Self::DEFAULT_CHUNK_SIZE)],
            items: HashSet::new(),
        }
    }

    fn allocate(&mut self, item: &T) -> Interned<T> {
        let item = loop {
            if let Some(item) = self
                .chunks
                .iter()
                .rev()
                .filter_map(|chunk| chunk.allocate(item))
                .next()
            {
                break item;
            } else {
                self.chunks
                    .push(ArenaChunk::new(Self::DEFAULT_CHUNK_SIZE.max(item.bytes())));
            }
        };

        self.items.insert(InternedInternal { item });
        item
    }

    fn get_or_allocate(&mut self, item: &T) -> Interned<T> {
        self.items
            .get(InternedLookup::new(item))
            .map(|val| val.item)
            .unwrap_or_else(|| self.allocate(item))
    }

    fn untyped(self) -> ArenaUntyped {
        unsafe {
            let drop = |ptr| {
                let ptr = ptr as *mut Self;
                let layout = Layout::new::<Self>();
                std::ptr::drop_in_place(ptr);
                dealloc(ptr as *mut u8, layout);
            };

            let layout = Layout::new::<Self>();
            let arena = alloc(layout);
            if arena.is_null() {
                handle_alloc_error(layout);
            }

            ArenaUntyped {
                arena: arena as *mut (),
                drop,
            }
        }
    }
}

impl<T: Internable> Drop for Arena<T> {
    fn drop(&mut self) {
        for item in self.items.drain() {
            unsafe {
                item.item.drop_item();
            }
        }
    }
}

struct ArenaUntyped {
    arena: *mut (),
    drop: fn(*mut ()),
}

impl ArenaUntyped {
    unsafe fn typed<T: Internable>(&mut self) -> &mut Arena<T> {
        &mut *(self.arena as *mut Arena<T>)
    }
}

impl Drop for ArenaUntyped {
    fn drop(&mut self) {
        (self.drop)(self.arena)
    }
}

struct Arenas {
    arenas: RwLock<HashMap<TypeId, Mutex<ArenaUntyped>>>,
}

impl Arenas {
    fn new() -> Self {
        Self {
            arenas: RwLock::new(HashMap::new()),
        }
    }

    fn ensure_arena<T: Internable>(&self) {
        let id = TypeId::of::<T>();
        if !self.arenas.read().unwrap().contains_key(&id) {
            self.arenas
                .write()
                .unwrap()
                .entry(id)
                .or_insert_with(|| Mutex::new(Arena::<T>::new().untyped()));
        }
    }

    fn with_arena<T: Internable, R>(&self, f: impl FnOnce(&mut Arena<T>) -> R) -> R {
        self.ensure_arena::<T>();
        let id = TypeId::of::<T>();
        let arenas = self.arenas.read().unwrap();
        let mut arena = arenas.get(&id).unwrap().lock().unwrap();
        unsafe { f(arena.typed::<T>()) }
    }

    fn allocate<T: Internable>(&self, item: T) -> Interned<T> {
        self.with_arena::<T, _>(move |arena| arena.allocate(&item))
    }

    fn allocate_unsized<T: Internable + ?Sized>(&self, item: &T) -> Interned<T> {
        self.with_arena::<T, _>(|arena| arena.allocate(&item))
    }
}
