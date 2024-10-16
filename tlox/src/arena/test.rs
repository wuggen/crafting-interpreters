use std::{iter, thread};

use super::*;

#[test]
fn dropless_bytes() {
    eprintln!("dropless bytes");
    let arena = DroplessArena::new();
    let bytes = b"lol hey";
    let alloced_bytes = arena.alloc_bytes(bytes);
    assert_eq!(bytes, alloced_bytes);
}

#[test]
fn dropless_other() {
    let arena = DroplessArena::new();
    let numbers = std::iter::repeat_n(13_u64, 19).collect::<Vec<_>>();

    let alloced_numbers = arena.alloc_from_slice(&numbers);

    assert!(alloced_numbers.as_ptr().is_aligned());
    assert_eq!(numbers, alloced_numbers);
}

#[test]
fn dropless_zst() {
    let arena = DroplessArena::new();
    let unit = arena.alloc(());
    assert!((unit as *const ()).is_aligned());

    let units = arena.alloc_from_iter(std::iter::repeat_n((), 6));
    assert!(units.as_ptr().is_aligned());
}

#[test]
fn dropless_multiple_allocs() {
    let arena = DroplessArena::new();
    let bytes1 = b"lololololol";
    let bytes2 = b"hey so uh";
    let bytes3 = b"hhhhmmmmmmmmmmmmmmm????";

    assert_eq!(arena.alloc_bytes(bytes1), bytes1);
    assert_eq!(arena.alloc_bytes(bytes2), bytes2);
    assert_eq!(arena.alloc_bytes(bytes3), bytes3);
}

#[test]
fn dropless_multiple_chunks() {
    let arena = DroplessArena::new();
    let bytes = iter::repeat_n(42u8, 3072).collect::<Vec<_>>();
    arena.alloc_bytes(&bytes);

    let bytes = iter::repeat_n(18u8, 2048).collect::<Vec<_>>();
    arena.alloc_bytes(&bytes);

    let chunks = unsafe { &mut *arena.core.chunks.get() };
    assert_eq!(chunks.len(), 2);
    assert_eq!(chunks[0].capacity(), Capacity::new(4096));
    assert_eq!(chunks[1].capacity(), Capacity::new(8192));
}

#[test]
fn dropless_weird_size() {
    type Foo = (u128, u16);
    debug_println!("layout for Foo {:?}", Layout::new::<Foo>());

    let arena = DroplessArena::new();
    let values = iter::repeat_n::<Foo>((14, 12), 128).collect::<Vec<_>>();
    arena.alloc_from_slice(&values);
    eprintln!("Successfully allocated once");

    let values = iter::repeat_n::<Foo>((22, 38), 200).collect::<Vec<_>>();
    arena.alloc_from_slice(&values);
    eprintln!("Successfully allocated twice");
}

#[test]
fn dropless_mixed_types() {
    let arena = DroplessArena::new();

    let alloced = arena.alloc_from_slice::<u32>(&[14, 197, 34871, 1349, 1034]);
    assert!(alloced.as_ptr().is_aligned());

    let alloced = arena.alloc_from_slice::<u64>(&[11, 150, 1051345, 883, 171]);
    assert!(alloced.as_ptr().is_aligned());

    let alloced = arena.alloc(());
    assert!((alloced as *const ()).is_aligned());

    let alloced = arena.alloc((12, 13, 14));
    assert!((alloced as *const (i32, i32, i32)).is_aligned());
}

#[test]
fn typed_drop_glue() {
    static DROP_COUNT: AtomicUsize = AtomicUsize::new(0);

    #[derive(Clone)]
    struct Foo(#[allow(dead_code)] u32);
    impl Drop for Foo {
        fn drop(&mut self) {
            DROP_COUNT.fetch_add(1, Ordering::Release);
        }
    }

    let arena = TypedArena::new();
    arena.alloc_from_iter(iter::repeat_n(Foo(0), 16));
    drop(arena);
    assert_eq!(DROP_COUNT.load(Ordering::Acquire), 16);
}

#[test]
fn typed_drop_glue_zst() {
    static DROP_COUNT: AtomicUsize = AtomicUsize::new(0);

    // It is deeply weird to make a ZST with drop glue, much less to arena allocate it, but hey
    #[derive(Debug, Clone, PartialEq, Eq)]
    struct Foo;
    impl Drop for Foo {
        fn drop(&mut self) {
            DROP_COUNT.fetch_add(1, Ordering::Release);
        }
    }

    let arena = TypedArena::new();
    arena.alloc_from_iter(iter::repeat_n(Foo, 18));
    drop(arena);
    assert_eq!(DROP_COUNT.load(Ordering::Acquire), 18);
}

#[test]
fn typed_multiple_chunks() {
    let arena = TypedArena::new();
    let alloced = arena.alloc_from_iter(iter::repeat_n(187_u128, 200));
    assert!(alloced.as_ptr().is_aligned());
    let alloced = arena.alloc_from_iter(iter::repeat_n(300_u128, 128));
    assert!(alloced.as_ptr().is_aligned());
}

#[test]
fn typed_multiple_chunks_drop_glue() {
    static DROP_COUNT: AtomicUsize = AtomicUsize::new(0);

    #[derive(Clone)]
    struct Foo(#[allow(dead_code)] u128);
    impl Drop for Foo {
        fn drop(&mut self) {
            DROP_COUNT.fetch_add(1, Ordering::Release);
        }
    }

    let arena = TypedArena::new();
    arena.alloc_from_iter(iter::repeat_n(Foo(187), 200));
    arena.alloc_from_iter(iter::repeat_n(Foo(300), 128));
    drop(arena);

    assert_eq!(DROP_COUNT.load(Ordering::Acquire), 328);
}

impl<T> ArenaCore<T> {
    fn report_status(&mut self) {
        unsafe {
            eprintln!("== Arena status ==");
            eprintln!("{} chunks:", (*self.chunks.get()).len());
            for chunk in &*self.chunks.get() {
                eprintln!(
                    "- {:?} {:?}, {} occupied",
                    chunk.capacity(),
                    chunk.capacity().byte_size(),
                    chunk.occupied,
                );
            }
            let pointers = self.pointers.get_mut().unwrap();
            let start = *pointers.start.get_mut();
            eprintln!(
                "Current range pointers: {:p} .. {:p} ({:?})",
                start,
                pointers.end,
                pointers.end.sub_ptr_capacity(start),
            );
            if let Some(last) = (*self.chunks.get()).last_mut() {
                let last_chunk_storage = last.get_storage_ptr();
                let last_chunk_occupied = start.sub_ptr_capacity(last_chunk_storage);
                eprintln!("Last chunk occupied {last_chunk_occupied:?}");
            }
        }
    }
}

#[test]
fn threaded_dropless() {
    let mut arena = DroplessArena::new();
    thread::scope(|scope| {
        // Some ints...
        scope.spawn(|| {
            for _ in 0..500000 {
                arena.alloc_from_slice(&[14, 15, 16, 17, 18]);
            }
        });

        // Some bytes...
        scope.spawn(|| {
            for _ in 0..500000 {
                arena.alloc_bytes(b"just gonna repeat this over and over");
            }
        });

        // Some strings...
        scope.spawn(|| {
            for _ in 0..500000 {
                arena.alloc_str("and hey why not also this");
            }
        });
    });
    arena.core.report_status();
}

#[test]
fn threaded_typed_drop_glue() {
    static DROP_COUNT: AtomicUsize = AtomicUsize::new(0);

    #[derive(Clone)]
    struct Foo(#[allow(dead_code)] usize);
    impl Drop for Foo {
        fn drop(&mut self) {
            DROP_COUNT.fetch_add(1, Ordering::Relaxed);
        }
    }

    const NUM_SLICES_PER_THREAD: usize = 15_000;
    const SLICE_SIZE: usize = 17;
    const NUM_THREADS: usize = 10;

    let mut arena = TypedArena::new();
    thread::scope(|scope| {
        for _ in 0..NUM_THREADS {
            scope.spawn(|| {
                for i in 0..NUM_SLICES_PER_THREAD {
                    arena.alloc_from_iter(iter::repeat_n(Foo(i), SLICE_SIZE));
                }
            });
        }
    });
    arena.core.report_status();
    drop(arena);
    assert_eq!(
        DROP_COUNT.load(Ordering::Acquire),
        NUM_SLICES_PER_THREAD * SLICE_SIZE * NUM_THREADS,
    );
}
