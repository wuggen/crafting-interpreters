//! Scoped thread-local storage.

use std::cell::Cell;
use std::marker::PhantomData;
use std::thread::LocalKey;

/// A thread-local storage key that allows storing non-`'static` data in a scoped way.
pub struct ScopedKey<T> {
    #[doc(hidden)]
    pub inner: &'static LocalKey<Cell<*const ()>>,
    #[doc(hidden)]
    pub _marker: PhantomData<T>,
}

/// Create a scoped thread-local key.
///
/// The key is initially unset; it must be set using [`ScopedKey::set`], and will be reset when the
/// closure given to that method returns.
#[macro_export]
macro_rules! scoped_thread_local {
    ($(#[$attr:meta])* $vis:vis static $NAME:ident: $Ty:ty) => {
        $(#[$attr])*
        $vis static $NAME: $crate::util::scoped::ScopedKey<$Ty> = $crate::util::scoped::ScopedKey {
            _marker: ::std::marker::PhantomData,
            inner: {
                ::std::thread_local!{
                    static FOO: ::std::cell::Cell<*const ()>
                        = ::std::cell::Cell::new(::std::ptr::null())
                }
                &FOO
            },
        };
    };

    ($($tt:tt)* ;) => { ::$crate::scoped_thread_local!($($tt)*) }
}

impl<T> ScopedKey<T> {
    /// Set the value stored in the key for the current thread.
    ///
    /// The value will be reset to its previous value when the given closure returns.
    pub fn set<R>(&'static self, value: &T, f: impl FnOnce() -> R) -> R {
        struct Reset {
            key: &'static LocalKey<Cell<*const ()>>,
            prev: *const (),
        }
        impl Drop for Reset {
            fn drop(&mut self) {
                self.key.set(self.prev);
            }
        }
        let _reset = Reset {
            key: self.inner,
            prev: self.inner.replace(value as *const _ as *const ()),
        };
        f()
    }

    /// Access the current value of the key for the current thread.
    ///
    /// Panics if the key is currently unset in this thread.
    pub fn with<R>(&'static self, f: impl FnOnce(&T) -> R) -> R {
        let val = self.inner.get();
        assert!(!val.is_null(), "scoped key has not been set");
        unsafe { f(&*(val as *const T)) }
    }

    /// Is the key currently set in this thread?
    pub fn is_set(&'static self) -> bool {
        !self.inner.get().is_null()
    }
}
