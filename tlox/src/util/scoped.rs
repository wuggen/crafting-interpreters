use std::cell::Cell;
use std::marker::PhantomData;
use std::thread::LocalKey;

pub struct ScopedKey<T> {
    #[doc(hidden)]
    pub inner: &'static LocalKey<Cell<*const ()>>,
    #[doc(hidden)]
    pub _marker: PhantomData<T>,
}

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

    pub fn with<R>(&'static self, f: impl FnOnce(&T) -> R) -> R {
        let val = self.inner.get();
        assert!(!val.is_null(), "scoped key has not been set");
        unsafe { f(&*(val as *const T)) }
    }

    pub fn is_set(&'static self) -> bool {
        !self.inner.get().is_null()
    }
}
