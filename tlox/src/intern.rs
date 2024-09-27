//! Interned data.

use std::collections::HashMap;
use std::fmt::{self, Debug, Formatter};
use std::hash::Hash;
use std::ops::Deref;
use std::ptr;
use std::sync::Mutex;

#[derive(PartialOrd, Ord)]
#[repr(transparent)]
pub struct Interned<T: ?Sized + 'static>(pub &'static T);

impl<T: Debug + ?Sized + 'static> Debug for Interned<T> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Debug::fmt(self.0, f)
    }
}

impl<T: ?Sized + 'static> Clone for Interned<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: ?Sized + 'static> Copy for Interned<T> {}

impl<T: ?Sized + 'static> PartialEq for Interned<T> {
    fn eq(&self, other: &Self) -> bool {
        ptr::eq(self.0, other.0)
    }
}

impl<T: ?Sized + 'static> Eq for Interned<T> {}

impl<T: ?Sized + 'static> Hash for Interned<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        ptr::hash(self.0, state);
    }
}

impl<T: ?Sized + 'static> Deref for Interned<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.0
    }
}

impl<T: ?Sized + 'static> AsRef<T> for Interned<T> {
    fn as_ref(&self) -> &T {
        self.0
    }
}

pub struct InternedTable<T: ?Sized> {
    items: Mutex<HashMap<Box<T>, ()>>,
}

impl<T: ?Sized> Default for InternedTable<T> {
    fn default() -> Self {
        Self {
            items: Mutex::new(HashMap::new()),
        }
    }
}

impl<T: Eq + Hash> InternedTable<T> {
    pub fn intern(&self, item: T) -> Interned<T> {
        let mut items = self.items.lock().unwrap();
        let (interned, _) = items
            .raw_entry_mut()
            .from_key(&item)
            .or_insert_with(|| (Box::new(item), ()));

        unsafe { Interned(&*(interned.as_ref() as *const _)) }
    }
}

impl InternedTable<[u8]> {
    pub fn intern_bytes(&self, bytes: &[u8]) -> Interned<[u8]> {
        let mut items = self.items.lock().unwrap();
        let (interned, _) = items
            .raw_entry_mut()
            .from_key(bytes)
            .or_insert_with(|| (Vec::from(bytes).into_boxed_slice(), ()));

        unsafe { Interned(&*(interned.as_ref() as *const _)) }
    }
}

#[macro_export]
macro_rules! mk_internable {
    ($($name:ident, $ty:ty);*) => {
        pub trait Internable: ::std::marker::Sized + ::std::borrow::Borrow<Self::Interned> {
            type Interned: ?::std::marker::Sized;
            fn intern(self) -> $crate::intern::Interned<Self::Interned>;
        }

        #[allow(non_snake_case)]
        #[derive(Default)]
        struct InternedTables {
            __default_bytes_table: $crate::intern::InternedTable<[u8]>,
            $(
                $name: $crate::intern::InternedTable<$ty>,
            )*
        }

        static INTERNED_TABLES: ::std::sync::LazyLock<InternedTables> = ::std::sync::LazyLock::new(Default::default);

        impl Internable for &[u8] {
            type Interned = [u8];
            fn intern(self) -> $crate::intern::Interned<Self::Interned> {
                INTERNED_TABLES.__default_bytes_table.intern_bytes(self)
            }
        }

        impl Internable for &str {
            type Interned = str;
            fn intern(self) -> $crate::intern::Interned<Self::Interned> {
                use $crate::intern::Interned;
                let interned_bytes = self.as_bytes().intern();
                unsafe { Interned(std::str::from_utf8_unchecked(interned_bytes.0)) }
            }
        }

        $(
            impl Internable for $ty {
                type Interned = Self;
                fn intern(self) -> $crate::intern::Interned<Self::Interned> {
                    INTERNED_TABLES.$name.intern(self)
                }
            }
        )*
    };

    ($($name:ident, $ty:ty);* ;) => {
        $crate::mk_internable!($($name, $ty);*);
    }
}

#[cfg(test)]
mod test {
    use std::ptr;

    #[test]
    fn string_interning() {
        mk_internable!();

        let s1 = "hey there".intern();
        let s2 = String::from("hey there").intern();
        let s3 = "lmao".intern();

        assert_eq!(s1, s2);
        assert_ne!(s1, s3);

        assert!(ptr::eq(s1.0, s2.0));
        assert!(!ptr::eq(s2.0, s3.0));

        assert_eq!(&*s1, &*s2);
        assert_ne!(&*s2, &*s3);
    }

    #[test]
    fn non_copy_interning() {
        #[derive(Debug, PartialEq, Eq, Hash)]
        struct NonCopy(u32);

        mk_internable!(noncopy, NonCopy);

        let nc1 = NonCopy(4).intern();
        let nc2 = NonCopy(4).intern();
        let nc3 = NonCopy(7).intern();

        let nc4 = nc1;

        assert_eq!(nc1, nc2);
        assert_eq!(nc2, nc4);
        assert_ne!(nc2, nc3);

        assert!(ptr::eq(nc1.0, nc2.0));
        assert!(!ptr::eq(nc4.0, nc3.0));
    }
}
