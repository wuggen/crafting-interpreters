//! Interned data.

use std::collections::HashMap;
use std::fmt::{self, Debug, Display, Formatter};
use std::hash::Hash;
use std::ops::Deref;
use std::ptr;
use std::sync::Mutex;

/// A `T` that is known to be unique.
///
/// Because interned data is known to be unique, it can be checked for equality cheaply simply by
/// pointer comparison, and can be freely copied even if the underlying type doesn't implement
/// `Copy`.
///
/// Instances of this struct should only be constructed from references to data that is known to be
/// unique; the easiest way to accomplish this is via the `interned()` method of the `Internable`
/// trait defined by the [`mk_internable`](crate::mk_internable) macro. It is possible and safe to
/// construct an `Interned` with a reference to non-unique data, but this will cause incorrect
/// behavior.
#[derive(PartialOrd, Ord)]
#[repr(transparent)]
pub struct Interned<T: ?Sized + 'static>(pub &'static T);

impl<T: Debug + ?Sized + 'static> Debug for Interned<T> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Debug::fmt(self.0, f)
    }
}

impl<T: Display + ?Sized + 'static> Display for Interned<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(self.0, f)
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

/// A table of interned values.
///
/// Normally this should not be manually constructed. The [`mk_internable`] macro establishes
/// static intern tables for a given set of types.
#[doc(hidden)]
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
    /// Intern a value in this table.
    ///
    /// If a value equal to the given item has already been interned in this table, returns a
    /// reference to that item.
    ///
    /// # Safety
    ///
    /// This table must live for the `'static` lifetime in order for the returned reference to be
    /// valid.
    pub unsafe fn intern(&self, item: T) -> Interned<T> {
        let mut items = self.items.lock().unwrap();
        let (interned, _) = items
            .raw_entry_mut()
            .from_key(&item)
            .or_insert_with(|| (Box::new(item), ()));

        Interned(&*(interned.as_ref() as *const _))
    }
}

impl InternedTable<[u8]> {
    /// Intern a byte slice.
    ///
    /// If a byte slice equal to the given one has already been interned in this table, returns a
    /// reference to that slice.
    ///
    /// The [`mk_internable`] macro uses a single table of byte slices for both `&[u8]` and `&str`
    /// data.
    ///
    /// # Safety
    ///
    /// This table must live for the `'static` lifetime in order for the returned reference to be
    /// valid.
    pub unsafe fn intern_bytes(&self, bytes: &[u8]) -> Interned<[u8]> {
        let mut items = self.items.lock().unwrap();
        let (interned, _) = items
            .raw_entry_mut()
            .from_key(bytes)
            .or_insert_with(|| (Vec::from(bytes).into_boxed_slice(), ()));

        Interned(&*(interned.as_ref() as *const _))
    }
}

/// Construct intern tables for a given set of types.
///
/// This macro establishes interning support in the calling scope for:
/// - Byte slices (`&[u8]`);
/// - String slices (`&str`);
/// - Other specified types `T`, which must be [`Sized`], [`Eq`], [`Hash`], and `'static`.
///
/// It accomplishes this by defining static intern tables for each of these types, along with a
/// trait similar to the following:
///
/// ```no_run
/// # use std::borrow::Borrow;
/// # use tlox::intern::Interned;
/// pub trait Internable: Sized + Borrow<Self::Interned> {
///     type Interned: ?Sized;
///     fn interned(self) -> Interned<Self::Interned>;
/// }
/// ```
///
/// This trait is implemented for `&[u8]` (`type Interned = [u8]`), `&str` (`type Interned = str`),
/// and each of the types named in the macro invocation (`type Interned = Self`). The `interned()`
/// method interns the value in the static table defined for the implementing type.
///
/// Note that `&[u8]` and `&str` will share the same table; interned values of either type that are
/// bytewise identical will refer to the same interned byte slice.
///
/// # Example
///
/// ```
/// # use tlox::mk_internable;
/// // Syntax:
/// //
/// //     mk_internable! {
/// //         name1: Type1,
/// //         name2: Type2,
/// //         ...
/// //     }
/// //
/// // Names are arbitrary and are only used internally by the macro to establish the intern
/// // tables for the associated types. The only restriction is that the names assigned to each
/// // internable type must be distinct from each other.
/// mk_internable! {
///     int: i32,
///     heap_string: String,
/// }
///
/// let string1 = "hello world!".interned();
/// let string2 = "hello world!".interned();
///
/// // Equality comparison between interned values is just pointer equality:
/// assert_eq!(string1, string2);
/// assert_eq!(string1.0 as *const _, string2.0 as *const _);
///
/// // Interned values implement `Debug` and `Display` whenever their underlying types do:
/// assert_eq!(format!("{string1}"), "hello world!");
///
/// // They also inherit their underlying types' `PartialOrd` and `Ord` implementations:
/// let int1 = 42_i32.interned();
/// let int2 = 120_i32.interned();
/// assert!(int1 < int2);
///
/// // They also implement `Deref`:
/// assert_eq!(string1.chars().count(), 12);
/// assert_eq!(&*string1, "hello world!");
///
/// // Interned values are `Copy` even if their underlying types are not:
/// let heap_string = String::from("foobar").interned();
/// let heap_string_copy = heap_string;
/// assert_eq!(heap_string, heap_string_copy);
/// ```
#[macro_export]
macro_rules! mk_internable {
    ($($name:ident: $ty:ty),*) => {
        /// Types that can be interned.
        pub trait Internable: ::std::marker::Sized + ::std::borrow::Borrow<Self::Interned> {
            type Interned: ?::std::marker::Sized;
            fn interned(self) -> $crate::intern::Interned<Self::Interned>;
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
            fn interned(self) -> $crate::intern::Interned<Self::Interned> {
                unsafe { INTERNED_TABLES.__default_bytes_table.intern_bytes(self) }
            }
        }

        impl Internable for &str {
            type Interned = str;
            fn interned(self) -> $crate::intern::Interned<Self::Interned> {
                use $crate::intern::Interned;
                let interned_bytes = self.as_bytes().interned();
                unsafe { Interned(std::str::from_utf8_unchecked(interned_bytes.0)) }
            }
        }

        $(
            impl Internable for $ty {
                type Interned = Self;
                fn interned(self) -> $crate::intern::Interned<Self::Interned> {
                    unsafe { INTERNED_TABLES.$name.intern(self) }
                }
            }
        )*
    };

    ($($name:ident: $ty:ty),* ,) => {
        $crate::mk_internable!($($name: $ty),*);
    }
}

#[cfg(test)]
mod test {
    use std::ptr;

    #[test]
    fn string_interning() {
        mk_internable!();

        let s1 = "hey there".interned();
        let s2 = String::from("hey there").interned();
        let s3 = "lmao".interned();

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

        mk_internable!(noncopy: NonCopy);

        let nc1 = NonCopy(4).interned();
        let nc2 = NonCopy(4).interned();
        let nc3 = NonCopy(7).interned();

        let nc4 = nc1;

        assert_eq!(nc1, nc2);
        assert_eq!(nc2, nc4);
        assert_ne!(nc2, nc3);

        assert!(ptr::eq(nc1.0, nc2.0));
        assert!(!ptr::eq(nc4.0, nc3.0));
    }
}
