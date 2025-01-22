//! Assorted utility functions.

pub mod scoped;

use std::fmt::{self, Display, Formatter};

/// Wrapper struct that `Display`s as a prose list, with the given joiner (usually a conjunction)
/// and appropriate Oxford comma placement.
pub struct Oxford<'a, D> {
    pub list: &'a [D],
    pub join: &'static str,
}

impl<D: Display> Display for Oxford<'_, D> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self.list.len() {
            0 => Ok(()),
            1 => write!(f, "{}", self.list[0]),
            2 => write!(f, "{} {} {}", self.list[0], self.join, self.list[1]),
            n => {
                for item in &self.list[..n - 1] {
                    write!(f, "{item}, ")?;
                }
                write!(f, "{} {}", self.join, self.list.last().unwrap())
            }
        }
    }
}

/// Renders an Oxford comma list with "or".
pub fn oxford_or<D>(list: &[D]) -> Oxford<D> {
    Oxford { list, join: "or" }
}

/// Renders an Oxford comma list with "and".
pub fn oxford_and<D>(list: &[D]) -> Oxford<D> {
    Oxford { list, join: "and" }
}

/// Arbitrarily change the lifetime of a reference.
///
/// # Safety
///
/// The value must not be accessed outside of the `'a` lifetime.
#[inline(always)]
pub unsafe fn with_lifetime<'a, T: ?Sized>(val: &T) -> &'a T {
    unsafe { std::mem::transmute(val) }
}

#[cfg(test)]
pub mod test {
    //! Testing utilities.
    use std::fmt::{self, Display, Formatter};

    use crate::parse::parse_source;
    use crate::session::SessionKey;
    use crate::syn::Program;

    /// Add a new source to the current session and parse it.
    pub fn parse_new_source<'s>(key: SessionKey<'s>, source: &str) -> Option<Program<'s>> {
        let source_idx = key.get().sm.add_source(0, source);
        parse_source(key, source_idx)
    }

    /// A wrapper that adds a `Display` implementation to an `Option<T>` where `T: Display`.
    pub struct DisplayOption<'a, T>(pub &'a Option<T>);
    impl<T: Display> Display for DisplayOption<'_, T> {
        fn fmt(&self, f: &mut Formatter) -> fmt::Result {
            match self.0 {
                None => write!(f, "None"),
                Some(val) => <T as Display>::fmt(val, f),
            }
        }
    }
}
