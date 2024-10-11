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

#[cfg(test)]
pub mod test {
    //! Testing utilities.
    use std::fmt::{self, Display, Formatter};

    use crate::parse::parse_source;
    use crate::session::Session;
    use crate::span::Spanned;
    use crate::syn::Expr;

    /// Add a new source to the current session and parse it.
    pub fn parse_new_source(source: &str) -> Option<Spanned<Expr>> {
        Session::with_current(|sess| {
            let source_idx = sess.sm.add_source(0, source);
            parse_source(source_idx)
        })
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
