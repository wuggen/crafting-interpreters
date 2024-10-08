//! Assorted utility functions.

use std::fmt::{self, Display, Formatter};

/// Wrapper struct that `Display`s as a prose list, with the given conjunction and appropriate
/// Oxford comma placement.
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
    use std::fmt::{self, Display, Formatter};

    use crate::intern::Interned;
    use crate::parse::parse_source;
    use crate::span::{SourceMap, Spanned};
    use crate::syn::Expr;

    pub fn parse_new_source(source: &str) -> Option<Spanned<Interned<Expr>>> {
        let source_idx = SourceMap::with_current(|sm| sm.add_source(0, source));
        parse_source(source_idx)
    }

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
