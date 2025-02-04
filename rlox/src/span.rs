//! Source code spans.

use std::fmt::{self, Display, Formatter};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Location {
    pub line: usize,
    pub col: usize,
}

impl Display for Location {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let val = format!("{}:{}", self.line + 1, self.col + 1);
        f.pad(&val)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct Span {
    offset: usize,
    len: usize,
}

impl Span {
    pub const fn offset(&self) -> usize {
        self.offset
    }

    pub const fn len(&self) -> usize {
        self.len
    }
}
