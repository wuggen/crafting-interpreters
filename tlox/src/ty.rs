//! Runtime Lox value types.

use std::fmt::{self, Display, Formatter};

/// A Lox primitive type.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PrimitiveTy {
    Nil,
    Num,
    Bool,
    Str,
}

impl Display for PrimitiveTy {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            PrimitiveTy::Nil => write!(f, "Nil"),
            PrimitiveTy::Num => write!(f, "Num"),
            PrimitiveTy::Bool => write!(f, "Bool"),
            PrimitiveTy::Str => write!(f, "Str"),
        }
    }
}

/// A Lox runtime type.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Ty {
    Primitive(PrimitiveTy),
}

impl Display for Ty {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Ty::Primitive(ty) => Display::fmt(ty, f),
        }
    }
}
