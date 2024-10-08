//! Runtime Lox values.

use std::fmt::{self, Display, Formatter};
use std::rc::Rc;

use crate::intern::Interned;
use crate::ty::{PrimitiveTy, Ty};

/// A runtime value.
#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Nil,
    Bool(bool),
    Num(f64),
    Str(StrValue),
}

impl Value {
    /// Get the type of this value.
    pub fn ty(&self) -> Ty {
        match self {
            Value::Nil => Ty::Primitive(PrimitiveTy::Nil),
            Value::Bool(_) => Ty::Primitive(PrimitiveTy::Bool),
            Value::Num(_) => Ty::Primitive(PrimitiveTy::Num),
            Value::Str(_) => Ty::Primitive(PrimitiveTy::Str),
        }
    }

    /// Is this value truthy?
    ///
    /// Nil and false are falsey; all other values are truthy.
    pub fn is_truthy(&self) -> bool {
        !matches!(self, Value::Nil | Value::Bool(false))
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Value::Nil => write!(f, "nil"),
            Value::Bool(b) => write!(f, "{b}"),
            Value::Num(n) => write!(f, "{n}"),
            Value::Str(s) => write!(f, "{s}"),
        }
    }
}

impl PartialEq<bool> for Value {
    fn eq(&self, other: &bool) -> bool {
        if let Value::Bool(b) = self {
            b == other
        } else {
            false
        }
    }
}

impl PartialEq<f64> for Value {
    fn eq(&self, other: &f64) -> bool {
        if let Value::Num(n) = self {
            n == other
        } else {
            false
        }
    }
}

impl PartialEq<&str> for Value {
    fn eq(&self, other: &&str) -> bool {
        if let Value::Str(s) = self {
            s.as_ref() == *other
        } else {
            false
        }
    }
}

/// A string value.
///
/// A string value can be either static or computed. Static strings are those that are defined
/// directly in the program text as literals, and are interned during lexical analysis. Computed
/// strings are constructed at runtime, are not interned, and are represented by reference-counted
/// Rust `String`s.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StrValue {
    Static(Interned<str>),
    Computed(Rc<String>),
}

impl AsRef<str> for StrValue {
    fn as_ref(&self) -> &str {
        match self {
            StrValue::Static(s) => s,
            StrValue::Computed(s) => s,
        }
    }
}

impl Display for StrValue {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", <Self as AsRef<str>>::as_ref(self))
    }
}

impl StrValue {
    /// Concatenate two string values.
    ///
    /// String values in Lox are immutable; concatenation produces a new string value whose
    /// contents are the concatenation of the two operands.
    pub fn concat(&self, other: &Self) -> Self {
        StrValue::Computed(Rc::new(
            [self.as_ref(), other.as_ref()]
                .into_iter()
                .collect::<String>(),
        ))
    }
}
