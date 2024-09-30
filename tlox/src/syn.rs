//! Abstract syntax tree.

use std::any::TypeId;
use std::fmt::{self, Display, Formatter};
use std::hash::{Hash, Hasher};

use crate::intern::Interned;
use crate::span::{Spannable, Spanned};
use crate::Internable;

/// Unary operator symbols.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnopSym {
    /// Boolean negation, `!`
    Not,

    /// Numerical negation, `-`
    Neg,
}

impl Display for UnopSym {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            UnopSym::Not => write!(f, "!"),
            UnopSym::Neg => write!(f, "-"),
        }
    }
}

/// Binary operator symbols.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinopSym {
    /// Equality comparison, `==`
    Eq,

    /// Inequality comparison, `!=`
    Ne,

    /// Greater-than comparison, `>`
    Gt,

    /// Greater-or-equal comparison, `>=`
    Ge,

    /// Less-than comparison, `<`
    Lt,

    /// Less-or-equal comparison, `<=`
    Le,

    /// Subtraction, `-`
    Sub,

    /// Addition, `+`
    Add,

    /// Division, `/`
    Div,

    /// Multiplication, `*`
    Mul,

    /// Modulo, `%`
    Mod,
}

impl Display for BinopSym {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let s = match self {
            BinopSym::Eq => "==",
            BinopSym::Ne => "!=",
            BinopSym::Gt => ">",
            BinopSym::Ge => ">=",
            BinopSym::Lt => "<",
            BinopSym::Le => "<=",
            BinopSym::Sub => "-",
            BinopSym::Add => "+",
            BinopSym::Div => "/",
            BinopSym::Mul => "*",
            BinopSym::Mod => "%",
        };
        write!(f, "{s}")
    }
}

/// A literal value.
#[derive(Debug, Clone, Copy)]
pub enum Lit {
    /// Literal nil
    Nil,

    /// Number literal
    Num(f64),

    /// Boolean literal
    Bool(bool),

    /// String literal
    Str(Interned<str>),
}

impl Display for Lit {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Lit::Nil => write!(f, "nil"),
            Lit::Num(n) => write!(f, "{n}"),
            Lit::Bool(b) => write!(f, "{b}"),
            Lit::Str(s) => write!(f, "{s:?}"),
        }
    }
}

impl Hash for Lit {
    fn hash<H: Hasher>(&self, state: &mut H) {
        TypeId::of::<Self>().hash(state);
        std::mem::discriminant(self).hash(state);
        match self {
            Lit::Nil => {}
            Lit::Num(n) => n.to_bits().hash(state),
            Lit::Bool(b) => b.hash(state),
            Lit::Str(s) => s.hash(state),
        }
    }
}

impl PartialEq for Lit {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Lit::Nil, Lit::Nil) => true,
            (Lit::Num(a), Lit::Num(b)) => a.total_cmp(b).is_eq(),
            (Lit::Bool(a), Lit::Bool(b)) => a == b,
            (Lit::Str(a), Lit::Str(b)) => a == b,
            _ => false,
        }
    }
}

impl Eq for Lit {}

/// An expression.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Expr {
    /// A literal expression
    Literal(Lit),

    /// A unary operator expression
    Unop {
        /// Operator symbol
        sym: Spanned<UnopSym>,

        /// Operand
        operand: Spanned<Interned<Expr>>,
    },

    /// A binary operator expression
    Binop {
        /// Operator symbol
        sym: Spanned<BinopSym>,

        /// Left operand
        lhs: Spanned<Interned<Expr>>,

        /// Right operand
        rhs: Spanned<Interned<Expr>>,
    },
}

impl Expr {
    pub fn literal(value: Lit) -> Interned<Self> {
        Self::Literal(value).interned()
    }

    pub fn unop(
        sym: Spanned<UnopSym>,
        operand: Spanned<Interned<Expr>>,
    ) -> Spanned<Interned<Self>> {
        let span = sym.span.join(operand.span);
        Self::Unop { sym, operand }.interned().spanned(span)
    }

    pub fn binop(
        sym: Spanned<BinopSym>,
        lhs: Spanned<Interned<Expr>>,
        rhs: Spanned<Interned<Expr>>,
    ) -> Spanned<Interned<Self>> {
        let span = lhs.span.join(rhs.span);
        Self::Binop { sym, lhs, rhs }.interned().spanned(span)
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Literal(lit) => write!(f, "{lit}"),
            Expr::Unop { sym, operand } => write!(f, "({} {})", sym.node, operand.node),
            Expr::Binop { sym, lhs, rhs } => write!(f, "({} {} {})", sym.node, lhs.node, rhs.node),
        }
    }
}
