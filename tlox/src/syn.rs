//! Abstract syntax tree.

use std::fmt::{self, Display, Formatter};

use crate::intern::Interned;
use crate::span::{Spannable, Spanned};

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
#[derive(Debug, Clone, Copy, PartialEq)]
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

/// An expression.
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    /// A literal expression
    Literal(Lit),

    /// A unary operator expression
    Unop {
        /// Operator symbol
        sym: Spanned<UnopSym>,

        /// Operand
        operand: Box<Spanned<Expr>>,
    },

    /// A binary operator expression
    Binop {
        /// Operator symbol
        sym: Spanned<BinopSym>,

        /// Left operand
        lhs: Box<Spanned<Expr>>,

        /// Right operand
        rhs: Box<Spanned<Expr>>,
    },
}

impl Expr {
    pub fn literal(value: Lit) -> Self {
        Self::Literal(value)
    }

    pub fn unop(sym: Spanned<UnopSym>, operand: Spanned<Expr>) -> Spanned<Self> {
        let span = sym.span.join(operand.span);
        Self::Unop {
            sym,
            operand: Box::new(operand),
        }
        .spanned(span)
    }

    pub fn binop(sym: Spanned<BinopSym>, lhs: Spanned<Expr>, rhs: Spanned<Expr>) -> Spanned<Self> {
        let span = lhs.span.join(rhs.span);
        Self::Binop {
            sym,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        }
        .spanned(span)
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
