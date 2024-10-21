//! Abstract syntax tree.

use std::fmt::{self, Display, Formatter};
use std::hash::{Hash, Hasher};

use crate::span::{Spannable, Spanned};
use crate::symbol::Symbol;

/// A Lox statement.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Stmt<'s> {
    /// An expression statement.
    Expr { val: Spanned<Expr<'s>> },

    /// A print statement.
    Print { val: Spanned<Expr<'s>> },
}

impl Display for Stmt<'_> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Self::Expr { val } => write!(f, "{};", val.node),
            Self::Print { val } => write!(f, "print {};", val.node),
        }
    }
}

/// A Lox program.
///
/// Syntactically, a Lox program is simply a list of statements.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Program<'s> {
    pub stmts: Vec<Spanned<Stmt<'s>>>,
}

impl Display for Program<'_> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        for stmt in &self.stmts {
            writeln!(f, "{stmt}")?;
        }
        Ok(())
    }
}

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
pub enum Lit<'s> {
    /// Literal nil
    Nil,

    /// Number literal
    Num(f64),

    /// Boolean literal
    Bool(bool),

    /// String literal
    Str(Symbol<'s>),
}

impl Display for Lit<'_> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Lit::Nil => write!(f, "nil"),
            Lit::Num(n) => write!(f, "{n}"),
            Lit::Bool(b) => write!(f, "{b}"),
            Lit::Str(s) => write!(f, "{:?}", s.as_str()),
        }
    }
}

impl Hash for Lit<'_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        "Lit".hash(state);
        std::mem::discriminant(self).hash(state);
        match self {
            Lit::Nil => {}
            Lit::Num(n) => n.to_bits().hash(state),
            Lit::Bool(b) => b.hash(state),
            Lit::Str(s) => s.hash(state),
        }
    }
}

impl PartialEq for Lit<'_> {
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

impl Eq for Lit<'_> {}

/// An expression.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ExprNode<'s> {
    /// A literal expression
    Literal(Lit<'s>),

    /// A unary operator expression
    Unop {
        /// Operator symbol
        sym: Spanned<UnopSym>,

        /// Operand
        operand: Spanned<Expr<'s>>,
    },

    /// A binary operator expression
    Binop {
        /// Operator symbol
        sym: Spanned<BinopSym>,

        /// Left operand
        lhs: Spanned<Expr<'s>>,

        /// Right operand
        rhs: Spanned<Expr<'s>>,
    },
}

pub type Expr<'s> = Box<ExprNode<'s>>;

pub mod expr {
    use super::*;

    /// Create a literal expression.
    pub fn literal(value: Lit) -> Expr {
        Box::new(ExprNode::Literal(value))
    }

    /// Create a unary operator expression.
    pub fn unop(sym: Spanned<UnopSym>, operand: Spanned<Expr>) -> Spanned<Expr> {
        let span = sym.span.join(operand.span);
        Box::new(ExprNode::Unop { sym, operand }).spanned(span)
    }

    /// Create a binary operator expression.
    pub fn binop<'s>(
        sym: Spanned<BinopSym>,
        lhs: Spanned<Expr<'s>>,
        rhs: Spanned<Expr<'s>>,
    ) -> Spanned<Expr<'s>> {
        let span = lhs.span.join(rhs.span);
        Box::new(ExprNode::Binop { sym, lhs, rhs }).spanned(span)
    }
}

impl Display for ExprNode<'_> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            ExprNode::Literal(lit) => write!(f, "{lit}"),
            ExprNode::Unop { sym, operand } => write!(f, "({} {})", sym.node, operand.node),
            ExprNode::Binop { sym, lhs, rhs } => {
                write!(f, "({} {} {})", lhs.node, sym.node, rhs.node)
            }
        }
    }
}
