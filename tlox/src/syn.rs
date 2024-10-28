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

    /// A variable declaration.
    Decl {
        name: Spanned<Symbol<'s>>,
        init: Option<Spanned<Expr<'s>>>,
    },

    /// A block statement.
    Block { stmts: Vec<Spanned<Stmt<'s>>> },

    /// An if-else statement.
    IfElse {
        cond: Spanned<Expr<'s>>,
        body: Box<Spanned<Stmt<'s>>>,
        else_body: Option<Box<Spanned<Stmt<'s>>>>,
    },
}

impl Stmt<'_> {
    fn display_indented_level(&self, level: usize, omit_first: bool) -> impl Display + use<'_> {
        struct DisplayIndented<'s> {
            node: &'s Stmt<'s>,
            level: usize,
            omit_first: bool,
        }
        impl Display for DisplayIndented<'_> {
            fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
                let indent = self.level * 4;
                let first = if self.omit_first { 0 } else { indent };

                match self.node {
                    Stmt::Expr { val } => write!(f, "{:first$}{};", "", val.node),
                    Stmt::Print { val } => write!(f, "{:first$}print {};", "", val.node),
                    Stmt::Decl { name, init } => {
                        write!(f, "{:first$}var {}", "", name.node)?;
                        if let Some(init) = init {
                            write!(f, " = {}", init.node)?;
                        }
                        write!(f, ";")
                    }
                    Stmt::Block { stmts } => {
                        writeln!(f, "{:first$}{{", "")?;
                        for stmt in stmts {
                            writeln!(
                                f,
                                "{}",
                                stmt.node.display_indented_level(self.level + 1, false)
                            )?;
                        }
                        write!(f, "{:indent$}}}", "")
                    }
                    Stmt::IfElse {
                        cond,
                        body,
                        else_body,
                    } => {
                        write!(
                            f,
                            "{:first$}if ({}) {}",
                            "",
                            cond.node,
                            body.node.display_indented_level(self.level, true),
                        )?;
                        if let Some(else_body) = else_body {
                            write!(
                                f,
                                "\nelse {}",
                                else_body.node.display_indented_level(self.level, true),
                            )?;
                        }
                        Ok(())
                    }
                }
            }
        }

        DisplayIndented {
            node: self,
            level,
            omit_first,
        }
    }

    fn display_indented(&self) -> impl Display + use<'_> {
        self.display_indented_level(0, false)
    }
}

impl Display for Stmt<'_> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(&self.display_indented(), f)
    }
}

pub mod stmt {
    use super::*;

    pub fn expr(val: Spanned<Expr>) -> Stmt {
        Stmt::Expr { val }
    }

    pub fn print(val: Spanned<Expr>) -> Stmt {
        Stmt::Print { val }
    }

    pub fn decl<'s>(
        name: Spanned<Symbol<'s>>,
        init: impl Into<Option<Spanned<Expr<'s>>>>,
    ) -> Stmt<'s> {
        Stmt::Decl {
            name,
            init: init.into(),
        }
    }

    pub fn block(stmts: Vec<Spanned<Stmt>>) -> Stmt {
        Stmt::Block { stmts }
    }

    pub fn if_else<'s>(
        cond: Spanned<Expr<'s>>,
        body: Spanned<Stmt<'s>>,
        else_body: Option<Spanned<Stmt<'s>>>,
    ) -> Stmt<'s> {
        Stmt::IfElse {
            cond,
            body: Box::new(body),
            else_body: else_body.map(Box::new),
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

impl BinopSym {
    pub fn binding(self) -> BindingLevel {
        match self {
            BinopSym::Eq | BinopSym::Ne => BindingLevel::Eq,
            BinopSym::Gt | BinopSym::Ge | BinopSym::Lt | BinopSym::Le => BindingLevel::Comp,
            BinopSym::Sub | BinopSym::Add => BindingLevel::Add,
            BinopSym::Div | BinopSym::Mul | BinopSym::Mod => BindingLevel::Mul,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum BindingLevel {
    Assign,
    Eq,
    Comp,
    Add,
    Mul,
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

/// A place expression.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Place<'s> {
    /// A variable place.
    Var(Symbol<'s>),
}

impl Display for Place<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Place::Var(name) => write!(f, "{name}"),
        }
    }
}

/// An expression.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ExprNode<'s> {
    /// A literal expression.
    Literal(Lit<'s>),

    /// A variable reference.
    Var(Symbol<'s>),

    /// A parenthesized expression.
    Group(Spanned<Expr<'s>>),

    /// A unary operator expression.
    Unop {
        /// Operator symbol.
        sym: Spanned<UnopSym>,

        /// Operand.
        operand: Spanned<Expr<'s>>,
    },

    /// A binary operator expression.
    Binop {
        /// Operator symbol.
        sym: Spanned<BinopSym>,

        /// Left operand.
        lhs: Spanned<Expr<'s>>,

        /// Right operand.
        rhs: Spanned<Expr<'s>>,
    },

    /// A variable assignment expression.
    Assign {
        /// The place assigned to.
        place: Spanned<Place<'s>>,

        /// The value assigned.
        val: Spanned<Expr<'s>>,
    },
}

pub type Expr<'s> = Box<ExprNode<'s>>;

pub mod expr {
    use super::*;

    /// Create a literal expression.
    pub fn literal(value: Lit) -> Expr {
        Box::new(ExprNode::Literal(value))
    }

    /// Create a variable reference expression.
    pub fn var(name: Symbol) -> Expr {
        Box::new(ExprNode::Var(name))
    }

    /// Create a grouped expression.
    pub fn group(inner: Spanned<Expr>) -> Expr {
        Box::new(ExprNode::Group(inner))
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

    /// Create a variable assignment expression.
    pub fn assign<'s>(place: Spanned<Place<'s>>, val: Spanned<Expr<'s>>) -> Spanned<Expr<'s>> {
        let span = place.span.join(val.span);
        Box::new(ExprNode::Assign { place, val }).spanned(span)
    }
}

impl<'s> ExprNode<'s> {
    /// Is this expression a place expression?
    pub fn is_place(&self) -> bool {
        matches!(self, ExprNode::Var(_))
    }

    /// Convert `self` into a place expression, if possible.
    pub fn into_place(self) -> Result<Place<'s>, Self> {
        match self {
            ExprNode::Var(name) => Ok(Place::Var(name)),
            _ => Err(self),
        }
    }
}

impl ExprNode<'_> {
    fn subexpr_needs_group(&self) -> bool {
        matches!(self, ExprNode::Binop { .. })
    }

    fn opd_needs_group(&self, level: BindingLevel) -> bool {
        matches!(self, ExprNode::Binop { sym, .. } if sym.node.binding() < level)
    }
}

impl Display for ExprNode<'_> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            ExprNode::Literal(lit) => write!(f, "{lit}"),
            ExprNode::Var(name) => write!(f, "{name}"),
            ExprNode::Group(expr) => write!(f, "({})", expr.node),
            ExprNode::Unop { sym, operand } => {
                write!(f, "{}", sym.node)?;
                if operand.node.subexpr_needs_group() {
                    write!(f, "({})", operand.node)
                } else {
                    write!(f, "{}", operand.node)
                }
            }
            ExprNode::Binop { sym, lhs, rhs } => {
                let level = sym.node.binding();
                if lhs.node.subexpr_needs_group() {
                    write!(f, "({})", lhs.node)?;
                } else {
                    write!(f, "{}", lhs.node)?;
                }

                write!(f, " {} ", sym.node)?;

                if rhs.node.opd_needs_group(level) {
                    write!(f, "({})", rhs.node)
                } else {
                    write!(f, "{}", rhs.node)
                }
            }
            ExprNode::Assign { place, val } => write!(f, "{} = {}", place.node, val.node),
        }
    }
}
