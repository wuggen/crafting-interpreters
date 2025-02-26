//! Abstract syntax tree.

use std::fmt::{self, Debug, Display, Formatter};
use std::hash::{Hash, Hasher};

use crate::span::{HasSpan, Span, Spannable, Spanned};
use crate::symbol::Symbol;

pub trait SynEq<T: ?Sized = Self> {
    fn syn_eq(&self, other: &T) -> bool;
}

impl<T: SynEq> SynEq for Spanned<T> {
    fn syn_eq(&self, other: &Self) -> bool {
        self.node.syn_eq(&other.node)
    }
}

impl<T: SynEq> SynEq for Box<T> {
    fn syn_eq(&self, other: &Self) -> bool {
        (**self).syn_eq(&**other)
    }
}

impl<T: SynEq> SynEq for &T {
    fn syn_eq(&self, other: &Self) -> bool {
        T::syn_eq(self, other)
    }
}

impl<T: SynEq> SynEq for Vec<T> {
    fn syn_eq(&self, other: &Self) -> bool {
        self.as_slice().syn_eq(other.as_slice())
    }
}

impl<T: SynEq> SynEq for Option<T> {
    fn syn_eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Some(a), Some(b)) => a.syn_eq(b),
            (None, None) => true,
            _ => false,
        }
    }
}

impl<T: SynEq> SynEq for [T] {
    fn syn_eq(&self, other: &Self) -> bool {
        self.len() == other.len() && self.iter().zip(other.iter()).all(|(a, b)| a.syn_eq(b))
    }
}

impl SynEq for Symbol<'_> {
    fn syn_eq(&self, other: &Self) -> bool {
        self == other
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Fun<'s> {
    pub name: Spanned<Symbol<'s>>,
    pub args: Vec<Spanned<Symbol<'s>>>,
    pub body: Vec<Spanned<Stmt<'s>>>,
}

impl SynEq for Fun<'_> {
    fn syn_eq(&self, other: &Self) -> bool {
        self.name.syn_eq(&other.name)
            && self.args.syn_eq(&other.args)
            && self.body.syn_eq(&other.body)
    }
}

/// A Lox statement.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Stmt<'s> {
    /// An expression statement.
    Expr { val: Spanned<Expr<'s>> },

    /// A print statement.
    Print { val: Spanned<Expr<'s>> },

    /// A variable declaration.
    VarDecl {
        name: Spanned<Symbol<'s>>,
        init: Option<Spanned<Expr<'s>>>,
    },

    /// A block statement.
    Block { stmts: Vec<Spanned<Stmt<'s>>> },

    /// An if-else statement.
    IfElse {
        cond: Spanned<Expr<'s>>,
        body: Spanned<Box<Stmt<'s>>>,
        else_body: Option<Spanned<Box<Stmt<'s>>>>,
    },

    /// A while loop.
    While {
        cond: Spanned<Expr<'s>>,
        body: Spanned<Box<Stmt<'s>>>,
    },

    /// A for loop.
    ///
    /// For loops are internally desugared into while loops. This node is retained explicitly for
    /// pretty-printing purposes.
    For {
        init: Option<Spanned<Box<Stmt<'s>>>>,
        cond: Option<Spanned<Expr<'s>>>,
        update: Option<Spanned<Expr<'s>>>,
        body: Spanned<Box<Stmt<'s>>>,
    },

    /// A function declaration.
    FunDecl { def: Fun<'s> },

    /// A class declaration.
    ClassDecl {
        name: Spanned<Symbol<'s>>,
        superclass: Option<Spanned<Symbol<'s>>>,
        methods: Vec<Spanned<Fun<'s>>>,
    },

    /// A return statement.
    Return { val: Option<Spanned<Expr<'s>>> },

    /// A break statement.
    Break,
}

impl SynEq for Stmt<'_> {
    fn syn_eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Stmt::Expr { val: v1 }, Stmt::Expr { val: v2 }) => v1.syn_eq(v2),
            (Stmt::Print { val: v1 }, Stmt::Print { val: v2 }) => v1.syn_eq(v2),

            (Stmt::VarDecl { name: n1, init: i1 }, Stmt::VarDecl { name: n2, init: i2 }) => {
                n1.syn_eq(n2) && i1.syn_eq(i2)
            }

            (Stmt::Block { stmts: s1 }, Stmt::Block { stmts: s2 }) => s1.syn_eq(s2),

            (
                Stmt::IfElse {
                    cond: c1,
                    body: b1,
                    else_body: eb1,
                },
                Stmt::IfElse {
                    cond: c2,
                    body: b2,
                    else_body: eb2,
                },
            ) => c1.syn_eq(c2) && b1.syn_eq(b2) && eb1.syn_eq(eb2),

            (Stmt::While { cond: c1, body: b1 }, Stmt::While { cond: c2, body: b2 }) => {
                c1.syn_eq(c2) && b1.syn_eq(b2)
            }

            (
                Stmt::For {
                    init: i1,
                    cond: c1,
                    update: u1,
                    body: b1,
                },
                Stmt::For {
                    init: i2,
                    cond: c2,
                    update: u2,
                    body: b2,
                },
            ) => i1.syn_eq(i2) && c1.syn_eq(c2) && u1.syn_eq(u2) && b1.syn_eq(b2),

            (Stmt::FunDecl { def: d1 }, Stmt::FunDecl { def: d2 }) => d1.syn_eq(d2),

            (
                Stmt::ClassDecl {
                    name: n1,
                    superclass: s1,
                    methods: m1,
                },
                Stmt::ClassDecl {
                    name: n2,
                    superclass: s2,
                    methods: m2,
                },
            ) => n1.syn_eq(n2) && s1.syn_eq(s2) && m1.syn_eq(m2),

            (Stmt::Return { val: v1 }, Stmt::Return { val: v2 }) => v1.syn_eq(v2),

            (Stmt::Break, Stmt::Break) => true,

            _ => false,
        }
    }
}

impl Fun<'_> {
    fn display_indented_level(&self, level: usize, omit_first: bool) -> impl Display + use<'_> {
        struct DisplayIndented<'s> {
            node: &'s Fun<'s>,
            level: usize,
            omit_first: bool,
        }
        impl Display for DisplayIndented<'_> {
            fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
                let indent = self.level * 4;
                let first = if self.omit_first { 0 } else { indent };

                write!(f, "{:first$}{}(", "", self.node.name.node)?;
                for (i, arg) in self.node.args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", arg.node)?;
                }
                writeln!(f, ") {{")?;
                for stmt in &self.node.body {
                    writeln!(
                        f,
                        "{}",
                        stmt.node.display_indented_level(self.level + 1, false)
                    )?;
                }
                write!(f, "{:indent$}}}", "")
            }
        }
        DisplayIndented {
            node: self,
            level,
            omit_first,
        }
    }
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
                    Stmt::VarDecl { name, init } => {
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
                    Stmt::While { cond, body } => {
                        write!(
                            f,
                            "{:first$}while ({}) {}",
                            "",
                            cond.node,
                            body.node.display_indented_level(self.level, true),
                        )
                    }
                    Stmt::For {
                        init,
                        cond,
                        update,
                        body,
                    } => {
                        write!(f, "{:first$}for (", "")?;
                        if let Some(init) = init {
                            write!(f, "{init}")?;
                        } else {
                            write!(f, ";")?;
                        }
                        if let Some(cond) = cond {
                            write!(f, " {cond}")?;
                        }
                        write!(f, ";")?;
                        if let Some(update) = update {
                            write!(f, " {update}")?;
                        }
                        write!(
                            f,
                            ") {}",
                            body.node.display_indented_level(self.level, true)
                        )
                    }
                    Stmt::FunDecl { def } => {
                        write!(
                            f,
                            "{:first$}fun {}",
                            "",
                            def.display_indented_level(self.level, true)
                        )
                    }
                    Stmt::ClassDecl {
                        name,
                        superclass,
                        methods,
                    } => {
                        // writeln!(f, "{:first$}class {} {{", "", name.node)?;
                        write!(f, "{:first$}class {}", "", name.node)?;
                        if let Some(superclass) = superclass {
                            write!(f, " < {}", superclass.node)?;
                        }
                        writeln!(f, " {{")?;

                        for method in methods {
                            writeln!(
                                f,
                                "{}",
                                method.node.display_indented_level(self.level + 1, false)
                            )?;
                        }
                        write!(f, "{:indent$}}}", "")
                    }
                    Stmt::Return { val } => {
                        write!(f, "{:first$}return", "")?;
                        if let Some(val) = val {
                            write!(f, " {}", val.node)?;
                        }
                        write!(f, ";")
                    }
                    Stmt::Break => write!(f, "{:first$}break;", ""),
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
        Stmt::VarDecl {
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
            body: body.boxed(),
            else_body: else_body.map(Spanned::boxed),
        }
    }

    pub fn while_loop<'s>(cond: Spanned<Expr<'s>>, body: Spanned<Stmt<'s>>) -> Stmt<'s> {
        Stmt::While {
            cond,
            body: body.boxed(),
        }
    }

    pub fn for_loop<'s>(
        init: Option<Spanned<Stmt<'s>>>,
        cond: Option<Spanned<Expr<'s>>>,
        update: Option<Spanned<Expr<'s>>>,
        body: Spanned<Stmt<'s>>,
    ) -> Stmt<'s> {
        let init = init.map(|stmt| stmt.boxed());
        let body = body.boxed();
        Stmt::For {
            init,
            cond,
            update,
            body,
        }
    }

    pub fn fun_decl<'s>(
        name: Spanned<Symbol<'s>>,
        args: Vec<Spanned<Symbol<'s>>>,
        body: Vec<Spanned<Stmt<'s>>>,
    ) -> Stmt<'s> {
        Stmt::FunDecl {
            def: Fun { name, args, body },
        }
    }

    pub fn fun_return<'s>(val: impl Into<Option<Spanned<Expr<'s>>>>) -> Stmt<'s> {
        Stmt::Return { val: val.into() }
    }

    pub fn loop_break<'s>() -> Stmt<'s> {
        Stmt::Break
    }
}

/// A Lox program.
///
/// Syntactically, a Lox program is simply a list of statements.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Program<'s> {
    pub stmts: Vec<Spanned<Stmt<'s>>>,
}

impl SynEq for Program<'_> {
    fn syn_eq(&self, other: &Self) -> bool {
        self.stmts.syn_eq(&other.stmts)
    }
}

impl Display for Program<'_> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        for stmt in &self.stmts {
            writeln!(f, "{}", stmt.node)?;
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

impl SynEq for UnopSym {
    fn syn_eq(&self, other: &Self) -> bool {
        self == other
    }
}

impl Display for UnopSym {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            UnopSym::Not => write!(f, "!"),
            UnopSym::Neg => write!(f, "-"),
        }
    }
}

/// Boolean binary operator symbols.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BooleanBinopSym {
    /// Boolean `or`
    Or,

    /// Boolean `and`
    And,
}

/// Binary operator symbols.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinopSym {
    /// Boolean binary operators
    Bool(BooleanBinopSym),

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

impl SynEq for BinopSym {
    fn syn_eq(&self, other: &Self) -> bool {
        self == other
    }
}

impl Display for BinopSym {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let s = match self {
            BinopSym::Bool(BooleanBinopSym::Or) => "or",
            BinopSym::Bool(BooleanBinopSym::And) => "and",
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
            BinopSym::Bool(BooleanBinopSym::Or) => BindingLevel::LogicOr,
            BinopSym::Bool(BooleanBinopSym::And) => BindingLevel::LogicAnd,
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
    LogicOr,
    LogicAnd,
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

impl SynEq for Lit<'_> {
    fn syn_eq(&self, other: &Self) -> bool {
        self == other
    }
}

/// A place expression.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Place<'s> {
    /// Variable or property name
    pub name: Spanned<Symbol<'s>>,

    /// Optional receiver expression
    pub receiver: Option<Spanned<Expr<'s>>>,
}

impl HasSpan for Place<'_> {
    fn span(&self) -> Span {
        if let Some(receiver) = &self.receiver {
            receiver.span.join(self.name.span)
        } else {
            self.name.span
        }
    }
}

impl SynEq for Place<'_> {
    fn syn_eq(&self, other: &Self) -> bool {
        self.name.syn_eq(&other.name) && self.receiver.syn_eq(&other.receiver)
    }
}

impl Display for Place<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if let Some(receiver) = &self.receiver {
            write!(f, "{}.", receiver.node)?;
        }

        write!(f, "{}", self.name.node)
    }
}

impl<'s> Place<'s> {
    pub fn from_expr(expr: Spanned<Expr<'s>>) -> Result<Self, Spanned<Expr<'s>>> {
        match *expr.node {
            ExprNode::Var(name) => Ok(Place {
                name: name.spanned(expr.span),
                receiver: None,
            }),
            ExprNode::Access { receiver, name } => Ok(Place {
                receiver: Some(receiver),
                name,
            }),
            _ => Err(expr),
        }
    }
}

/// An expression.
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum ExprNode<'s> {
    /// A literal expression.
    Literal(Lit<'s>),

    /// A variable reference.
    Var(Symbol<'s>),

    /// A reference to the bound instance in a method.
    This,

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
        place: Place<'s>,

        /// The value assigned.
        val: Spanned<Expr<'s>>,
    },

    /// A function call expression.
    Call {
        /// The callee.
        callee: Spanned<Expr<'s>>,

        /// The arguments list.
        args: Spanned<Vec<Spanned<Expr<'s>>>>,
    },

    /// A property access ("get") expression
    Access {
        /// The receiving object
        receiver: Spanned<Expr<'s>>,

        /// The property name
        name: Spanned<Symbol<'s>>,
    },

    /// A superclass method access
    Super {
        /// The span of the `super` keyword
        kw: Span,

        /// The accessed method
        name: Spanned<Symbol<'s>>,
    },
}

impl Debug for ExprNode<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            ExprNode::Literal(lit) => Debug::fmt(lit, f),
            ExprNode::Var(symbol) => f.debug_tuple("Var").field(&symbol).finish(),
            ExprNode::This => write!(f, "This"),
            ExprNode::Group(expr) => f.debug_tuple("Group").field(&expr).finish(),
            ExprNode::Unop { sym, operand } => {
                f.debug_tuple(&format!("{sym:?}")).field(&operand).finish()
            }
            ExprNode::Binop { sym, lhs, rhs } => f
                .debug_tuple(&format!("{sym:?}"))
                .field(&lhs)
                .field(&rhs)
                .finish(),
            ExprNode::Assign { place, val } => {
                f.debug_tuple("Assign").field(&place).field(&val).finish()
            }
            ExprNode::Call { callee, args } => {
                f.debug_tuple("Call").field(&callee).field(&args).finish()
            }
            ExprNode::Access { receiver, name } => f
                .debug_tuple("Access")
                .field(&receiver)
                .field(&name)
                .finish(),
            ExprNode::Super { name, .. } => f.debug_tuple("Super").field(&name).finish(),
        }
    }
}

impl SynEq for ExprNode<'_> {
    fn syn_eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Literal(a), Self::Literal(b)) => a.syn_eq(b),
            (Self::Var(a), Self::Var(b)) => a.syn_eq(b),
            (Self::This, Self::This) => true,
            (Self::Group(a), Self::Group(b)) => a.syn_eq(b),
            (
                Self::Unop {
                    sym: s1,
                    operand: o1,
                },
                Self::Unop {
                    sym: s2,
                    operand: o2,
                },
            ) => s1.syn_eq(s2) && o1.syn_eq(o2),
            (
                Self::Binop {
                    sym: s1,
                    lhs: l1,
                    rhs: r1,
                },
                Self::Binop {
                    sym: s2,
                    lhs: l2,
                    rhs: r2,
                },
            ) => s1.syn_eq(s2) && l1.syn_eq(l2) && r1.syn_eq(r2),
            (Self::Assign { place: p1, val: v1 }, Self::Assign { place: p2, val: v2 }) => {
                p1.syn_eq(p2) && v1.syn_eq(v2)
            }
            (
                Self::Call {
                    callee: c1,
                    args: a1,
                },
                Self::Call {
                    callee: c2,
                    args: a2,
                },
            ) => c1.syn_eq(c2) && a1.syn_eq(a2),
            (
                Self::Access {
                    receiver: r1,
                    name: n1,
                },
                Self::Access {
                    receiver: r2,
                    name: n2,
                },
            ) => r1.syn_eq(r2) && n1.syn_eq(n2),
            (Self::Super { name: n1, .. }, Self::Super { name: n2, .. }) => n1.syn_eq(n2),
            _ => false,
        }
    }
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

    /// Create a `this` expression.
    pub fn this() -> Expr<'static> {
        Box::new(ExprNode::This)
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
    pub fn assign<'s>(place: Place<'s>, val: Spanned<Expr<'s>>) -> Spanned<Expr<'s>> {
        let span = place.span().join(val.span);
        Box::new(ExprNode::Assign { place, val }).spanned(span)
    }

    /// Create a function call expression.
    pub fn call<'s>(
        callee: Spanned<Expr<'s>>,
        args: Spanned<Vec<Spanned<Expr<'s>>>>,
    ) -> Spanned<Expr<'s>> {
        let span = callee.span.join(args.span);
        Box::new(ExprNode::Call { callee, args }).spanned(span)
    }

    pub fn access<'s>(receiver: Spanned<Expr<'s>>, name: Spanned<Symbol<'s>>) -> Spanned<Expr<'s>> {
        let span = receiver.span.join(name.span);
        Box::new(ExprNode::Access { receiver, name }).spanned(span)
    }

    pub fn super_access(kw: Span, name: Spanned<Symbol<'_>>) -> Spanned<Expr<'_>> {
        let span = kw.join(name.span);
        Box::new(ExprNode::Super { kw, name }).spanned(span)
    }
}

impl ExprNode<'_> {
    /// Is this expression a place expression?
    pub fn is_place(&self) -> bool {
        matches!(self, ExprNode::Var(_))
    }
}

impl ExprNode<'_> {
    fn subexpr_needs_group(&self) -> bool {
        matches!(self, ExprNode::Binop { .. })
    }

    fn lhs_needs_group(&self, level: BindingLevel) -> bool {
        matches!(self, ExprNode::Binop { sym, .. } if sym.node.binding() < level)
    }

    fn rhs_needs_group(&self, level: BindingLevel) -> bool {
        matches!(self, ExprNode::Binop { sym, .. } if sym.node.binding() <= level)
    }
}

impl Display for ExprNode<'_> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            ExprNode::Literal(lit) => write!(f, "{lit}"),
            ExprNode::Var(name) => write!(f, "{name}"),
            ExprNode::This => write!(f, "this"),
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
                if lhs.node.lhs_needs_group(level) {
                    write!(f, "({})", lhs.node)?;
                } else {
                    write!(f, "{}", lhs.node)?;
                }

                write!(f, " {} ", sym.node)?;

                if rhs.node.rhs_needs_group(level) {
                    write!(f, "({})", rhs.node)
                } else {
                    write!(f, "{}", rhs)
                }
            }
            ExprNode::Assign { place, val } => write!(f, "{} = {}", place, val.node),
            ExprNode::Call { callee, args } => {
                write!(f, "{}(", callee.node)?;
                let mut tail = false;
                for arg in &args.node {
                    if tail {
                        write!(f, ", {}", arg.node)?;
                    } else {
                        write!(f, "{}", arg.node)?;
                        tail = true;
                    }
                }
                write!(f, ")")
            }
            ExprNode::Access { receiver, name } => write!(f, "{}.{}", receiver.node, name.node),
            ExprNode::Super { name, .. } => write!(f, "super.{}", name.node),
        }
    }
}
