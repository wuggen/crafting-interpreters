//! Variable resolution.

use std::collections::HashMap;

use crate::diag::{Diag, DiagKind, Diagnostic};
use crate::span::{Span, Spanned};
use crate::symbol::Symbol;
use crate::syn::{Expr, ExprNode, Place, Stmt};

#[derive(Debug, Clone, Default)]
pub struct ResolutionTable<'s> {
    references: HashMap<Spanned<Symbol<'s>>, usize>,
}

impl<'s> ResolutionTable<'s> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn resolve(&mut self, stmts: &[Spanned<Stmt<'s>>]) {
        let mut resolver = Resolver {
            table: self,
            env: ResolverEnv::new(),
        };

        resolver.resolve_stmts(stmts);
    }

    pub fn lookup(&self, var: Spanned<Symbol<'s>>) -> Option<usize> {
        self.references.get(&var).copied()
    }
}

struct Resolver<'s, 'i> {
    table: &'i mut ResolutionTable<'s>,
    env: ResolverEnv<'s>,
}

impl<'s> Resolver<'s, '_> {
    fn resolve_stmts(&mut self, stmts: &[Spanned<Stmt<'s>>]) {
        for stmt in stmts {
            self.resolve_stmt(stmt.as_ref());
        }
    }

    fn resolve_stmt(&mut self, stmt: Spanned<&Stmt<'s>>) {
        match &stmt.node {
            Stmt::Expr { val } | Stmt::Print { val } => self.resolve_expr(val.as_ref()),

            Stmt::IfElse {
                cond,
                body,
                else_body,
            } => {
                self.resolve_expr(cond.as_ref());
                self.resolve_stmt(body.as_deref());
                if let Some(stmt) = else_body.as_ref() {
                    self.resolve_stmt(stmt.as_deref());
                }
            }
            Stmt::While { cond, body } => {
                self.resolve_expr(cond.as_ref());
                self.resolve_stmt(body.as_deref());
            }
            Stmt::For { desugared, .. } => self.resolve_stmt(stmt.with_node(desugared)),
            Stmt::Return { val } => {
                if let Some(val) = val.as_ref() {
                    self.resolve_expr(val.as_ref());
                }
            }
            Stmt::Break => {}

            Stmt::Block { stmts } => {
                self.env.push_scope();
                self.resolve_stmts(stmts);
                self.env.pop_scope();
            }
            Stmt::FunDecl { name, args, body } => {
                self.env.declare_and_define(*name);

                self.env.push_scope();
                for arg in args {
                    self.env.declare_and_define(*arg);
                }
                self.resolve_stmts(body);
                self.env.pop_scope();
            }
            Stmt::Decl { name, init } => {
                self.env.declare(*name);
                if let Some(expr) = init.as_ref() {
                    self.resolve_expr(expr.as_ref());
                }
                self.env.define(name.node);
            }
        }
    }

    fn resolve_expr(&mut self, expr: Spanned<&Expr<'s>>) {
        match &**expr.node {
            ExprNode::Literal(_) => {}
            ExprNode::Group(expr) => self.resolve_expr(expr.as_ref()),
            ExprNode::Unop { operand, .. } => self.resolve_expr(operand.as_ref()),
            ExprNode::Binop { lhs, rhs, .. } => {
                self.resolve_expr(lhs.as_ref());
                self.resolve_expr(rhs.as_ref());
            }
            ExprNode::Assign { place, val } => {
                self.resolve_place(place.as_ref());
                self.resolve_expr(val.as_ref());
            }
            ExprNode::Call { callee, args } => {
                self.resolve_expr(callee.as_ref());
                for expr in &args.node {
                    self.resolve_expr(expr.as_ref());
                }
            }

            ExprNode::Var(name) => self.resolve_name(expr.with_node(*name)),
        }
    }

    fn resolve_place(&mut self, place: Spanned<&Place<'s>>) {
        match place.node {
            Place::Var(name) => self.resolve_name(place.with_node(*name)),
        }
    }

    fn resolve_name(&mut self, name: Spanned<Symbol<'s>>) {
        if let Some(res) = self.env.resolve(name) {
            self.table.references.insert(name, res);
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum VarStatus {
    Declared,
    Defined,
}

#[derive(Default)]
struct ResolverEnv<'s> {
    scopes: Vec<HashMap<Symbol<'s>, (Span, VarStatus)>>,
}

impl<'s> ResolverEnv<'s> {
    fn new() -> Self {
        Self::default()
    }

    fn declare(&mut self, name: Spanned<Symbol<'s>>) {
        self.scopes
            .last_mut()
            .map(|scope| scope.insert(name.node, (name.span, VarStatus::Declared)));
    }

    fn define(&mut self, name: Symbol<'s>) {
        self.scopes
            .last_mut()
            .map(|scope| scope.get_mut(&name).unwrap().1 = VarStatus::Defined);
    }

    fn declare_and_define(&mut self, name: Spanned<Symbol<'s>>) {
        self.scopes
            .last_mut()
            .map(|scope| scope.insert(name.node, (name.span, VarStatus::Defined)));
    }

    fn push_scope(&mut self) {
        self.scopes.push(HashMap::new());
    }

    fn pop_scope(&mut self) {
        self.scopes.pop();
    }

    fn resolve(&mut self, name: Spanned<Symbol<'s>>) -> Option<usize> {
        self.scopes
            .iter()
            .rev()
            .enumerate()
            .filter_map(|(i, scope)| {
                let (decl, status) = scope.get(&name.node)?;
                if *status == VarStatus::Declared {
                    ResolverDiag::RecursiveVarDecl {
                        name: name.node,
                        decl: *decl,
                        reference: name.span,
                    }
                    .emit();
                }
                Some(i)
            })
            .next()
    }
}

pub enum ResolverDiag<'s> {
    RecursiveVarDecl {
        name: Symbol<'s>,
        decl: Span,
        reference: Span,
    },
}

impl Diagnostic for ResolverDiag<'_> {
    fn into_diag(self) -> Diag {
        match self {
            ResolverDiag::RecursiveVarDecl {
                name,
                decl,
                reference,
            } => Diag::new(
                DiagKind::Error,
                format!("recursive definition of variable `{name}`"),
            )
            .with_primary(
                reference,
                format!("`{name}` referenced recursively in its own definition"),
            )
            .with_secondary(decl, format!("declaration of `{name}` here"))
            .with_note("variable initializers cannot reference the variable being defined"),
        }
    }
}
