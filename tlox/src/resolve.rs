//! Variable resolution.

use std::collections::{HashMap, HashSet};

use crate::span::Spanned;
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
                self.env.declare(name.node);

                self.env.push_scope();
                for arg in args {
                    self.env.declare(arg.node);
                }
                self.resolve_stmts(body);
                self.env.pop_scope();
            }
            Stmt::Decl { name, init } => {
                if let Some(expr) = init.as_ref() {
                    self.resolve_expr(expr.as_ref());
                }
                self.env.declare(name.node);
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
        if let Some(res) = self.env.resolve(name.node) {
            self.table.references.insert(name, res);
        }
    }
}

#[derive(Default)]
struct ResolverEnv<'s> {
    scopes: Vec<HashSet<Symbol<'s>>>,
}

impl<'s> ResolverEnv<'s> {
    fn new() -> Self {
        Self::default()
    }

    fn declare(&mut self, name: Symbol<'s>) {
        self.scopes
            .last_mut()
            .map(|scope| scope.insert(name));
    }

    fn push_scope(&mut self) {
        self.scopes.push(HashSet::new());
    }

    fn pop_scope(&mut self) {
        self.scopes.pop();
    }

    fn resolve(&mut self, name: Symbol<'s>) -> Option<usize> {
        self.scopes
            .iter()
            .rev()
            .enumerate()
            .filter_map(|(i, scope)| {
                if scope.contains(&name) {
                    Some(i)
                } else {
                    None
                }
            })
            .next()
    }
}
