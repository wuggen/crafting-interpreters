//! Variable resolution.

use std::collections::HashMap;

use crate::diag::{Diag, Diagnostic};
use crate::span::{Span, Spannable, Spanned};
use crate::symbol::Symbol;
use crate::symbol::static_syms::{SYM_SUPER, SYM_THIS};
use crate::syn::{Expr, ExprNode, Fun, Place, Stmt};

#[derive(Debug, Clone, Default)]
pub struct ResolutionTable<'s> {
    // Map from variable references to pairs of (a) the index of the scope in
    // which the referenced variable is declared and (b) the span of that
    // declaration.
    references: HashMap<Spanned<Symbol<'s>>, (usize, Span)>,
}

impl<'s> ResolutionTable<'s> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn resolve(&mut self, stmts: &[Spanned<Stmt<'s>>]) {
        let mut resolver = Resolver {
            table: self,
            enclosing_classes: 0,
            env: ResolverEnv::new(),
        };

        resolver.resolve_stmts(stmts);
    }

    /// Look up the variable declaration referred to by a variable use.
    ///
    /// `var` is the spanned variable reference. If the referenced variable is
    /// global, returns `None`. Otherwise, returns a pair of:
    ///
    /// - The index of the enclosing scope in which the referenced variable is declared, and;
    /// - The spanned variable declaration.
    pub fn lookup(&self, var: Spanned<Symbol<'s>>) -> Option<(usize, Spanned<Symbol<'s>>)> {
        self.references
            .get(&var)
            .copied()
            .map(|(i, sp)| (i, var.with_span(sp)))
    }
}

struct Resolver<'s, 'i> {
    table: &'i mut ResolutionTable<'s>,
    enclosing_classes: u32,
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

                let _guard = self.env.push_scope();

                self.resolve_stmt(body.as_deref());
                if let Some(stmt) = else_body.as_ref() {
                    self.resolve_stmt(stmt.as_deref());
                }
            }
            Stmt::While { cond, body } => {
                let _guard = self.env.push_scope();
                self.resolve_expr(cond.as_ref());
                self.resolve_stmt(body.as_deref());
            }
            Stmt::For {
                init,
                cond,
                update,
                body,
            } => {
                let _guard = self.env.push_scope();

                if let Some(init) = init {
                    self.resolve_stmt(init.as_deref());
                }
                if let Some(cond) = cond {
                    self.resolve_expr(cond.as_ref());
                }
                self.resolve_stmt(body.as_deref());
                if let Some(update) = update {
                    self.resolve_expr(update.as_ref());
                }
            }
            Stmt::Return { val } => {
                if let Some(val) = val.as_ref() {
                    self.resolve_expr(val.as_ref());
                }
            }
            Stmt::Break => {}
            Stmt::Block { stmts } => {
                let _guard = self.env.push_scope();
                self.resolve_stmts(stmts);
            }
            Stmt::FunDecl {
                def: Fun { name, args, body },
            } => {
                self.env.declare(*name);

                let _guard = self.env.push_scope();
                for arg in args {
                    self.env.declare(*arg);
                }
                self.resolve_stmts(body);
            }
            Stmt::ClassDecl {
                name,
                superclass,
                methods,
            } => {
                if let Some(superclass) = superclass {
                    if superclass.node == name.node {
                        Diag::new(
                            crate::diag::DiagKind::Error,
                            format!("class `{name}` cannot inherit from itself"),
                        )
                        .with_primary(superclass.span, "attempt to derive a class from itself")
                        .emit();
                    }

                    self.resolve_name(*superclass);
                }

                self.enclosing_classes += 1;

                self.env.declare(*name);

                let _super_guard = superclass.as_ref().map(|_| {
                    let guard = self.env.push_scope();
                    self.env.declare(SYM_SUPER.spanned(Span::empty()));
                    guard
                });

                let _guard = self.env.push_scope();
                self.env.declare(SYM_THIS.spanned(Span::empty()));

                for method in methods {
                    let _guard = self.env.push_scope();
                    for arg in &method.node.args {
                        self.env.declare(*arg);
                    }
                    self.resolve_stmts(&method.node.body);
                }

                self.enclosing_classes -= 1;
            }
            Stmt::VarDecl { name, init } => {
                if let Some(expr) = init.as_ref() {
                    self.resolve_expr(expr.as_ref());
                }
                self.env.declare(*name);
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
                self.resolve_place(place);
                self.resolve_expr(val.as_ref());
            }
            ExprNode::Call { callee, args } => {
                self.resolve_expr(callee.as_ref());
                for expr in &args.node {
                    self.resolve_expr(expr.as_ref());
                }
            }
            ExprNode::Access { receiver, .. } => {
                self.resolve_expr(receiver.as_ref());
            }

            ExprNode::Var(name) => self.resolve_name(expr.with_node(*name)),
            ExprNode::This => self.resolve_name(expr.with_node(SYM_THIS)),
            ExprNode::Super { kw, .. } => {
                self.resolve_name(SYM_SUPER.spanned(*kw));
                self.resolve_name(SYM_THIS.spanned(*kw));
            }
        }
    }

    fn resolve_place(&mut self, place: &Place<'s>) {
        if let Some(receiver) = &place.receiver {
            self.resolve_expr(receiver.as_ref());
        } else {
            self.resolve_name(place.name);
        }
    }

    fn resolve_name(&mut self, name: Spanned<Symbol<'s>>) {
        if let Some(res) = self.env.resolve(name.node) {
            if name.node == SYM_THIS {
                debug_println!(@"resolved `this` at {:?} to {res:?}", name.span);
            }
            self.table.references.insert(name, res);
        }
    }
}

#[derive(Default)]
struct ResolverEnv<'s> {
    // Maps from variable names to the spans at which they were declared
    scopes: Vec<HashMap<Symbol<'s>, Span>>,
}

struct ScopeGuard<'s> {
    env: *mut ResolverEnv<'s>,
}

impl Drop for ScopeGuard<'_> {
    fn drop(&mut self) {
        unsafe {
            (*self.env)
                .scopes
                .pop()
                .expect("cannot pop the global scope");
        }
    }
}

impl<'s> ResolverEnv<'s> {
    fn new() -> Self {
        Self::default()
    }

    fn declare(&mut self, name: Spanned<Symbol<'s>>) {
        self.scopes
            .last_mut()
            .map(|scope| scope.insert(name.node, name.span));
    }

    fn push_scope(&mut self) -> ScopeGuard<'s> {
        self.scopes.push(HashMap::new());
        ScopeGuard { env: self }
    }

    fn resolve(&mut self, name: Symbol<'s>) -> Option<(usize, Span)> {
        self.scopes
            .iter()
            .rev()
            .enumerate()
            .filter_map(|(i, scope)| scope.get(&name).map(|span| (i, *span)))
            .next()
    }
}
