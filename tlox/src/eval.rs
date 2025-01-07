//! Evaluation of Lox syntax trees.
use std::cell::{RefCell, RefMut};
use std::collections::HashMap;
use std::io::Write;
use std::ops::{Div, Mul, Rem, Sub};
use std::rc::Rc;

use crate::builtin::Builtin;
use crate::diag::Diagnostic;
use crate::error::{join_errs, CoercionCause, RuntimeError, RuntimeResult};
use crate::output::OutputStream;
use crate::resolve::ResolutionTable;
use crate::session::SessionKey;
use crate::span::{Span, Spannable, Spanned};
use crate::symbol::Symbol;
use crate::syn::{
    BinopSym, BooleanBinopSym, Expr, ExprNode, Fun, Lit, Place, Program, Stmt, UnopSym,
};
use crate::ty::{PrimitiveTy, Ty};
use crate::val::{ClassValue, FunValue, StrValue, UserFun, Value};

/// A tree-walking Lox interpreter.
pub struct Interpreter<'s, 'out> {
    key: SessionKey<'s>,
    env: Env<'s>,
    output: OutputStream<'out>,
    repl: bool,
}

impl<'s> Interpreter<'s, '_> {
    pub fn new(key: SessionKey<'s>) -> Interpreter<'s, 'static> {
        Interpreter {
            key,
            env: Env::default(),
            output: OutputStream::default(),
            repl: false,
        }
    }

    pub fn new_repl(key: SessionKey<'s>) -> Interpreter<'s, 'static> {
        Interpreter {
            key,
            env: Env::default(),
            output: OutputStream::default(),
            repl: true,
        }
    }

    pub fn with_output<'out>(self, output: OutputStream<'out>) -> Interpreter<'s, 'out> {
        Interpreter { output, ..self }
    }

    pub fn with_vec_output<'out>(self, output: &'out mut Vec<u8>) -> Interpreter<'s, 'out> {
        self.with_output(OutputStream::with(output))
    }

    pub fn key(&self) -> SessionKey<'s> {
        self.key
    }
}

impl<'s> Interpreter<'s, '_> {
    /// Evaluate a Lox program.
    pub fn eval(&mut self, program: &Program<'s>) {
        self.env.resolve(&program.stmts);

        if self.key.get().dcx.has_errors() {
            return;
        }

        let res = match self.eval_stmts(&program.stmts) {
            Ok(val) => val,
            Err(errs) => {
                for err in errs {
                    err.emit();
                }
                return;
            }
        };

        if self.repl && !matches!(res, Value::Nil) {
            writeln!(self.output, "{res}").unwrap();
        }
    }

    fn eval_stmts(&mut self, code: &[Spanned<Stmt<'s>>]) -> RuntimeResult<'s, Value<'s>> {
        let mut res = Value::Nil;
        for stmt in code {
            res = self.eval_stmt(stmt.as_ref())?;
        }
        Ok(res)
    }

    pub fn eval_with_env(
        &mut self,
        env: &mut Env<'s>,
        code: &[Spanned<Stmt<'s>>],
    ) -> RuntimeResult<'s, Value<'s>> {
        std::mem::swap(env, &mut self.env);
        let res = self.eval_stmts(code);
        std::mem::swap(env, &mut self.env);
        res
    }

    fn eval_stmt(&mut self, stmt: Spanned<&Stmt<'s>>) -> RuntimeResult<'s, Value<'s>> {
        let mut res = Value::Nil;

        match &stmt.node {
            Stmt::Expr { val } => {
                res = self.eval_expr(val)?;
            }

            Stmt::Print { val } => {
                let val = self.eval_expr(val)?;
                writeln!(self.output, "{val}").unwrap();
                res = Value::Nil;
            }

            Stmt::VarDecl { name, init } => {
                let init = if let Some(expr) = init {
                    self.eval_expr(expr)?
                } else {
                    Value::Nil
                };

                self.env.declare(*name, init.clone());
                res = init;
            }

            Stmt::Block { stmts } => {
                let _guard = self.env.push_scope();
                res = self.eval_stmts(stmts)?;
            }

            Stmt::IfElse {
                cond,
                body,
                else_body,
            } => {
                let cond = self.eval_expr(cond)?;

                let _guard = self.env.push_scope();

                if cond.is_truthy() {
                    res = self.eval_stmt(body.as_deref())?;
                } else if let Some(else_body) = else_body {
                    res = self.eval_stmt(else_body.as_deref())?;
                } else {
                    res = Value::Nil;
                }
            }

            Stmt::While { cond, body } => {
                let _guard = self.env.push_scope();

                while self.eval_expr(cond)?.is_truthy() {
                    match self.eval_stmt(body.as_deref()) {
                        Ok(val) => {
                            res = val;
                        }
                        Err(errs) => {
                            if let [RuntimeError::LoopBreak] = &errs[..] {
                                res = Value::Nil;
                                break;
                            } else {
                                return Err(errs);
                            }
                        }
                    };
                }
            }

            Stmt::For {
                init,
                cond,
                update,
                body,
            } => {
                let _guard = self.env.push_scope();

                if let Some(init) = init {
                    self.eval_stmt(init.as_deref())?;
                }

                loop {
                    if let Some(cond) = cond {
                        if !self.eval_expr(cond)?.is_truthy() {
                            break;
                        }
                    }

                    match self.eval_stmt(body.as_deref()) {
                        Ok(val) => {
                            res = val;
                        }

                        Err(errs) => {
                            if let [RuntimeError::LoopBreak] = &errs[..] {
                                res = Value::Nil;
                                break;
                            } else {
                                return Err(errs);
                            }
                        }
                    }

                    if let Some(update) = update {
                        self.eval_expr(update)?;
                    }
                }
            }

            Stmt::FunDecl {
                def: Fun { name, args, body },
            } => {
                let env = self.env.clone();
                let fun = Value::Fun(FunValue::User(Rc::new(UserFun::new(
                    name.node, args, body, env,
                ))));
                self.env.declare(*name, fun.clone());
                res = fun;
            }

            Stmt::ClassDecl { name, methods: _ } => {
                let class = Value::Class(ClassValue::new(name.node));
                self.env.declare(*name, class.clone());
                res = class;
            }

            Stmt::Return { val } => {
                let val = val
                    .as_ref()
                    .map(|val| self.eval_expr(val))
                    .unwrap_or(Ok(Value::Nil))?;
                return Err(vec![RuntimeError::fun_return(val)]);
            }

            Stmt::Break => {
                return Err(vec![RuntimeError::loop_break()]);
            }
        }

        Ok(res)
    }

    /// Evaluate an expression.
    fn eval_expr(&mut self, expr: &Spanned<Expr<'s>>) -> RuntimeResult<'s, Value<'s>> {
        match &*expr.node {
            ExprNode::Literal(lit) => Ok(lit.eval()),

            ExprNode::Var(name) => self
                .env
                .get(expr.with_node(*name))
                .ok_or_else(|| vec![RuntimeError::unbound_var_ref(expr.with_node(*name))]),

            ExprNode::Group(expr) => self.eval_expr(expr),

            ExprNode::Unop { sym, operand } => {
                let operand_val = self.eval_expr(operand)?;
                match sym.node {
                    UnopSym::Not => Ok(Value::Bool(!operand_val.is_truthy())),

                    UnopSym::Neg => {
                        let operand_val = self.coerce_to_num(
                            operand.with_node(operand_val),
                            CoercionCause::Unop { sym: *sym },
                        )?;
                        Ok(Value::Num(-operand_val))
                    }
                }
            }

            ExprNode::Binop { sym, lhs, rhs } => {
                if let BinopSym::Bool(bool_sym) = sym.node {
                    self.eval_boolean_binop(sym.with_node(bool_sym), lhs, rhs)
                } else {
                    let lop = self.eval_expr(lhs)?;
                    let rop = self.eval_expr(rhs)?;

                    self.eval_binop(*sym, lhs.with_node(lop), rhs.with_node(rop))
                }
            }

            ExprNode::Assign { place, val } => self.eval_assign(place, val),

            ExprNode::Call { callee, args } => {
                let callee_span = callee.span;
                let callee = self.eval_expr(callee)?;
                if let Some(callable) = callee.callable() {
                    if callable.arity() as usize != args.node.len() {
                        return Err(vec![RuntimeError::unexpected_arg_count(
                            callable.spanned(callee_span),
                            args,
                        )]);
                    }
                    let args = args
                        .node
                        .iter()
                        .map(|arg| self.eval_expr(arg))
                        .collect::<Result<Vec<_>, _>>()?;

                    callable.call(self, &args)
                } else {
                    Err(vec![RuntimeError::not_callable(callee_span, callee.ty())])
                }
            }

            ExprNode::Access { receiver, name } => {
                let receiver_span = receiver.span;
                let receiver = self.eval_expr(receiver)?;
                if let Value::Instance(instance) = &receiver {
                    if let Some(val) = instance.get_property(name.node) {
                        Ok(val)
                    } else {
                        Err(vec![RuntimeError::undefined_property(*name, receiver_span)])
                    }
                } else {
                    Err(vec![RuntimeError::not_instance(
                        receiver_span,
                        receiver.ty(),
                    )])
                }
            }
        }
    }

    /// Evaluate a short-circuiting boolean binary operator expression.
    fn eval_boolean_binop(
        &mut self,
        sym: Spanned<BooleanBinopSym>,
        lhs: &Spanned<Expr<'s>>,
        rhs: &Spanned<Expr<'s>>,
    ) -> RuntimeResult<'s, Value<'s>> {
        let lhs = self.eval_expr(lhs)?;

        match sym.node {
            BooleanBinopSym::Or => {
                if lhs.is_truthy() {
                    return Ok(lhs);
                }
            }

            BooleanBinopSym::And => {
                if !lhs.is_truthy() {
                    return Ok(lhs);
                }
            }
        }

        self.eval_expr(rhs)
    }

    /// Evaluate a non-boolean binary operator expression.
    fn eval_binop(
        &mut self,
        sym: Spanned<BinopSym>,
        lhs: Spanned<Value<'s>>,
        rhs: Spanned<Value<'s>>,
    ) -> RuntimeResult<'s, Value<'s>> {
        match sym.node {
            BinopSym::Eq => Ok(Value::Bool(self.value_eq(lhs, rhs))),
            BinopSym::Ne => Ok(Value::Bool(!self.value_eq(lhs, rhs))),

            BinopSym::Add => match (&lhs.node, &rhs.node) {
                (Value::Num(lhs), Value::Num(rhs)) => Ok(Value::Num(*lhs + *rhs)),
                (Value::Str(lhs), Value::Str(rhs)) => Ok(Value::Str(lhs.concat(rhs))),

                (Value::Str(_) | Value::Num(_), _) => {
                    let lhs_ty = lhs.node.ty();
                    let cause = Some(CoercionCause::BinopOperand {
                        sym,
                        operand: lhs.span,
                        operand_ty: lhs.node.ty(),
                    });
                    Err(vec![RuntimeError::InvalidCoercion {
                        val: rhs.span,
                        val_ty: rhs.node.ty(),
                        coerced_ty: lhs_ty,
                        cause,
                    }])
                }

                _ => {
                    let cause = CoercionCause::Binop { sym };
                    Err(join_errs(
                        self.coerce_to_num(lhs, cause),
                        self.coerce_to_num(rhs, cause),
                    )
                    .unwrap_err())
                }
            },

            // Boolean operators are intercepted and handled before ever calling this function; if
            // we get to this point, it's an operator that's expecting numerical operands.
            _ => {
                let cause = CoercionCause::Binop { sym };
                let (lhs, rhs) = join_errs(
                    self.coerce_to_num(lhs, cause),
                    self.coerce_to_num(rhs, cause),
                )?;
                Ok(sym.node.eval_num(lhs, rhs))
            }
        }
    }

    /// Evaluate a place expression.
    ///
    /// Returns a mutable reference to the value currently assigned to the evaluated place.
    fn eval_assign(
        &mut self,
        place: &Place<'s>,
        value: &Spanned<Expr<'s>>,
    ) -> RuntimeResult<'s, Value<'s>> {
        if let Some(receiver) = &place.receiver {
            let receiver_span = receiver.span;
            let receiver = self.eval_expr(receiver)?;
            if let Value::Instance(instance) = receiver {
                let val = self.eval_expr(value)?;
                instance
                    .get_property_place(place.name.node)
                    .set(val.clone());
                Ok(val)
            } else {
                Err(vec![RuntimeError::not_instance(
                    receiver_span,
                    receiver.ty(),
                )])
            }
        } else {
            let val = self.eval_expr(value)?;
            self.env
                .get_place(place.name)
                .ok_or_else(|| vec![RuntimeError::unbound_var_assign(place.name)])?
                .set(val.clone());
            Ok(val)
        }
    }

    /// Are these values equal?
    ///
    /// This is implemented as a method on the interpreter rather than on values to allow for
    /// looking up custom equality predicates on class instance values.
    fn value_eq(&mut self, lhs: Spanned<Value>, rhs: Spanned<Value>) -> bool {
        match (lhs.node, rhs.node) {
            (Value::Nil, Value::Nil) => true,
            (Value::Bool(b1), Value::Bool(b2)) => b1 == b2,
            (Value::Num(n1), Value::Num(n2)) => n1 == n2,
            // Importantly, we don't use the PartialEq implementation for StrValues, which
            // distinguishes between static and computed values
            (Value::Str(s1), Value::Str(s2)) => s1.as_ref() == s2.as_ref(),
            _ => false,
        }
    }

    /// Coerce a value to a number.
    ///
    /// Returns a coercion error if the value cannot be coerced.
    ///
    /// Currently no values besides numbers can be coerced to numbers, so this is functionally just
    /// a check to make sure a value has the correct type.
    fn coerce_to_num(
        &mut self,
        val: Spanned<Value>,
        cause: CoercionCause,
    ) -> RuntimeResult<'s, f64> {
        match val.node {
            Value::Num(n) => Ok(n),
            _ => Err(vec![RuntimeError::InvalidCoercion {
                val: val.span,
                val_ty: val.node.ty(),
                coerced_ty: Ty::Primitive(PrimitiveTy::Num),
                cause: Some(cause),
            }]),
        }
    }
}

pub struct PlaceVal<'e, 's> {
    val: RefMut<'e, Value<'s>>,
}

impl<'s> PlaceVal<'_, 's> {
    pub fn new<'e>(val: RefMut<'e, Value<'s>>) -> PlaceVal<'e, 's> {
        PlaceVal { val }
    }

    fn set(&mut self, value: Value<'s>) {
        *self.val = value;
    }
}

#[derive(Debug, Clone, Default)]
struct EnvBindings<'s> {
    bindings: Rc<RefCell<HashMap<Spanned<Symbol<'s>>, Value<'s>>>>,
}

impl<'s> EnvBindings<'s> {
    fn declare(&self, name: Spanned<Symbol<'s>>, init: Value<'s>) {
        self.bindings.borrow_mut().insert(name, init);
    }

    fn get(&self, name: Spanned<Symbol<'s>>) -> Option<Value<'s>> {
        self.bindings.borrow().get(&name).cloned()
    }

    fn get_place(&self, name: Spanned<Symbol<'s>>) -> Option<PlaceVal<'_, 's>> {
        let val = RefMut::filter_map(self.bindings.borrow_mut(), |bindings| {
            bindings.get_mut(&name)
        })
        .ok()?;
        Some(PlaceVal { val })
    }
}

#[derive(Debug, Clone)]
pub struct Env<'s> {
    global_binds: EnvBindings<'s>,
    local_binds: Vec<EnvBindings<'s>>,
    resolutions: ResolutionTable<'s>,
}

impl Default for Env<'_> {
    fn default() -> Self {
        let mut env = Self {
            global_binds: EnvBindings::default(),
            local_binds: Vec::new(),
            resolutions: ResolutionTable::default(),
        };
        Builtin::declare_builtins(&mut env);
        env
    }
}

// TODO(?): this struct is technically unsound. It's not bound to the lifetime
// of the environment it's guarding, so it's possible to exfiltrate it from the
// scope in which it's created.
//
// We _don't_ do that here, but it's possible! That may or may not be a concern.
pub(crate) struct ScopeGuard<'s> {
    env: *mut Env<'s>,
}

impl Drop for ScopeGuard<'_> {
    fn drop(&mut self) {
        unsafe {
            (*self.env)
                .local_binds
                .pop()
                .expect("cannot pop the global scope");
        }
    }
}

impl<'s> Env<'s> {
    pub(crate) fn push_scope(&mut self) -> ScopeGuard<'s> {
        self.local_binds.push(EnvBindings::default());
        ScopeGuard { env: self }
    }

    pub fn declare(&self, name: Spanned<Symbol<'s>>, init: Value<'s>) {
        let (binds, name) = self
            .local_binds
            .last()
            .map(|binds| (binds, name))
            .unwrap_or((&self.global_binds, name.with_span(Span::empty())));

        binds.declare(name, init);
    }

    fn get(&self, var: Spanned<Symbol<'s>>) -> Option<Value<'s>> {
        let (binds, decl) = self.lookup_scope(var);
        binds.get(decl)
    }

    fn get_place(&self, var: Spanned<Symbol<'s>>) -> Option<PlaceVal<'_, 's>> {
        let (binds, decl) = self.lookup_scope(var);
        binds.get_place(decl)
    }

    fn lookup_scope(&self, var: Spanned<Symbol<'s>>) -> (&EnvBindings<'s>, Spanned<Symbol<'s>>) {
        self.resolutions
            .lookup(var)
            .map(|(idx, span)| {
                debug_assert!(idx < self.local_binds.len());
                (
                    &self.local_binds[self.local_binds.len() - 1 - idx],
                    var.with_span(span),
                )
            })
            .unwrap_or((&self.global_binds, var.with_span(Span::empty())))
    }

    fn resolve(&mut self, stmts: &[Spanned<Stmt<'s>>]) {
        self.resolutions.resolve(stmts);
    }
}

impl<'s> Lit<'s> {
    fn eval(&self) -> Value<'s> {
        match *self {
            Lit::Nil => Value::Nil,
            Lit::Num(n) => Value::Num(n),
            Lit::Bool(b) => Value::Bool(b),
            Lit::Str(s) => Value::Str(StrValue::Static(s)),
        }
    }
}

impl BinopSym {
    fn is_num_num(self) -> bool {
        matches!(
            self,
            BinopSym::Sub | BinopSym::Add | BinopSym::Div | BinopSym::Mul | BinopSym::Mod
        )
    }

    fn num_num_op(self) -> fn(f64, f64) -> f64 {
        match self {
            BinopSym::Sub => Sub::sub,
            // BinopSym::Add => Add::add, // This case is handled in Interpreter::eval_binop
            BinopSym::Div => Div::div,
            BinopSym::Mul => Mul::mul,
            BinopSym::Mod => Rem::rem,
            _ => panic!(),
        }
    }

    fn num_bool_op(self) -> fn(&f64, &f64) -> bool {
        match self {
            BinopSym::Gt => PartialOrd::gt,
            BinopSym::Ge => PartialOrd::ge,
            BinopSym::Lt => PartialOrd::lt,
            BinopSym::Le => PartialOrd::le,
            _ => panic!(),
        }
    }

    fn eval_num<'s>(self, lhs: f64, rhs: f64) -> Value<'s> {
        if self.is_num_num() {
            Value::Num(self.num_num_op()(lhs, rhs))
        } else {
            Value::Bool(self.num_bool_op()(&lhs, &rhs))
        }
    }
}
