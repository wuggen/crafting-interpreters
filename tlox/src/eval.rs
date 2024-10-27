//! Evaluation of Lox syntax trees.
use std::collections::HashMap;
use std::io::Write;
use std::ops::{Add, Div, Mul, Rem, Sub};

use crate::diag::Diagnostic;
use crate::error::{join_errs, CoercionCause, RuntimeError, RuntimeResult};
use crate::output::OutputStream;
use crate::span::{Spannable, Spanned};
use crate::symbol::Symbol;
use crate::syn::{BinopSym, Expr, ExprNode, Lit, Place, Program, Stmt, UnopSym};
use crate::ty::{PrimitiveTy, Ty};
use crate::val::{StrValue, Value};

#[cfg(test)]
mod test;

/// A tree-walking Lox interpreter.
#[derive(Default)]
pub struct Interpreter<'s, 'out> {
    env: Env<'s>,
    output: OutputStream<'out>,
}

impl<'out> Interpreter<'_, 'out> {
    pub fn with_output(output: OutputStream<'out>) -> Self {
        Self {
            env: Env::default(),
            output,
        }
    }

    pub fn with_vec_output(output: &'out mut Vec<u8>) -> Self {
        Self::with_output(OutputStream::with(output))
    }
}

impl<'s> Interpreter<'s, '_> {
    /// Evaluate a Lox program.
    pub fn eval(&mut self, program: &Program<'s>) {
        for stmt in &program.stmts {
            if let Err(errs) = self.eval_stmt(stmt) {
                for err in errs {
                    err.emit();
                }
                return;
            }
        }
    }

    fn eval_stmt(&mut self, stmt: &Spanned<Stmt<'s>>) -> RuntimeResult<'s, ()> {
        match &stmt.node {
            Stmt::Expr { val } => {
                self.eval_expr(val)?;
            }

            Stmt::Print { val } => {
                let val = self.eval_expr(val)?;
                writeln!(self.output, "{val}").unwrap();
            }

            Stmt::Decl { name, init } => {
                let init = if let Some(expr) = init {
                    self.eval_expr(expr)?
                } else {
                    Value::Nil
                };

                self.env.declare(name.node, init);
            }
        }

        Ok(())
    }

    /// Evaluate an expression.
    fn eval_expr(&mut self, expr: &Spanned<Expr<'s>>) -> RuntimeResult<'s, Value<'s>> {
        match &*expr.node {
            ExprNode::Literal(lit) => Ok(lit.eval()),

            ExprNode::Var(name) => self
                .env
                .get(*name)
                .ok_or_else(|| vec![RuntimeError::unbound_var_ref((*name).spanned(expr.span))]),

            ExprNode::Group(expr) => self.eval_expr(expr),

            ExprNode::Unop { sym, operand } => {
                let operand_val = self.eval_expr(operand)?;
                match sym.node {
                    UnopSym::Not => Ok(Value::Bool(!operand_val.is_truthy())),

                    UnopSym::Neg => {
                        let operand_val = self.coerce_to_num(
                            operand_val.spanned(operand.span),
                            CoercionCause::Unop { sym: *sym },
                        )?;
                        Ok(Value::Num(-operand_val))
                    }
                }
            }

            ExprNode::Binop { sym, lhs, rhs } => {
                let lop = self.eval_expr(lhs)?;
                let rop = self.eval_expr(rhs)?;

                self.eval_binop(*sym, lop.spanned(lhs.span), rop.spanned(rhs.span))
            }

            ExprNode::Assign { place, val } => {
                let val = self.eval_expr(&val)?;
                *self.eval_place(&place)? = val.clone();
                Ok(val)
            }
        }
    }

    /// Evaluate a binary operator expression.
    fn eval_binop(
        &mut self,
        sym: Spanned<BinopSym>,
        lhs: Spanned<Value<'s>>,
        rhs: Spanned<Value<'s>>,
    ) -> RuntimeResult<'s, Value<'s>> {
        match (sym.node, &lhs.node, &rhs.node) {
            (BinopSym::Add, Value::Str(lnode), Value::Str(rnode)) => {
                Ok(Value::Str(lnode.concat(rnode)))
            }

            (BinopSym::Eq, _, _) => Ok(Value::Bool(self.value_eq(lhs, rhs))),
            (BinopSym::Ne, _, _) => Ok(Value::Bool(!self.value_eq(lhs, rhs))),

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
    fn eval_place(&mut self, place: &Spanned<Place<'s>>) -> RuntimeResult<'s, &mut Value<'s>> {
        match place.node {
            Place::Var(name) => self
                .env
                .get_mut(name)
                .ok_or_else(|| vec![RuntimeError::unbound_var_assign(name.spanned(place.span))]),
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

#[derive(Debug, Default)]
struct Env<'s> {
    bindings: HashMap<Symbol<'s>, Value<'s>>,
    parent: Option<Box<Env<'s>>>,
}

impl<'s> Env<'s> {
    fn with_parent(parent: Env<'s>) -> Self {
        Self {
            parent: Some(Box::new(parent)),
            ..Default::default()
        }
    }

    fn declare(&mut self, name: Symbol<'s>, init: Value<'s>) {
        self.bindings.insert(name, init);
    }

    fn get(&self, name: Symbol<'s>) -> Option<Value<'s>> {
        self.bindings
            .get(&name)
            .cloned()
            .or_else(|| self.parent.as_ref().and_then(|env| env.get(name)))
    }

    fn get_mut(&mut self, name: Symbol<'s>) -> Option<&mut Value<'s>> {
        self.bindings
            .get_mut(&name)
            .or_else(|| self.parent.as_mut().and_then(|env| env.get_mut(name)))
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
            BinopSym::Add => Add::add,
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
