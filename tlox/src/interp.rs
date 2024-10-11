//! Evaluation of Lox syntax trees.
use std::ops::{Add, Div, Mul, Rem, Sub};

use crate::diag::Diagnostic;
use crate::error::{join_errs, CoercionCause, RuntimeError, RuntimeResult};
use crate::intern::Interned;
use crate::span::{Spannable, Spanned};
use crate::syn::{BinopSym, Expr, Lit, UnopSym};
use crate::ty::{PrimitiveTy, Ty};
use crate::val::{StrValue, Value};

#[cfg(test)]
mod test;

/// A tree-walking Lox interpreter.
pub struct Interpreter {}

impl Interpreter {
    /// Evaluate a Lox syntax tree.
    pub fn eval(&self, expr: &Spanned<Interned<Expr>>) -> Option<Value> {
        match self.eval_expression(expr) {
            Ok(val) => Some(val),
            Err(errs) => {
                for err in errs {
                    err.emit();
                }
                None
            }
        }
    }

    /// Evaluate an expression.
    fn eval_expression(&self, expr: &Spanned<Interned<Expr>>) -> RuntimeResult<Value> {
        match &*expr.node {
            Expr::Literal(lit) => Ok(lit.eval()),

            Expr::Unop { sym, operand } => {
                let operand_val = self.eval_expression(operand)?;
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

            Expr::Binop { sym, lhs, rhs } => {
                let lop = self.eval_expression(lhs)?;
                let rop = self.eval_expression(rhs)?;

                self.eval_binop(*sym, lop.spanned(lhs.span), rop.spanned(rhs.span))
            }
        }
    }

    /// Evaluate a binary operator expression.
    fn eval_binop(
        &self,
        sym: Spanned<BinopSym>,
        lhs: Spanned<Value>,
        rhs: Spanned<Value>,
    ) -> RuntimeResult<Value> {
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

    /// Are these values equal?
    ///
    /// This is implemented as a method on the interpreter rather than on values to allow for
    /// looking up custom equality predicates on class instance values.
    fn value_eq(&self, lhs: Spanned<Value>, rhs: Spanned<Value>) -> bool {
        match (lhs.node, rhs.node) {
            (Value::Nil, Value::Nil) => true,
            (Value::Bool(b1), Value::Bool(b2)) => b1 == b2,
            (Value::Num(n1), Value::Num(n2)) => n1 == n2,
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
    fn coerce_to_num(&self, val: Spanned<Value>, cause: CoercionCause) -> RuntimeResult<f64> {
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

impl Lit {
    fn eval(&self) -> Value {
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

    fn eval_num(self, lhs: f64, rhs: f64) -> Value {
        if self.is_num_num() {
            Value::Num(self.num_num_op()(lhs, rhs))
        } else {
            Value::Bool(self.num_bool_op()(&lhs, &rhs))
        }
    }
}
