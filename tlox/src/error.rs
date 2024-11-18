//! Runtime errors.

use crate::callable::Callable;
use crate::diag::{Diag, DiagKind, Diagnostic};
use crate::span::{Span, Spanned};
use crate::symbol::Symbol;
use crate::syn::{BinopSym, Expr, UnopSym};
use crate::ty::{PrimitiveTy, Ty};
use crate::val::{CallableValue, Value};

/// A Lox runtime error.
#[derive(Debug, Clone)]
pub enum RuntimeError<'s> {
    /// A function return.
    ///
    /// This is not an error per se, but rather a mediator of control flow within the treewalking
    /// interpreter.
    FunReturn { val: Value<'s> },

    /// An invalid type coercion was attempted.
    InvalidCoercion {
        /// Span of the coerced value.
        val: Span,

        /// Dynamic type of the value.
        val_ty: Ty,

        /// Type to which coercion was attempted.
        coerced_ty: Ty,

        /// If available, the reason for the coercion.
        cause: Option<CoercionCause>,
    },

    /// An unbound variable name was referenced.
    UnboundVariable {
        /// Span of the variable reference.
        site: Spanned<Symbol<'s>>,
        usage: VarUsage,
    },

    /// Attempted to call a non-Callable value.
    NotCallable {
        /// Span of the expression that was called.
        site: Span,
        /// Type of the value that was called.
        ty: Ty,
    },

    /// Called a function with the incorrect number of arguments.
    UnexpectedArgCount {
        callable: Spanned<Symbol<'s>>,
        args: Span,
        expected: u8,
        found: u8,
    },
}

impl<'s> RuntimeError<'s> {
    pub fn fun_return(val: Value<'s>) -> Self {
        Self::FunReturn { val }
    }

    pub fn unbound_var_ref(site: Spanned<Symbol<'s>>) -> Self {
        Self::UnboundVariable {
            site,
            usage: VarUsage::Reference,
        }
    }

    pub fn unbound_var_assign(site: Spanned<Symbol<'s>>) -> Self {
        Self::UnboundVariable {
            site,
            usage: VarUsage::Assign,
        }
    }

    pub fn not_callable(site: Span, ty: Ty) -> Self {
        Self::NotCallable { site, ty }
    }

    pub fn unexpected_arg_count(
        callable: Spanned<&CallableValue<'s>>,
        args: &Spanned<Vec<Spanned<Expr<'s>>>>,
    ) -> Self {
        let expected = callable.node.arity();
        let found = args.node.len() as u8;
        let callable = callable.map(Callable::name);
        let args = args.span;
        Self::UnexpectedArgCount {
            callable,
            args,
            expected,
            found,
        }
    }
}

#[derive(Debug, Clone)]
pub enum VarUsage {
    Reference,
    Assign,
}

/// A `Result` type specialized to runtime errors.
pub type RuntimeResult<'s, T> = Result<T, Vec<RuntimeError<'s>>>;

/// Join the errors of two runtime results, if any.
///
/// If either of the given results is an `Err`, returns an `Err` containing the combined
/// [`RuntimeError`]s of each. If both are `Ok`, returns their results.
pub fn join_errs<'s, A, B>(
    a: RuntimeResult<'s, A>,
    b: RuntimeResult<'s, B>,
) -> RuntimeResult<'s, (A, B)> {
    match (a, b) {
        (Err(mut a_errs), Err(mut b_errs)) => {
            a_errs.append(&mut b_errs);
            Err(a_errs)
        }

        (Err(errs), Ok(_)) | (Ok(_), Err(errs)) => Err(errs),

        (Ok(a), Ok(b)) => Ok((a, b)),
    }
}

impl Diagnostic for RuntimeError<'_> {
    fn into_diag(self) -> Diag {
        match self {
            RuntimeError::FunReturn { .. } => panic!("function return not caught"),
            RuntimeError::InvalidCoercion {
                val,
                val_ty,
                coerced_ty,
                cause,
            } => {
                let diag = Diag::new(
                    DiagKind::Error,
                    format!("cannot coerce {val_ty} to {coerced_ty}"),
                )
                .with_primary(val, format!("expression found to be of type {val_ty}"));
                match cause {
                    Some(CoercionCause::Unop { sym }) => diag
                        .with_secondary(
                            sym.span,
                            "value coerced due to use as an operand for this operator",
                        )
                        .with_note(format!(
                            "operator `{}` expects operand of type {}",
                            sym.node,
                            sym.node.expected_tys()
                        )),

                    Some(CoercionCause::Binop { sym }) => diag
                        .with_secondary(
                            sym.span,
                            "value coerced due to use as an operand to this operator",
                        )
                        .with_note(format!(
                            "operator `{}` expects {}",
                            sym.node,
                            sym.node.expected_tys()
                        )),

                    Some(CoercionCause::BinopOperand {
                        sym,
                        operand,
                        operand_ty,
                    }) => diag
                        .with_secondary(sym.span, "operands to this operator are incompatible")
                        .with_secondary(
                            operand,
                            format!("other operand found to be of type {operand_ty}"),
                        )
                        .with_note(format!(
                            "operator `{}` expects {}",
                            sym.node,
                            sym.node.expected_tys(),
                        )),

                    None => diag,
                }
            }

            RuntimeError::UnboundVariable { site, usage } => {
                let message = match usage {
                    VarUsage::Reference => format!("reference to unbound variable `{}`", site.node),
                    VarUsage::Assign => format!("assignment to unbound variable `{}`", site.node),
                };

                Diag::new(DiagKind::Error, message)
                    .with_primary(site.span, "variable is not bound at this point")
            }

            RuntimeError::NotCallable { site, ty } => {
                let message = format!("cannot call value of type {ty}");
                Diag::new(DiagKind::Error, message.clone())
                    .with_primary(site, message)
                    .with_note("only functions and class methods can be called")
            }

            RuntimeError::UnexpectedArgCount {
                callable,
                args,
                expected,
                found,
            } => Diag::new(
                DiagKind::Error,
                format!(
                    "callee `{}` expects {expected} arguments, found {found}",
                    callable.node
                ),
            )
            .with_primary(args, format!("found {found} arguments"))
            .with_secondary(
                callable.span,
                format!("callee `{}` expects {expected} arguments", callable.node),
            ),
        }
    }
}

/// The reason a type coercion was attemtped.
#[derive(Debug, Clone, Copy)]
pub enum CoercionCause {
    /// Operand to a unop was of a type unsupported by the operator.
    Unop { sym: Spanned<UnopSym> },

    /// Operand to a binop was of a type unsupported by the operator.
    Binop { sym: Spanned<BinopSym> },

    /// Operand to a binop was of an incompatible type to the other operand.
    BinopOperand {
        sym: Spanned<BinopSym>,
        operand: Span,
        operand_ty: Ty,
    },
}

impl UnopSym {
    fn expected_tys(self) -> String {
        match self {
            UnopSym::Not => PrimitiveTy::Bool.to_string(),
            UnopSym::Neg => PrimitiveTy::Num.to_string(),
        }
    }
}

impl BinopSym {
    fn expected_tys(self) -> String {
        match self {
            BinopSym::Bool(_) | BinopSym::Eq | BinopSym::Ne => "operands of any type".to_string(),
            BinopSym::Gt | BinopSym::Ge | BinopSym::Lt | BinopSym::Le => {
                format!("operands of type {}", PrimitiveTy::Num)
            }
            BinopSym::Add => format!(
                "both operands to be of type {}, or of type {}",
                PrimitiveTy::Num,
                PrimitiveTy::Str
            ),
            BinopSym::Sub | BinopSym::Div | BinopSym::Mul | BinopSym::Mod => {
                format!("operands of type {}", PrimitiveTy::Num)
            }
        }
    }
}
