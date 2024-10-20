//! Runtime errors.

use crate::diag::{Diag, DiagKind, Diagnostic};
use crate::span::{Span, Spanned};
use crate::syn::{BinopSym, UnopSym};
use crate::ty::{PrimitiveTy, Ty};
use crate::util::oxford_or;

/// A Lox runtime error.
#[derive(Debug, Clone)]
pub enum RuntimeError {
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
}

/// A `Result` type specialized to runtime errors.
pub type RuntimeResult<T> = Result<T, Vec<RuntimeError>>;

/// Join the errors of two runtime results, if any.
///
/// If either of the given results is an `Err`, returns an `Err` containing the combined
/// [`RuntimeError`]s of each. If both are `Ok`, returns their results.
pub fn join_errs<A, B>(a: RuntimeResult<A>, b: RuntimeResult<B>) -> RuntimeResult<(A, B)> {
    match (a, b) {
        (Err(mut a_errs), Err(mut b_errs)) => {
            a_errs.append(&mut b_errs);
            Err(a_errs)
        }

        (Err(errs), Ok(_)) | (Ok(_), Err(errs)) => Err(errs),

        (Ok(a), Ok(b)) => Ok((a, b)),
    }
}

impl Diagnostic for RuntimeError {
    fn into_diag(self) -> Diag {
        match self {
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
                            "operator `{}` expects operands of type {}",
                            sym.node,
                            sym.node.expected_tys()
                        )),

                    None => diag,
                }
            }
        }
    }
}

/// The reason a type coercion was attemtped.
#[derive(Debug, Clone, Copy)]
pub enum CoercionCause {
    /// Attempted to coerce the operand of a unary operator to the correct type.
    Unop { sym: Spanned<UnopSym> },

    /// Attempted to coerce an operand of a binary operator to the correct type.
    Binop { sym: Spanned<BinopSym> },
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
            BinopSym::Eq | BinopSym::Ne => "any".into(),
            BinopSym::Gt | BinopSym::Ge | BinopSym::Lt | BinopSym::Le => {
                PrimitiveTy::Num.to_string()
            }
            BinopSym::Add => oxford_or(&[PrimitiveTy::Num, PrimitiveTy::Str]).to_string(),
            BinopSym::Sub | BinopSym::Div | BinopSym::Mul | BinopSym::Mod => {
                PrimitiveTy::Num.to_string()
            }
        }
    }
}
