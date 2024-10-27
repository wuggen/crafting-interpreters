//! Runtime errors.

use crate::diag::{Diag, DiagKind, Diagnostic};
use crate::span::{Span, Spanned};
use crate::symbol::Symbol;
use crate::syn::{BinopSym, UnopSym};
use crate::ty::{PrimitiveTy, Ty};
use crate::util::oxford_or;

/// A Lox runtime error.
#[derive(Debug, Clone)]
pub enum RuntimeError<'s> {
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
}

impl<'s> RuntimeError<'s> {
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

            RuntimeError::UnboundVariable { site, usage } => {
                let message = match usage {
                    VarUsage::Reference => format!("reference to unbound variable `{}`", site.node),
                    VarUsage::Assign => format!("assignment to unbound variable `{}`", site.node),
                };

                Diag::new(DiagKind::Error, message)
                    .with_primary(site.span, "variable is not bound at this point")
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
