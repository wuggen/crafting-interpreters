//! Error recovery and diagnostic types for the parser.
//!
//! Error recovery and control flow in the parser are mediated via `Result`s of [`ParserError`]. The
//! actual errors presented to the user are implemented by [`ParserDiag`].

use super::Parser;
use crate::diag::{Diag, DiagKind, Diagnostic};
use crate::span::{Span, Spanned};
use crate::tok::Token;
use crate::util::oxford_or;

/// Result type for parser errors.
pub type ParserRes<'s, T> = Result<T, ParserError<'s>>;

/// Extension trait for parser `Result`s to handle deferred errors.
pub trait ParserResExt<'s, T> {
    /// Catch a deferred error, returning a new result to take its place.
    ///
    /// If `self` is `Ok` or `Err(ParserError::Handled(_))`, this will have no effect and simply
    /// return `self`. If `self` is `Err(ParserError::Deferred(kind))`, this will return the
    /// result of `f(kind)`.
    fn catch_deferred(
        self,
        f: impl FnOnce(ParserErrorKind<'s>) -> ParserRes<'s, T>,
    ) -> ParserRes<'s, T>;
}

impl<'s, T> ParserResExt<'s, T> for ParserRes<'s, T> {
    fn catch_deferred(
        self,
        f: impl FnOnce(ParserErrorKind<'s>) -> ParserRes<'s, T>,
    ) -> ParserRes<'s, T> {
        match self {
            Err(ParserError::Deferred(diag)) => f(diag),
            other => other,
        }
    }
}

/// A parser error, for control flow and error recovery.
///
/// A parser error can either be handled where the source of the error was encountered (e.g. by
/// immediately emitting a user diagnostic), or it can be deferred to further up the parse tree
/// (e.g. to allow for more precise diagnostics).
#[derive(Debug)]
pub enum ParserError<'s> {
    Handled(ParserErrorKind<'s>),
    Deferred(ParserErrorKind<'s>),
}

impl<'s> ParserError<'s> {
    pub fn into_kind(self) -> ParserErrorKind<'s> {
        match self {
            ParserError::Handled(diag) | ParserError::Deferred(diag) => diag,
        }
    }
}

/// Kinds of parser errors.
#[derive(Debug)]
pub enum ParserErrorKind<'s> {
    /// An unexpected token, or EOF.
    Unexpected(Option<Spanned<Token<'s>>>),

    /// A spurious statement end.
    ///
    /// This could either be caused by a semicolon where there shouldn't be one, or a missing
    /// semicolon where a statement end was expected. Either way, the parser should not sync to a
    /// statement boundary, since it is reasonable to assume it's at one.
    SpuriousStmtEnd,
}

impl<'s> ParserError<'s> {
    pub fn unexpected(tok: Option<Spanned<Token<'s>>>) -> ParserErrorKind<'s> {
        ParserErrorKind::Unexpected(tok)
    }

    pub fn unexpected_tok(token: Spanned<Token<'s>>) -> ParserErrorKind<'s> {
        Self::unexpected(Some(token))
    }

    pub fn eof() -> ParserErrorKind<'s> {
        Self::unexpected(None)
    }

    pub fn spurious_stmt_end() -> ParserErrorKind<'s> {
        ParserErrorKind::SpuriousStmtEnd
    }
}

impl<'s> ParserErrorKind<'s> {
    pub fn handled(self) -> ParserError<'s> {
        ParserError::Handled(self)
    }

    pub fn deferred(self) -> ParserError<'s> {
        ParserError::Deferred(self)
    }
}

#[derive(Debug)]
pub enum ParserDiag<'s> {
    Unexpected {
        tok: Option<Token<'s>>,
        span: Span,
        expected: Vec<&'static str>,
    },

    EarlyCloseParen {
        open: Span,
        close: Span,
    },

    UnclosedParen {
        open: Span,
        expected_close: Span,
    },

    UnterminatedStmt {
        stmt: Span,
        expected_semi: Span,
    },

    EarlyTerminatedStmt {
        semi: Span,
    },

    MissingVarName {
        decl: Span,
        expected_name: Span,
    },
}

impl ParserDiag<'_> {
    pub fn extend_expected(mut self, new_expected: impl IntoIterator<Item = &'static str>) -> Self {
        if let Self::Unexpected { expected, .. } = &mut self {
            expected.extend(new_expected);
        }

        self
    }
}

impl<'s> ParserDiag<'s> {
    pub fn unexpected(
        parser: &Parser<'s>,
        maybe_tok: Option<Spanned<Token<'s>>>,
        expected: impl IntoIterator<Item = &'static str>,
    ) -> Self {
        let (tok, span) = maybe_tok
            .map(|tok| (Some(tok.node), tok.span))
            .unwrap_or_else(|| (None, parser.end_of_source()));
        Self::Unexpected {
            tok,
            span,
            expected: expected.into_iter().collect(),
        }
    }

    pub fn unexpected_tok(
        parser: &Parser<'s>,
        tok: Spanned<Token<'s>>,
        expected: impl IntoIterator<Item = &'static str>,
    ) -> Self {
        Self::unexpected(parser, Some(tok), expected)
    }

    pub fn early_close_paren(open: Span, close: Span) -> Self {
        Self::EarlyCloseParen { open, close }
    }

    pub fn unclosed_paren(open: Span, expected_close: Span) -> Self {
        Self::UnclosedParen {
            open,
            expected_close,
        }
    }

    pub fn unterminated_stmt(stmt: Span, expected_semi: Span) -> Self {
        Self::UnterminatedStmt {
            stmt,
            expected_semi,
        }
    }

    pub fn early_terminated_stmt(semi: Span) -> Self {
        Self::EarlyTerminatedStmt { semi }
    }

    pub fn missing_var_name(decl: Span, expected_name: Span) -> Self {
        Self::MissingVarName {
            decl,
            expected_name,
        }
    }
}

impl ParserDiag<'_> {
    fn message(&self) -> String {
        match self {
            ParserDiag::Unexpected { tok: Some(tok), .. } => {
                format!("unexpected {} token in input", tok.summary())
            }
            ParserDiag::Unexpected { tok: None, .. } => "unexpected end of input".into(),
            ParserDiag::EarlyCloseParen { .. } => "parentheses closed prematurely".into(),
            ParserDiag::UnclosedParen { .. } => "unclosed parentheses".into(),
            ParserDiag::UnterminatedStmt { .. } => "unterminated statement".into(),
            ParserDiag::EarlyTerminatedStmt { .. } => "statement terminated prematurely".into(),
            ParserDiag::MissingVarName { .. } => "missing name in variable declaration".into(),
        }
    }

    fn elaborate(self, mut diag: Diag) -> Diag {
        match self {
            ParserDiag::Unexpected {
                tok,
                span,
                expected,
            } => {
                if !expected.is_empty() {
                    diag = diag.with_note(format!("expected {}", oxford_or(&expected)));
                }

                match tok {
                    Some(_) => diag.with_primary(span, "unexpected token here"),
                    None => diag.with_primary(span, "end of input here"),
                }
            }

            ParserDiag::EarlyCloseParen { open, close } => diag
                .with_primary(close, "parentheses closed here")
                .with_secondary(open, "parentheses opened here"),

            ParserDiag::UnclosedParen {
                open,
                expected_close,
            } => diag
                .with_primary(expected_close, "expected `)` here")
                .with_secondary(open, "parentheses opened here"),

            ParserDiag::UnterminatedStmt {
                stmt,
                expected_semi,
            } => diag
                .with_primary(expected_semi, "expected semicolon here")
                .with_secondary(stmt, "this statement"),

            ParserDiag::EarlyTerminatedStmt { semi } => {
                diag.with_primary(semi, "statement terminated here")
            }

            ParserDiag::MissingVarName {
                decl,
                expected_name,
            } => diag
                .with_primary(expected_name, "expected variable name here")
                .with_secondary(decl, "declaration requires a variable name")
                .with_note("expected identifier"),
        }
    }

    fn expected(&self) -> Option<String> {
        match self {
            ParserDiag::Unexpected { expected, .. } => {
                if expected.is_empty() {
                    None
                } else {
                    Some(oxford_or(expected).to_string())
                }
            }

            ParserDiag::EarlyCloseParen { .. } => Some(oxford_or(&Parser::ATOM_STARTS).to_string()),
            ParserDiag::UnclosedParen { .. } => Some("`)`".into()),
            ParserDiag::UnterminatedStmt { .. } => Some("`;`".into()),
            ParserDiag::EarlyTerminatedStmt { .. } => {
                Some(oxford_or(&Parser::ATOM_STARTS).to_string())
            }
            ParserDiag::MissingVarName { .. } => Some("identifier".into()),
        }
    }
}

impl Diagnostic for ParserDiag<'_> {
    fn into_diag(self) -> Diag {
        let message = self.message();
        self.elaborate(Diag::new(DiagKind::Error, message))
    }
}
