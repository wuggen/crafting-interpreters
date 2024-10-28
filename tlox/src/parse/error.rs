//! Error recovery and diagnostic types for the parser.
//!
//! Error recovery and control flow in the parser are mediated via `Result`s of [`ParserError`]. The
//! actual errors presented to the user are implemented by [`ParserDiag`].

use super::Parser;
use crate::diag::{Diag, DiagKind, Diagnostic};
use crate::span::{Span, Spanned};
use crate::tok::Token;

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

    /// A spurious block statement end.
    ///
    /// This is caused by an unexpected closing brace while parsing a block statement. As for
    /// `SpuriousStmtEnd`, synchronization is not needed outside of the block statement.
    SpuriousBlockEnd,

    /// An assignment was attempted to an invalid place expression.
    InvalidPlaceExpr,
}

impl<'s> ParserError<'s> {
    pub const fn unexpected(tok: Option<Spanned<Token<'s>>>) -> ParserErrorKind<'s> {
        ParserErrorKind::Unexpected(tok)
    }

    pub const fn unexpected_tok(token: Spanned<Token<'s>>) -> ParserErrorKind<'s> {
        Self::unexpected(Some(token))
    }

    pub const fn eof() -> ParserErrorKind<'s> {
        Self::unexpected(None)
    }

    pub const fn spurious_stmt_end() -> ParserErrorKind<'s> {
        ParserErrorKind::SpuriousStmtEnd
    }

    pub const fn spurious_block_end() -> ParserErrorKind<'s> {
        ParserErrorKind::SpuriousBlockEnd
    }

    pub const fn invalid_place_expr() -> ParserErrorKind<'s> {
        ParserErrorKind::InvalidPlaceExpr
    }
}

impl<'s> ParserErrorKind<'s> {
    pub const fn handled(self) -> ParserError<'s> {
        ParserError::Handled(self)
    }

    pub const fn deferred(self) -> ParserError<'s> {
        ParserError::Deferred(self)
    }
}

#[derive(Debug)]
pub enum Pair {
    Parens,
    Braces,
}

impl Pair {
    fn close_tok(&self) -> Token<'static> {
        match self {
            Pair::Parens => Token::RightParen,
            Pair::Braces => Token::RightBrace,
        }
    }

    fn desc(&self) -> &'static str {
        match self {
            Pair::Parens => "parentheses",
            Pair::Braces => "braces",
        }
    }
}

#[derive(Debug)]
pub enum ParserDiag<'s> {
    Unexpected {
        tok: Option<Token<'s>>,
        span: Span,
        expected: Option<&'static str>,
    },

    EarlyClosePair {
        kind: Pair,
        open: Span,
        close: Span,
    },

    UnclosedPair {
        kind: Pair,
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

    InvalidPlaceExpr {
        place: Span,
        eq: Span,
    },
}

impl<'s> ParserDiag<'s> {
    pub fn unexpected(
        parser: &Parser<'s>,
        maybe_tok: Option<Spanned<Token<'s>>>,
        expected: impl Into<Option<&'static str>>,
    ) -> Self {
        let (tok, span) = maybe_tok
            .map(|tok| (Some(tok.node), tok.span))
            .unwrap_or_else(|| (None, parser.end_of_source()));
        Self::Unexpected {
            tok,
            span,
            expected: expected.into(),
        }
    }

    pub fn unexpected_tok(
        parser: &Parser<'s>,
        tok: Spanned<Token<'s>>,
        expected: impl Into<Option<&'static str>>,
    ) -> Self {
        Self::unexpected(parser, Some(tok), expected)
    }

    pub const fn early_close_pair(kind: Pair, open: Span, close: Span) -> Self {
        Self::EarlyClosePair { kind, open, close }
    }

    pub const fn early_close_paren(open: Span, close: Span) -> Self {
        Self::early_close_pair(Pair::Parens, open, close)
    }

    pub const fn early_close_brace(open: Span, close: Span) -> Self {
        Self::early_close_pair(Pair::Braces, open, close)
    }

    pub const fn unclosed_pair(kind: Pair, open: Span, expected_close: Span) -> Self {
        Self::UnclosedPair {
            kind,
            open,
            expected_close,
        }
    }

    pub const fn unclosed_paren(open: Span, expected_close: Span) -> Self {
        Self::unclosed_pair(Pair::Parens, open, expected_close)
    }

    pub const fn unclosed_brace(open: Span, expected_close: Span) -> Self {
        Self::unclosed_pair(Pair::Braces, open, expected_close)
    }

    pub const fn unterminated_stmt(stmt: Span, expected_semi: Span) -> Self {
        Self::UnterminatedStmt {
            stmt,
            expected_semi,
        }
    }

    pub const fn early_terminated_stmt(semi: Span) -> Self {
        Self::EarlyTerminatedStmt { semi }
    }

    pub const fn missing_var_name(decl: Span, expected_name: Span) -> Self {
        Self::MissingVarName {
            decl,
            expected_name,
        }
    }

    pub const fn invalid_place_expr(place: Span, eq: Span) -> Self {
        Self::InvalidPlaceExpr { place, eq }
    }
}

impl ParserDiag<'_> {
    fn message(&self) -> String {
        match self {
            ParserDiag::Unexpected { tok: Some(tok), .. } => {
                format!("unexpected {} token in input", tok.summary())
            }
            ParserDiag::Unexpected { tok: None, .. } => "unexpected end of input".into(),
            ParserDiag::EarlyClosePair { kind, .. } => {
                format!("{} closed prematurely", kind.desc())
            }
            ParserDiag::UnclosedPair { kind, .. } => format!("unclosed {}", kind.desc()),
            ParserDiag::UnterminatedStmt { .. } => "unterminated statement".into(),
            ParserDiag::EarlyTerminatedStmt { .. } => "statement terminated prematurely".into(),
            ParserDiag::MissingVarName { .. } => "missing name in variable declaration".into(),
            ParserDiag::InvalidPlaceExpr { .. } => {
                "invalid place expression on left side of assignment".into()
            }
        }
    }

    fn expected(&mut self) -> Option<&'static str> {
        match self {
            ParserDiag::Unexpected { expected, .. } => expected.take(),

            ParserDiag::EarlyClosePair { .. } => Some("expression"),
            ParserDiag::UnclosedPair { kind, .. } => Some(kind.close_tok().summary()),
            ParserDiag::UnterminatedStmt { .. } => Some("`;`"),
            ParserDiag::EarlyTerminatedStmt { .. } => Some("expression"),
            ParserDiag::MissingVarName { .. } => Some("identifier"),
            ParserDiag::InvalidPlaceExpr { .. } => Some("identifier"),
        }
    }

    fn elaborate(self, diag: Diag) -> Diag {
        match self {
            ParserDiag::Unexpected { tok, span, .. } => match tok {
                Some(_) => diag.with_primary(span, "unexpected token here"),
                None => diag.with_primary(span, "end of input here"),
            },

            ParserDiag::EarlyClosePair { kind, open, close } => diag
                .with_primary(close, format!("{} closed here", kind.desc()))
                .with_secondary(open, format!("{} opened here", kind.desc())),

            ParserDiag::UnclosedPair {
                kind,
                open,
                expected_close,
            } => diag
                .with_primary(
                    expected_close,
                    format!("{} should have been closed here", kind.desc()),
                )
                .with_secondary(open, format!("{} opened here", kind.desc())),

            ParserDiag::UnterminatedStmt {
                stmt,
                expected_semi,
            } => diag
                .with_primary(expected_semi, "statement should have been terminated here")
                .with_secondary(stmt, "this statement"),

            ParserDiag::EarlyTerminatedStmt { semi } => {
                diag.with_primary(semi, "statement terminated here")
            }

            ParserDiag::MissingVarName {
                decl,
                expected_name,
            } => diag
                .with_primary(expected_name, "expected variable name here")
                .with_secondary(decl, "declaration requires a variable name"),

            ParserDiag::InvalidPlaceExpr { place, eq } => diag
                .with_primary(place, "invalid place expression")
                .with_secondary(eq, "expected place expression due to assignment here"),
        }
    }
}

impl Diagnostic for ParserDiag<'_> {
    fn into_diag(mut self) -> Diag {
        let mut diag = Diag::new(DiagKind::Error, self.message());
        if let Some(expected) = self.expected() {
            diag = diag.with_note(format!("expected {expected}"));
        }
        self.elaborate(diag)
    }
}
