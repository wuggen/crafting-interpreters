//! Error recovery and diagnostic types for the parser.
//!
//! Error recovery and control flow in the parser are mediated via `Result`s of [`ParserError`]. The
//! actual errors presented to the user are implemented by [`ParserDiag`].

use super::Parser;
use crate::diag::{Diag, DiagKind, Diagnostic};
use crate::span::{Span, Spanned};
use crate::symbol::Symbol;
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
            ParserError::Handled(kind) | ParserError::Deferred(kind) => kind,
        }
    }
}

/// Kinds of parser errors.
#[derive(Debug)]
pub enum ParserErrorKind<'s> {
    /// An unexpected token, or EOF.
    Unexpected(Option<Spanned<Token<'s>>>),

    /// An unexpected token when expecting a function or method name.
    MissingFunName(Option<Spanned<Token<'s>>>),

    /// A spurious statement end.
    ///
    /// This could either be caused by a semicolon where there shouldn't be one, or a missing
    /// semicolon where a statement end was expected. Either way, the parser should not sync to a
    /// statement boundary, since it is reasonable to assume it's at one.
    SpuriousStmtEnd,

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

    pub const fn missing_fun_name(found: Option<Spanned<Token<'s>>>) -> ParserErrorKind<'s> {
        ParserErrorKind::MissingFunName(found)
    }

    pub const fn spurious_stmt_end() -> ParserErrorKind<'s> {
        ParserErrorKind::SpuriousStmtEnd
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

#[derive(Debug, Clone, Copy)]
pub enum Pair {
    Parens,
    Braces,
}

impl Pair {
    pub fn open_tok<'a>(&self) -> Token<'a> {
        match self {
            Pair::Parens => Token::OpenParen,
            Pair::Braces => Token::OpenBrace,
        }
    }

    pub fn close_tok<'a>(&self) -> Token<'a> {
        match self {
            Pair::Parens => Token::CloseParen,
            Pair::Braces => Token::CloseBrace,
        }
    }

    fn desc(&self) -> &'static str {
        match self {
            Pair::Parens => "parentheses",
            Pair::Braces => "braces",
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum FunCtx {
    Def,
    Call,
}

impl FunCtx {
    fn desc(&self) -> &'static str {
        match self {
            FunCtx::Def => "definition",
            FunCtx::Call => "call",
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum FunKind {
    Fun,
    Method,
}

impl FunKind {
    fn desc(&self) -> &'static str {
        match self {
            FunKind::Fun => "function",
            FunKind::Method => "method",
        }
    }

    pub fn arg_num(&self) -> u32 {
        match self {
            FunKind::Fun => 255,
            FunKind::Method => 254,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum DeclKind {
    Var,
    Fun,
    Class,
}

impl DeclKind {
    fn desc(&self) -> &'static str {
        match self {
            DeclKind::Var => "variable",
            DeclKind::Fun => "function",
            DeclKind::Class => "class",
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

    MissingDeclName {
        kind: DeclKind,
        decl: Span,
        expected_name: Span,
    },

    MissingMethodName {
        class: Spanned<Symbol<'s>>,
        expected_name: Span,
    },

    MissingPropertyName {
        receiver: Span,
        expected_name: Span,
    },

    InvalidPlaceExpr {
        place: Span,
        eq: Span,
    },

    ExcessiveArgs {
        ctx: FunCtx,
        kind: FunKind,
        fun_name: Span,
        arg: Span,
    },

    ReturnOutsideFun {
        site: Span,
    },

    BreakOutsideLoop {
        site: Span,
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

    pub const fn missing_decl_name(kind: DeclKind, decl: Span, expected_name: Span) -> Self {
        Self::MissingDeclName {
            kind,
            decl,
            expected_name,
        }
    }

    pub const fn missing_var_name(decl: Span, expected_name: Span) -> Self {
        Self::missing_decl_name(DeclKind::Var, decl, expected_name)
    }

    pub const fn missing_fun_name(decl: Span, expected_name: Span) -> Self {
        Self::missing_decl_name(DeclKind::Fun, decl, expected_name)
    }

    pub const fn missing_class_name(decl: Span, expected_name: Span) -> Self {
        Self::missing_decl_name(DeclKind::Class, decl, expected_name)
    }

    pub const fn missing_method_name(class: Spanned<Symbol<'s>>, expected_name: Span) -> Self {
        Self::MissingMethodName {
            class,
            expected_name,
        }
    }

    pub const fn missing_property_name(receiver: Span, expected_name: Span) -> Self {
        Self::MissingPropertyName {
            receiver,
            expected_name,
        }
    }

    pub const fn invalid_place_expr(place: Span, eq: Span) -> Self {
        Self::InvalidPlaceExpr { place, eq }
    }

    pub const fn excessive_args(ctx: FunCtx, kind: FunKind, fun_name: Span, arg: Span) -> Self {
        Self::ExcessiveArgs {
            ctx,
            kind,
            fun_name,
            arg,
        }
    }

    pub const fn return_outside_fun(site: Span) -> Self {
        Self::ReturnOutsideFun { site }
    }

    pub const fn break_outside_loop(site: Span) -> Self {
        Self::BreakOutsideLoop { site }
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
            ParserDiag::MissingDeclName { kind, .. } => {
                format!("missing name in {} declaration", kind.desc())
            }
            ParserDiag::MissingMethodName { class, .. } => format!(
                "missing method name in definition of class `{}`",
                class.node
            ),
            ParserDiag::MissingPropertyName { .. } => {
                "missing property name in access expression".into()
            }
            ParserDiag::InvalidPlaceExpr { .. } => {
                "invalid place expression on left side of assignment".into()
            }
            ParserDiag::ExcessiveArgs { ctx, kind, .. } => format!(
                "more than {} arguments in {} {}",
                kind.arg_num(),
                kind.desc(),
                ctx.desc(),
            ),
            ParserDiag::ReturnOutsideFun { .. } => {
                "return statement found outside of an enclosing function definition".into()
            }
            ParserDiag::BreakOutsideLoop { .. } => {
                "break statement outside of an enclosing loop".into()
            }
        }
    }

    fn expected(&mut self) -> Option<&'static str> {
        match self {
            ParserDiag::Unexpected { expected, .. } => expected.take(),

            ParserDiag::UnclosedPair { kind, .. } => Some(kind.close_tok().summary()),
            ParserDiag::UnterminatedStmt { .. } => Some("`;`"),
            ParserDiag::EarlyClosePair { .. } | ParserDiag::EarlyTerminatedStmt { .. } => {
                Some("expression")
            }
            ParserDiag::MissingDeclName { .. }
            | ParserDiag::MissingMethodName { .. }
            | ParserDiag::MissingPropertyName { .. }
            | ParserDiag::InvalidPlaceExpr { .. } => Some("identifier"),
            ParserDiag::ExcessiveArgs { .. } => None,
            ParserDiag::ReturnOutsideFun { .. } => None,
            ParserDiag::BreakOutsideLoop { .. } => None,
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

            ParserDiag::MissingDeclName {
                kind,
                decl,
                expected_name,
            } => diag
                .with_primary(expected_name, format!("expected {} name here", kind.desc()))
                .with_secondary(decl, format!("{} declaration requires a name", kind.desc())),

            ParserDiag::MissingMethodName { expected_name, .. } => {
                diag.with_primary(expected_name, "expected method name here")
            }

            ParserDiag::MissingPropertyName {
                receiver,
                expected_name,
            } => diag
                .with_primary(expected_name, "expected property name after '.' operator")
                .with_secondary(receiver, "property access on this receiver"),

            ParserDiag::InvalidPlaceExpr { place, eq } => diag
                .with_primary(place, "invalid place expression")
                .with_secondary(eq, "expected place expression due to assignment here"),

            ParserDiag::ExcessiveArgs {
                ctx,
                kind,
                fun_name,
                arg,
            } => diag
                .with_primary(arg, self.message())
                .with_secondary(fun_name, format!("arguments for this {}", ctx.desc()))
                .with_note(format!(
                    "{}s can have no more than {} arguments",
                    kind.desc(),
                    kind.arg_num()
                )),

            ParserDiag::ReturnOutsideFun { site } => diag.with_primary(site, self.message()),

            ParserDiag::BreakOutsideLoop { site } => diag.with_primary(site, self.message()),
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
