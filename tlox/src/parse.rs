//! Parser for Lox.

use std::fmt::Write;
use std::iter::Peekable;

use crate::diag::{Diag, DiagKind, Diagnostic};
use crate::span::{Source, Span, Spannable, Spanned};
use crate::syn::*;
use crate::tok::{Lexer, Token};

#[cfg(test)]
mod test;

#[derive(Debug, Clone)]
pub struct Parser<'sm> {
    lexer: Peekable<Lexer<'sm>>,
    source: Source<'sm>,
}

// Grammar:
//
// expr -> equal
//
// ; Left-assoc
// equal -> comp ( ('!=' | '==') comp )*
//
// ; Left-assoc
// comp -> terms ( ('<' | '<=' | '>' | '>=') terms )*
//
// ; Left-assoc
// terms -> factors ( ('+' | '-') factors )*
//
// ; Left-assoc
// factors -> unary ( ('*' | '/' | '%') unary )*
//
// unary -> ('-' | '!') unary
//        | atom
//
// atom -> NUMBER | STRING | 'true' | 'false' | 'nil'
//       | '(' expr ')'

impl<'sm> Parser<'sm> {
    pub fn new(lexer: Lexer<'sm>) -> Self {
        let source = lexer.source();
        Self {
            lexer: lexer.peekable(),
            source,
        }
    }

    pub fn parse(mut self) -> Option<Spanned<Expr>> {
        self.expr().ok()
    }
}

/// Control flow and error recovery in the parser is mediated via these Results.
///
/// The errors that are actually reported to the user go through the diagnostic context instead.
type ParserRes<T> = Result<T, ParserError>;

#[derive(Debug, Clone, Copy)]
enum ParserError {
    /// Thrown when encountering an unexpected close paren. Diagnostic should not be immediately
    /// emitted in this case, but rather left to the code catching it, to allow for more precise
    /// diagnostics.
    ///
    /// For instance, the cases where a close paren appears appropos of nothing should get a
    /// different diagnostic than the case where an otherwise-correct set of parentheses is closed
    /// too early.
    ///
    /// Carries the span of the close paren to enable accurate emission of diagnostics. Code that
    /// catches this and emits the relevant diagnostic should, if it propagates the error instead
    /// of recovering, propagate it without the span so as to suppress redundant diagnostics.
    SpuriousCloseParen(Option<Span>),
    Eof,
    Other,
}

impl Parser<'_> {
    const ATOM_STARTS: [&'static str; 6] =
        ["number", "string", "`true`", "`false`", "`nil`", "`(`"];

    /// Get the one-character span representing the end of the source being parsed.
    fn end_of_source(&self) -> Span {
        let source = self.source.span();
        source.subspan(source.len() - 1..).unwrap()
    }

    /// Peek at the next token in the stream without advancing.
    fn peek(&mut self) -> Option<&Token> {
        self.lexer.peek().map(|tok| &tok.node)
    }

    /// Advance the token stream, returning the advanced-over token.
    fn advance(&mut self) -> Option<Spanned<Token>> {
        self.lexer.next()
    }

    /// Advance the token stream, applying the given function to the advanced-over token.
    fn advance_map<T>(&mut self, f: impl FnOnce(Token) -> T) -> Option<Spanned<T>> {
        let tok = self.advance()?;
        Some(f(tok.node).spanned(tok.span))
    }

    /// Advances one token, and tests the result.
    ///
    /// Returns the advanced-over token, as an `Ok` if it passed the test and as an `Err`
    /// otherwise. Returns `Err(None)` if it encounters EOF.
    ///
    /// Does not emit any diagnostics.
    fn advance_test(
        &mut self,
        test: impl FnOnce(&Token) -> bool,
    ) -> Result<Spanned<Token>, Option<Spanned<Token>>> {
        if let Some(tok) = self.advance() {
            if test(&tok.node) {
                Ok(tok)
            } else {
                Err(Some(tok))
            }
        } else {
            Err(None)
        }
    }

    /// Test the next token in the stream, without advancing.
    ///
    /// Returns true (a) there is a next token in the stream and (b) it passes the given test.
    /// Returns false if the next token fails or the stream is at EOF.
    fn check_next(&mut self, test: impl FnOnce(&Token) -> bool) -> bool {
        self.peek().map(test).unwrap_or_default()
    }

    /// Advance the token stream if the next token passes the given test.
    ///
    /// Unlike [`advance_test`](Self::advance_test), this will _not_ advance the stream if the next
    /// token would fail the test.
    fn advance_if(&mut self, test: impl FnOnce(&Token) -> bool) -> Option<Spanned<Token>> {
        if self.check_next(test) {
            self.advance()
        } else {
            None
        }
    }

    /// Advance over as many tokens as pass the given test.
    ///
    /// When this returns, it is guaranteed that either (a) the token stream is at EOF or (b) the
    /// next token fails the given test.
    fn advance_while(&mut self, test: impl Fn(&Token) -> bool) {
        while self.advance_if(&test).is_some() {}
    }

    /// Advance over as many tokens as fail the given test.
    ///
    /// When this returns, it is guaranteed that either (a) the token stream is at EOF or (b) the
    /// next token satisfies the given test.
    fn advance_until(&mut self, test: impl Fn(&Token) -> bool) {
        self.advance_while(|tok| !test(tok));
    }

    /// Advance the token stream to a synchronization point.
    ///
    /// This will repeatedly do the following:
    /// - Call `self.advance_until(until)`.
    /// - Check if the next token would satisfy `next`.
    ///   - If so, stop advancing and return.
    ///   - If not, and the stream is at EOF, return.
    ///   - If not, and there is a next toke, advance one token and repeat.
    fn synchronize(&mut self, until: impl Fn(&Token) -> bool, next: impl Fn(&Token) -> bool) {
        loop {
            self.advance_until(&until);
            if self.check_next(&next) {
                break;
            }

            self.advance();
        }
    }

    /// Synchronize to a statement start.
    ///
    /// This advances until the next non-operator keyword or method receiver start token.
    fn sync_to_statement(&mut self) {
        self.synchronize(|tok| matches!(tok, Token::Semicolon), Token::is_stmt_start);
    }

    /// Parse an expression.
    ///
    /// Corresponds to the `expr` grammar production.
    fn expr(&mut self) -> ParserRes<Spanned<Expr>> {
        debug_println!("= Parsing expression");
        self.equal()
    }

    /// Parse a left-associative chain of binary operators.
    ///
    /// Does the following:
    /// - Calls `operand(self)` to parse an operand.
    /// - If the next token satisfies `sym_test`:
    ///   - Advance and use `sym_map` to obtain the `BinopSym`.
    ///   - Parse another operand.
    ///   - Combine the two operands in a binop expression, and repeat, using the resulting
    ///     expression as the LHS of the next operator.
    /// - Otherwise, the chain is assumed to be completed, and the accumulated expression is
    ///   returned.
    fn binop_chain_left_assoc(
        &mut self,
        operand: impl Fn(&mut Self) -> ParserRes<Spanned<Expr>>,
        sym_test: impl Fn(&Token) -> bool,
        sym_map: impl Fn(Token) -> BinopSym,
    ) -> ParserRes<Spanned<Expr>> {
        let mut lhs = operand(self)?;

        while self.check_next(&sym_test) {
            let sym = self.advance_map(&sym_map).unwrap();
            match operand(self) {
                Ok(rhs) => {
                    lhs = Expr::binop(sym, lhs, rhs);
                }

                Err(ParserError::Eof) => {
                    break;
                }

                other => {
                    return other;
                }
            }
        }

        Ok(lhs)
    }

    /// Parse an equality operator chain.
    ///
    /// Corresponds to the `equal` grammar production.
    fn equal(&mut self) -> ParserRes<Spanned<Expr>> {
        self.binop_chain_left_assoc(
            Self::comp,
            |tok| matches!(tok, Token::EqualEqual | Token::BangEqual),
            |tok| match tok {
                Token::EqualEqual => BinopSym::Eq,
                Token::BangEqual => BinopSym::Ne,
                _ => unreachable!(),
            },
        )
    }

    /// Parse a comparison operator chain.
    ///
    /// Corresponds to the `comp` grammar production.
    fn comp(&mut self) -> ParserRes<Spanned<Expr>> {
        self.binop_chain_left_assoc(
            Self::terms,
            |tok| {
                matches!(
                    tok,
                    Token::Less | Token::LessEqual | Token::Greater | Token::GreaterEqual
                )
            },
            |tok| match tok {
                Token::Less => BinopSym::Lt,
                Token::LessEqual => BinopSym::Le,
                Token::Greater => BinopSym::Gt,
                Token::GreaterEqual => BinopSym::Ge,
                _ => unreachable!(),
            },
        )
    }

    /// Parse an additive (addition/subtraction) operator chain.
    ///
    /// Corresponds to the `terms` grammar production.
    fn terms(&mut self) -> ParserRes<Spanned<Expr>> {
        self.binop_chain_left_assoc(
            Self::factors,
            |tok| matches!(tok, Token::Plus | Token::Minus),
            |tok| match tok {
                Token::Plus => BinopSym::Add,
                Token::Minus => BinopSym::Sub,
                _ => unreachable!(),
            },
        )
    }

    /// Parse a multiplicative (multiplication/division/modulo) operator chain.
    ///
    /// Corresponds to the `factors` grammar production.
    fn factors(&mut self) -> ParserRes<Spanned<Expr>> {
        self.binop_chain_left_assoc(
            Self::unary,
            |tok| matches!(tok, Token::Star | Token::Slash | Token::Percent),
            |tok| match tok {
                Token::Star => BinopSym::Mul,
                Token::Slash => BinopSym::Div,
                Token::Percent => BinopSym::Mod,
                _ => unreachable!(),
            },
        )
    }

    /// Parse a unary (boolean/numerical negation) operator chain.
    ///
    /// Corresponds to the `unary` grammar production.
    fn unary(&mut self) -> ParserRes<Spanned<Expr>> {
        if self.check_next(|tok| matches!(tok, Token::Minus | Token::Bang)) {
            let sym = self
                .advance_map(|tok| match tok {
                    Token::Minus => UnopSym::Neg,
                    Token::Bang => UnopSym::Not,
                    _ => unreachable!(),
                })
                .unwrap();

            let operand = self.unary()?;

            Ok(Expr::unop(sym, operand))
        } else {
            self.atom()
        }
    }

    /// Parse an atomic (literal/identifier/parenthesized) expression.
    ///
    /// Corresponds to the `atom` grammar production.
    fn atom(&mut self) -> ParserRes<Spanned<Expr>> {
        if let Some(Spanned { node: tok, span }) = self.advance() {
            match tok {
                Token::Number(n) => Ok(Expr::literal(Lit::Num(n)).spanned(span)),
                Token::Str(s) => Ok(Expr::literal(Lit::Str(s)).spanned(span)),
                Token::Boolean(b) => Ok(Expr::literal(Lit::Bool(b)).spanned(span)),
                Token::Nil => Ok(Expr::literal(Lit::Nil).spanned(span)),
                Token::LeftParen => self.group(span),

                // Error productions
                Token::RightParen => Err(ParserError::SpuriousCloseParen(Some(span))),
                _ => {
                    ParserDiag::unexpected_tok(span, Self::ATOM_STARTS).emit();
                    Err(ParserError::Other)
                }
            }
        } else {
            ParserDiag::unexpected_eof(self.end_of_source(), Self::ATOM_STARTS).emit();
            Err(ParserError::Eof)
        }
    }

    /// Parse a parenthesized expression.
    ///
    /// Assumes that the opening parenthesis has already been advanced over. Uses the given span as
    /// the span for the opening paren, for diagnostic reporting.
    ///
    /// Corresponds to the parenthesized expression arm of the `atom` grammar production.
    fn group(&mut self, oparen_span: Span) -> ParserRes<Spanned<Expr>> {
        let expr = match self.expr() {
            Ok(expr) => expr,
            Err(ParserError::SpuriousCloseParen(Some(close_span))) => {
                ParserDiag::early_close_paren(oparen_span, close_span, Self::ATOM_STARTS).emit();
                return Err(ParserError::SpuriousCloseParen(None));
            }
            other => return other,
        };

        if let Err(maybe_tok) = self.advance_test(|tok| matches!(tok, Token::RightParen)) {
            let span = if let Some(tok) = maybe_tok {
                tok.span
            } else {
                self.end_of_source()
            };

            ParserDiag::unclosed_paren(oparen_span, span).emit();
            return Err(ParserError::Other);
        }

        Ok(expr)
    }
}

struct ParserDiag {
    primary_span: Span,
    info: ParserDiagInfo,
    expected: Vec<&'static str>,
}

enum ParserDiagInfo {
    Unexpected { kind: UnexpectedKind },

    EarlyCloseParen { open: Span },

    UnclosedParen { open: Span },
}

impl ParserDiagInfo {
    fn message(&self) -> &'static str {
        match self {
            Self::Unexpected {
                kind: UnexpectedKind::Token,
                ..
            } => "unexpected token in input",
            Self::Unexpected {
                kind: UnexpectedKind::Eof,
                ..
            } => "unexpected end of input",
            Self::EarlyCloseParen { .. } => "parentheses closed prematurely",
            Self::UnclosedParen { .. } => "unclosed parentheses",
        }
    }

    fn elaborate(self, primary_span: Span, diag: Diag) -> Diag {
        match self {
            ParserDiagInfo::Unexpected { .. } => {
                diag.with_primary(primary_span, "unexpected token")
            }

            ParserDiagInfo::EarlyCloseParen { open } => diag
                .with_primary(primary_span, "")
                .with_secondary(open, "parentheses opened here"),

            ParserDiagInfo::UnclosedParen { open } => diag
                .with_primary(primary_span, "parentheses should have been closed")
                .with_secondary(open, "parentheses opened here"),
        }
    }
}

enum UnexpectedKind {
    Token,
    Eof,
}

impl Diagnostic for ParserDiag {
    fn into_diag(self) -> Diag {
        let mut diag = Diag::new(DiagKind::Error, self.info.message());

        if !self.expected.is_empty() {
            let note = if self.expected.len() == 1 {
                format!("expected {}", self.expected[0])
            } else {
                let mut label = format!("expected {}", self.expected[0]);
                for expected in &self.expected[1..self.expected.len() - 1] {
                    write!(label, ", {}", expected).unwrap();
                }
                write!(label, " or {}", self.expected.last().unwrap()).unwrap();
                label
            };
            diag = diag.with_note(note);
        }

        self.info.elaborate(self.primary_span, diag)
    }
}

impl ParserDiag {
    fn unexpected(
        kind: UnexpectedKind,
        primary_span: Span,
        expected: impl IntoIterator<Item = &'static str>,
    ) -> Self {
        Self {
            primary_span,
            expected: expected.into_iter().collect(),
            info: ParserDiagInfo::Unexpected { kind },
        }
    }

    fn unexpected_tok(
        primary_span: Span,
        expected: impl IntoIterator<Item = &'static str>,
    ) -> Self {
        Self::unexpected(UnexpectedKind::Token, primary_span, expected)
    }

    fn unexpected_eof(
        primary_span: Span,
        expected: impl IntoIterator<Item = &'static str>,
    ) -> Self {
        Self::unexpected(UnexpectedKind::Eof, primary_span, expected)
    }

    fn early_close_paren(
        open_span: Span,
        close_span: Span,
        expected: impl IntoIterator<Item = &'static str>,
    ) -> Self {
        Self {
            primary_span: close_span,
            expected: expected.into_iter().collect(),
            info: ParserDiagInfo::EarlyCloseParen { open: open_span },
        }
    }

    fn unclosed_paren(open_span: Span, expected_close: Span) -> Self {
        Self {
            primary_span: expected_close,
            expected: vec![],
            info: ParserDiagInfo::UnclosedParen { open: open_span },
        }
    }
}
