//! Parser for Lox.

use std::iter::Peekable;

use crate::diag::{Diag, DiagKind, Diagnostic};
use crate::intern::Interned;
use crate::session::Session;
use crate::span::{Source, Span, Spannable, Spanned};
use crate::syn::*;
use crate::tok::{Lexer, Token};
use crate::util::oxford_or;

#[cfg(test)]
mod test;

/// Scan and parse the source with the given index in the current session's source map.
pub fn parse_source(source_idx: usize) -> Option<Spanned<Interned<Expr>>> {
    Session::with_current(|sess| {
        let lexer = Lexer::new(sess.sm.source(source_idx));
        let parser = Parser::new(lexer);
        parser.parse()
    })
}

/// Parser for Lox.
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
    /// Create a new parser, using the given lexer.
    pub fn new(lexer: Lexer<'sm>) -> Self {
        let source = lexer.source();
        Self {
            lexer: lexer.peekable(),
            source,
        }
    }

    /// Parse a Lox syntax tree from the parser's token stream.
    ///
    /// Returns `None` if the parser encounters syntax errors. Any such errors will have been
    /// emitted to the global session's diagnostic context.
    pub fn parse(mut self) -> Option<Spanned<Interned<Expr>>> {
        let res = self.expr().ok()?;
        Session::with_current(|sess| {
            if sess.dcx.has_errors() {
                None
            } else {
                Some(res)
            }
        })
    }
}

/// Control flow and error recovery in the parser is mediated via these Results.
///
/// The errors that are actually reported to the user go through the diagnostic context instead.
type ParserRes<T> = Result<T, ParserError>;

#[derive(Debug, Clone, Copy)]
enum ParserError {
    /// Raised when encountering an unexpected close paren. Diagnostic should not be immediately
    /// emitted in this case, but rather left to the code catching it, to allow for more precise
    /// diagnostics.
    ///
    /// For instance, the cases where a close paren appears appropos of nothing should get a
    /// different diagnostic than the case where an otherwise-correct set of parentheses is closed
    /// before its contained expression is complete.
    ///
    /// This error should usually be propagated up to the nearest containing atom node of the parse
    /// tree in order to enable accurate error recovery, but intervening nodes may be able to
    /// report more precise diagnostics; hence, this error carries a flag indicating whether the
    /// spurious paren has already been reported.
    SpuriousCloseParen {
        close: Span,
        reported: bool,
    },

    /// Thrown when encountering an unexpected binary operator.
    ///
    /// Carries the binding level of the operator, to allow catching and recovering at the
    /// appropriate level of the parse tree.
    LoneBinop {
        location: Span,
        level: BinopLevel,
    },

    Eof,
    Other,
}

/// Binary operator precedence levels.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BinopLevel {
    Logic,
    Eq,
    Comp,
    Add,
    Mul,
}

impl BinopLevel {
    fn from_tok(tok: &Token) -> Self {
        match tok {
            Token::And | Token::Or => Self::Logic,
            Token::EqualEqual | Token::BangEqual => Self::Eq,
            Token::Less | Token::LessEqual | Token::Greater | Token::GreaterEqual => Self::Comp,
            Token::Plus | Token::Minus => Self::Add,
            Token::Star | Token::Slash | Token::Percent => Self::Mul,
            _ => panic!("not a binop token"),
        }
    }
}

impl Parser<'_> {
    const ATOM_STARTS: [&'static str; 6] =
        ["number", "string", "`true`", "`false`", "`nil`", "`(`"];

    /// Get the span associated with the given error, if any.
    fn err_span(&self, err: &ParserError) -> Option<Span> {
        match err {
            ParserError::SpuriousCloseParen { close, .. } => Some(*close),
            ParserError::LoneBinop { location, .. } => Some(*location),
            ParserError::Eof => Some(self.end_of_source()),
            ParserError::Other => None,
        }
    }

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
    fn expr(&mut self) -> ParserRes<Spanned<Interned<Expr>>> {
        debug_println!(@"= Parsing expression");
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
        level: BinopLevel,
        operand: impl Fn(&mut Self) -> ParserRes<Spanned<Interned<Expr>>>,
        sym_test: impl Fn(&Token) -> bool,
        sym_map: impl Fn(Token) -> BinopSym,
    ) -> ParserRes<Spanned<Interned<Expr>>> {
        let mut lhs = match operand(self) {
            Ok(expr) => expr,

            // Missing LHS: attempt to parse RHS, emit error, return dummy expr
            Err(ParserError::LoneBinop {
                level: lv,
                location,
            }) if lv == level => {
                let rhs = operand(self)
                    .map(|expr| expr.span)
                    .or_else(|err| self.err_span(&err).ok_or(()))
                    .ok();

                ParserDiag::missing_lhs(location, rhs).emit();

                let dummy_span = if let Some(rhs) = rhs {
                    location.join(rhs)
                } else {
                    location
                };

                Expr::literal(Lit::Nil).spanned(dummy_span)
            }
            other => return other,
        };

        while self.check_next(&sym_test) {
            let sym = self.advance_map(&sym_map).unwrap();
            match operand(self) {
                Ok(rhs) => {
                    lhs = Expr::binop(sym, lhs, rhs);
                }

                Err(ParserError::SpuriousCloseParen { close, .. }) => {
                    ParserDiag::missing_rhs(lhs.span, sym.span, close).emit();
                    return Err(ParserError::SpuriousCloseParen {
                        close,
                        reported: true,
                    });
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
    fn equal(&mut self) -> ParserRes<Spanned<Interned<Expr>>> {
        self.binop_chain_left_assoc(
            BinopLevel::Eq,
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
    fn comp(&mut self) -> ParserRes<Spanned<Interned<Expr>>> {
        self.binop_chain_left_assoc(
            BinopLevel::Comp,
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
    fn terms(&mut self) -> ParserRes<Spanned<Interned<Expr>>> {
        self.binop_chain_left_assoc(
            BinopLevel::Add,
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
    fn factors(&mut self) -> ParserRes<Spanned<Interned<Expr>>> {
        self.binop_chain_left_assoc(
            BinopLevel::Mul,
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
    fn unary(&mut self) -> ParserRes<Spanned<Interned<Expr>>> {
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
    fn atom(&mut self) -> ParserRes<Spanned<Interned<Expr>>> {
        if let Some(Spanned { node: tok, span }) = self.advance() {
            match tok {
                Token::Number(n) => Ok(Expr::literal(Lit::Num(n)).spanned(span)),
                Token::Str(s) => Ok(Expr::literal(Lit::Str(s)).spanned(span)),
                Token::Boolean(b) => Ok(Expr::literal(Lit::Bool(b)).spanned(span)),
                Token::Nil => Ok(Expr::literal(Lit::Nil).spanned(span)),
                Token::LeftParen => self.group(span),

                // Error productions
                Token::RightParen => Err(ParserError::SpuriousCloseParen {
                    close: span,
                    reported: false,
                }),

                tok if tok.is_binop() => {
                    let level = BinopLevel::from_tok(&tok);
                    Err(ParserError::LoneBinop {
                        level,
                        location: span,
                    })
                }

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
    fn group(&mut self, oparen_span: Span) -> ParserRes<Spanned<Interned<Expr>>> {
        let expr = match self.expr() {
            Ok(expr) => expr,
            Err(ParserError::SpuriousCloseParen { close, reported }) => {
                if !reported {
                    ParserDiag::early_close_paren(oparen_span, close, Self::ATOM_STARTS).emit();
                }
                // Close the group and return a dummy expression to allow checking for further
                // errors in this expression
                let dummy_span = oparen_span.join(close);
                return Ok(Expr::literal(Lit::Nil).spanned(dummy_span));
            }
            other => return other,
        };

        let cparen_span = match self.advance_test(|tok| matches!(tok, Token::RightParen)) {
            Ok(tok) => tok.span,
            Err(maybe_tok) => {
                let span = if let Some(tok) = maybe_tok {
                    tok.span
                } else {
                    self.end_of_source()
                };

                ParserDiag::unclosed_paren(oparen_span, span).emit();
                return Err(ParserError::Other);
            }
        };

        Ok(expr.node.spanned(oparen_span.join(cparen_span)))
    }
}

enum ParserDiag {
    Unexpected {
        kind: UnexpectedKind,
        location: Span,
        expected: Vec<&'static str>,
    },

    EarlyCloseParen {
        open: Span,
        close: Span,
        expected: Vec<&'static str>,
    },

    UnclosedParen {
        open: Span,
        expected_close: Span,
    },

    MissingLhs {
        operator: Span,
        rhs: Option<Span>,
    },

    MissingRhs {
        lhs: Span,
        operator: Span,
        expected_rhs: Span,
    },
}

impl ParserDiag {
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
            Self::MissingLhs { .. } => "binary operator without left-hand operand",
            Self::MissingRhs { .. } => "binary operator without right-hand operand",
        }
    }

    fn elaborate(self, mut diag: Diag) -> Diag {
        match self {
            Self::Unexpected {
                location,
                expected,
                kind,
            } => {
                if !expected.is_empty() {
                    diag = diag.with_note(format!("expected {}", oxford_or(&expected)));
                }

                match kind {
                    UnexpectedKind::Token => diag.with_primary(location, "unexpected token"),
                    UnexpectedKind::Eof => diag.with_primary(location, "unexpected end of input"),
                }
            }

            Self::EarlyCloseParen {
                open,
                close,
                expected,
            } => {
                if !expected.is_empty() {
                    diag = diag.with_note(format!("expected {}", oxford_or(&expected)));
                }
                diag.with_secondary(open, "parentheses opened here")
                    .with_primary(close, "parentheses closed here, prematurely")
            }

            Self::UnclosedParen {
                open,
                expected_close,
            } => diag
                .with_primary(expected_close, "parentheses should have been closed")
                .with_secondary(open, "parentheses opened here")
                .with_note("expected `)`"),

            Self::MissingLhs { rhs, operator } => if let Some(rhs) = rhs {
                diag.with_primary(
                    operator.join(rhs),
                    "this expression is missing the left-hand operand",
                )
            } else {
                diag.with_primary(operator, "expected left-hand operand for this operator")
            }
            .with_note(format!("expected {}", oxford_or(&Parser::ATOM_STARTS))),

            Self::MissingRhs {
                operator,
                lhs,
                expected_rhs,
            } => diag
                .with_primary(expected_rhs, "expected right-hand operand here")
                .with_secondary(
                    operator.join(lhs),
                    "this expression is missing the right-hand operand",
                )
                .with_note(format!("expected {}", oxford_or(&Parser::ATOM_STARTS))),
        }
    }
}

impl Diagnostic for ParserDiag {
    fn into_diag(self) -> Diag {
        let message = self.message();
        self.elaborate(Diag::new(DiagKind::Error, message))
    }
}

enum UnexpectedKind {
    Token,
    Eof,
}

impl ParserDiag {
    fn unexpected(
        kind: UnexpectedKind,
        location: Span,
        expected: impl IntoIterator<Item = &'static str>,
    ) -> Self {
        Self::Unexpected {
            kind,
            location,
            expected: expected.into_iter().collect(),
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
        Self::EarlyCloseParen {
            open: open_span,
            close: close_span,
            expected: expected.into_iter().collect(),
        }
    }

    fn unclosed_paren(open_span: Span, expected_close: Span) -> Self {
        Self::UnclosedParen {
            open: open_span,
            expected_close,
        }
    }

    fn missing_lhs(operator: Span, rhs: Option<Span>) -> Self {
        Self::MissingLhs { operator, rhs }
    }

    fn missing_rhs(lhs: Span, operator: Span, expected_rhs: Span) -> Self {
        Self::MissingRhs {
            operator,
            lhs,
            expected_rhs,
        }
    }
}
