//! Parser for Lox.

use std::iter::Peekable;

use crate::diag::Diagnostic;
use crate::session::{Session, SessionKey};
use crate::span::{Source, Span, Spannable, Spanned};
use crate::syn::*;
use crate::tok::{Lexer, Token};

#[cfg(test)]
mod test;

mod error;
use error::*;

/// Scan and parse the source with the given index in the current session's source map.
pub fn parse_source(key: SessionKey, source_idx: usize) -> Option<Program> {
    let lexer = Lexer::new(key, key.get().sm.source(source_idx));
    let parser = Parser::new(lexer);
    parser.parse()
}

/// Parser for Lox.
#[derive(Debug)]
pub struct Parser<'s> {
    lexer: Peekable<Lexer<'s>>,
    source: Source<'s>,
    diags: Vec<ParserDiag<'s>>,
}

// Grammar:
//
// program -> stmt* EOF
//
// stmt -> expr_stmt | print_stmt
//
// expr_stmt -> expr ';'
//
// print_stmt -> 'print' expr ';'
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

impl<'s> Parser<'s> {
    /// Create a new parser, using the given lexer.
    pub fn new(lexer: Lexer<'s>) -> Self {
        let source = lexer.source();
        Self {
            lexer: lexer.peekable(),
            source,
            diags: Vec::new(),
        }
    }

    /// Parse a Lox syntax tree from the parser's token stream.
    ///
    /// Returns `None` if the parser encounters syntax errors. Any such errors will have been
    /// emitted to the global session's diagnostic context.
    pub fn parse(mut self) -> Option<Program<'s>> {
        debug_println!("=== STARTING NEW PARSE ===");
        let res = self.program();
        Session::with_current(|key| {
            if key.get().dcx.has_errors() {
                None
            } else {
                Some(res)
            }
        })
    }
}

impl<'s> Parser<'s> {
    const ATOM_STARTS: [&'static str; 6] =
        ["number", "string", "`true`", "`false`", "`nil`", "`(`"];

    fn push_diag(&mut self, diag: ParserDiag<'s>) {
        self.diags.push(diag);
    }

    fn emit_diags(&mut self) {
        for diag in self.diags.drain(..).rev() {
            diag.emit();
        }
    }

    /// Get the one-character span representing the end of the source being parsed.
    fn end_of_source(&self) -> Span {
        let source = self.source.span();
        source.subspan(source.len() - 1..).unwrap()
    }

    /// Is the parser at the end of input?
    fn is_at_end(&mut self) -> bool {
        self.peek().is_none()
    }

    /// Peek at the next token in the stream without advancing.
    fn peek(&mut self) -> Option<Spanned<Token<'s>>> {
        self.lexer.peek().copied()
    }

    /// Advance the token stream, returning the advanced-over token.
    fn advance(&mut self) -> Option<Spanned<Token<'s>>> {
        self.lexer.next()
    }

    /// Advance the token stream, applying the given function to the advanced-over token.
    fn advance_map<T>(&mut self, f: impl FnOnce(Token) -> T) -> Option<Spanned<T>> {
        let tok = self.advance()?;
        Some(f(tok.node).spanned(tok.span))
    }

    /// Test the next token in the stream, without advancing.
    ///
    /// Returns true (a) there is a next token in the stream and (b) it passes the given test.
    /// Returns false if the next token fails or the stream is at EOF.
    fn check_next(&mut self, test: impl FnOnce(&Token) -> bool) -> bool {
        self.peek().map(|tok| test(&tok.node)).unwrap_or_default()
    }

    /// Test the next token in the stream, advancing over it if the test succeeds and peeking
    /// otherwise.
    ///
    /// Returns `Ok` if the test passed and the token was advanced over. Otherwise, returns the
    /// peeked-at token (or `None` if the parser is at the end of input) as an `Err`.
    fn advance_or_peek(
        &mut self,
        test: impl FnOnce(&Token) -> bool,
    ) -> Result<Spanned<Token<'s>>, Option<Spanned<Token<'s>>>> {
        if self.check_next(test) {
            Ok(self.advance().unwrap())
        } else {
            Err(self.peek())
        }
    }

    /// Advance over as many tokens as pass the given test.
    ///
    /// When this returns, it is guaranteed that either (a) the token stream is at EOF or (b) the
    /// next token fails the given test.
    fn advance_while(&mut self, test: impl Fn(&Token) -> bool) {
        while self.advance_or_peek(&test).is_ok() {}
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
        while !self.is_at_end() {
            self.advance_until(&until);
            if self.check_next(&next) {
                break;
            }

            self.advance();
        }
    }

    /// Synchronize to a statement boundary.
    ///
    /// This advances until the next occurrence of a semicolon followed by a non-operator keyword or
    /// method receiver start token.
    fn sync_to_stmt_boundary(&mut self) {
        self.synchronize(
            |tok| matches!(tok, Token::Semicolon),
            |tok| tok.is_stmt_start(),
        );
    }

    fn program(&mut self) -> Program<'s> {
        let mut stmts = Vec::new();
        while !self.is_at_end() {
            match self
                .stmt()
                .catch_deferred(|kind| panic!("uncaught deferred parser error {kind:?}"))
                .map_err(ParserError::into_kind)
            {
                Ok(stmt) => {
                    stmts.push(stmt);
                }

                Err(ParserErrorKind::SpuriousStmtEnd) => {}

                _ => {
                    self.sync_to_stmt_boundary();
                }
            }

            self.emit_diags();
        }

        Program { stmts }
    }

    fn stmt(&mut self) -> ParserRes<'s, Spanned<Stmt<'s>>> {
        debug_println!("parsing stmt");
        let maybe_print = self.advance_or_peek(|tok| matches!(tok, Token::Print)).ok();
        debug_println!("=> maybe print? {maybe_print:?}");

        let expr = self.expr().catch_deferred(|kind| match kind {
            ParserErrorKind::Unexpected(Some(Spanned {
                node: Token::Semicolon,
                span,
            })) => {
                self.push_diag(ParserDiag::early_terminated_stmt(span));
                Err(ParserError::spurious_stmt_end().handled())
            }

            ParserErrorKind::Unexpected(tok) => {
                self.push_diag(ParserDiag::unexpected(self, tok, Self::ATOM_STARTS));
                Err(kind.handled())
            }

            _ => Err(kind.deferred()),
        })?;

        let semi = self
            .advance_or_peek(|tok| matches!(tok, Token::Semicolon))
            .map_err(|tok| {
                debug_println!("=> no semicolon at end of stmt");
                let mut stmt = expr.span;
                if let Some(print) = &maybe_print {
                    stmt = print.span.join(stmt);
                }

                let expected_semi = tok
                    .map(|tok| tok.span)
                    .unwrap_or_else(|| self.end_of_source());

                self.push_diag(ParserDiag::unterminated_stmt(stmt, expected_semi));
                ParserError::spurious_stmt_end().handled()
            })?;

        if let Some(print) = maybe_print {
            let span = print.span.join(semi.span);
            Ok(Stmt::Print { val: expr }.spanned(span))
        } else {
            let span = expr.span.join(semi.span);
            Ok(Stmt::Expr { val: expr }.spanned(span))
        }
    }

    /// Parse an expression.
    ///
    /// Corresponds to the `expr` grammar production.
    fn expr(&mut self) -> ParserRes<'s, Spanned<Expr<'s>>> {
        // debug_println!("parsing expression");
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
        operand: impl Fn(&mut Self) -> ParserRes<'s, Spanned<Expr<'s>>>,
        sym_test: impl Fn(&Token) -> bool,
        sym_map: impl Fn(Token) -> BinopSym,
    ) -> ParserRes<'s, Spanned<Expr<'s>>> {
        let mut accum = operand(self)?;
        while self.check_next(&sym_test) {
            let sym = self.advance_map(&sym_map).unwrap();
            let rhs = operand(self)?;
            accum = expr::binop(sym, accum, rhs);
        }

        Ok(accum)
    }

    /// Parse an equality operator chain.
    ///
    /// Corresponds to the `equal` grammar production.
    fn equal(&mut self) -> ParserRes<'s, Spanned<Expr<'s>>> {
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
    fn comp(&mut self) -> ParserRes<'s, Spanned<Expr<'s>>> {
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
    fn terms(&mut self) -> ParserRes<'s, Spanned<Expr<'s>>> {
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
    fn factors(&mut self) -> ParserRes<'s, Spanned<Expr<'s>>> {
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
    fn unary(&mut self) -> ParserRes<'s, Spanned<Expr<'s>>> {
        if self.check_next(|tok| matches!(tok, Token::Minus | Token::Bang)) {
            let sym = self
                .advance_map(|tok| match tok {
                    Token::Minus => UnopSym::Neg,
                    Token::Bang => UnopSym::Not,
                    _ => unreachable!(),
                })
                .unwrap();

            let operand = self.unary()?;

            Ok(expr::unop(sym, operand))
        } else {
            self.atom()
        }
    }

    /// Parse an atomic (literal/identifier/parenthesized) expression.
    ///
    /// Corresponds to the `atom` grammar production.
    fn atom(&mut self) -> ParserRes<'s, Spanned<Expr<'s>>> {
        debug_println!("parsing atom");
        if let Some(spanned @ Spanned { node: tok, span }) = self.advance() {
            match tok {
                Token::Number(n) => Ok(expr::literal(Lit::Num(n)).spanned(span)),
                Token::Str(s) => Ok(expr::literal(Lit::Str(s)).spanned(span)),
                Token::Boolean(b) => Ok(expr::literal(Lit::Bool(b)).spanned(span)),
                Token::Nil => Ok(expr::literal(Lit::Nil).spanned(span)),
                Token::LeftParen => self.group(span),

                // Error productions
                Token::RightParen | Token::Semicolon => {
                    Err(ParserError::unexpected_tok(spanned).deferred())
                }

                _ => {
                    self.push_diag(ParserDiag::unexpected_tok(self, spanned, Self::ATOM_STARTS));
                    Err(ParserError::unexpected_tok(spanned).handled())
                }
            }
        } else {
            Err(ParserError::eof().deferred())
        }
    }

    /// Parse a parenthesized expression.
    ///
    /// Assumes that the opening parenthesis has already been advanced over. Uses the given span as
    /// the span for the opening paren, for diagnostic reporting.
    ///
    /// Corresponds to the parenthesized expression arm of the `atom` grammar production.
    fn group(&mut self, oparen_span: Span) -> ParserRes<'s, Spanned<Expr<'s>>> {
        let expr = self.expr().catch_deferred(|kind| match kind {
            // ParserErrorKind::SpuriousCloseParen { close } => {
            //     self.push_diag(ParserDiag::early_close_paren(
            //         oparen_span,
            //         close,
            //         Self::ATOM_STARTS,
            //     ));
            //     Err(kind.handled())
            // }
            ParserErrorKind::Unexpected(Some(Spanned {
                node: Token::RightParen,
                span,
            })) => {
                self.push_diag(ParserDiag::early_close_paren(oparen_span, span));
                Err(kind.handled())
            }
            _ => Err(kind.deferred()),
        })?;

        let cparen_span = self
            .advance_or_peek(|tok| matches!(tok, Token::RightParen))
            .map(|tok| tok.span)
            .map_err(|tok| {
                let expected = tok
                    .map(|tok| tok.span)
                    .unwrap_or_else(|| self.end_of_source());
                self.push_diag(ParserDiag::unclosed_paren(oparen_span, expected));
                ParserError::unexpected(tok).handled()
            })?;

        Ok(expr.node.spanned(oparen_span.join(cparen_span)))
    }
}
