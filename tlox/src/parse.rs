//! Parser for Lox.

use std::iter::Peekable;

use crate::diag::Diagnostic;
use crate::session::{Session, SessionKey};
use crate::span::{HasSpan, Source, Span, Spannable, Spanned};
use crate::syn::*;
use crate::tok::{Lexer, Pair, Token};

#[cfg(test)]
mod test;

mod error;
use error::*;

// pub mod redo;

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
// stmt -> compound_stmt | simple_stmt ';'
//
// compound_stmt -> if_stmt | while_stmt | block_stmt
//
// simple_stmt -> decl_stmt | print_or_expr_stmt
//
// if_stmt -> 'if' '(' expr ')' stmt ('else' stmt)?
//
// while_stmt -> 'while' '(' expr ')' stmt
//
// block_stmt -> '{' stmt* '}'
//
// decl_stmt -> 'var' IDENT ('=' expr)?
//
// print_or_expr_stmt -> 'print'? expr
//
// expr -> assign
//
// ; Right-assoc
// assign -> place '=' assign
//         | logic_or
//
// place -> IDENT
//
// ; Left-assoc
// logic_or -> logic_and ('or' logic_and)*
//
// ; Left-assoc
// logic_and -> equal ('and' equal)*
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
        debug_println!(@"=== STARTING NEW PARSE ===");
        // let res = self.program();
        // Session::with_current(|key| {
        //     if key.get().dcx.has_errors() {
        //         None
        //     } else {
        //         Some(res)
        //     }
        // })
        self.program().ok()
    }
}

impl<'s> Parser<'s> {
    /// Push a diagnostic to the stack to be emitted.
    ///
    /// Diagnostics are emitted after attempting to parse each statement, in reverse of the order in
    /// which they were pushed via this method. This causes them to appear to the user in order
    /// first of statements, and then of syntactic specificity, broader (higher in the parse tree)
    /// first.
    fn push_diag(&mut self, diag: ParserDiag<'s>) {
        self.diags.push(diag);
    }

    /// Emit all diagnostics pushed via [`push_diag`], in reverse order.
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

    /// Get the span of a spanned object, or the end-of-source span.
    fn span_or_eof<T>(&self, val: &Option<Spanned<T>>) -> Span {
        val.as_ref()
            .map(|val| val.span)
            .unwrap_or_else(|| self.end_of_source())
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
        Some(self.advance()?.map(f))
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
    /// This will advance the input stream until it reaches a token that satisfies the given `until`
    /// predicate, which is followed by a token that satisfies the given `next` predicate. When this
    /// returns, it is guaranteed that:
    ///
    /// - The most recently advanced-over token satisfies `until`, and
    /// - The next token to be advanced over will satisfy `next`.
    fn synchronize(&mut self, until: impl Fn(&Token) -> bool, next: impl Fn(&Token) -> bool) {
        while !self.is_at_end() {
            self.advance_until(&until);
            self.advance();
            if self.check_next(&next) {
                debug_println!(@"=> found sync point");
                return;
            }
        }

        debug_println!(@"=> reached EOF without finding sync point");
    }

    /// Synchronize to a statement boundary.
    ///
    /// This advances until the next occurrence of a semicolon followed by a non-operator keyword or
    /// method receiver start token.
    fn sync_to_stmt_boundary(&mut self) {
        debug_println!(@"snychronizing to stmt boundary");
        self.synchronize(
            |tok| matches!(tok, Token::Semicolon | Token::CloseBrace),
            |tok| tok.is_stmt_start(),
        );
    }

    /// Parse something enclosed by a delimiter pair.
    ///
    /// Returns the opening delimiter token, the parsed contents, and the closing delimiter token.
    fn parse_pair<T>(
        &mut self,
        pair: Pair,
        contents: impl Fn(&mut Self) -> ParserRes<'s, T>,
    ) -> ParserRes<'s, (Spanned<Token<'s>>, T, Spanned<Token<'s>>)> {
        let open = self
            .advance_or_peek(|tok| tok == &pair.open_tok())
            .map_err(|tok| {
                self.push_diag(ParserDiag::unexpected(self, tok, pair.open_tok().summary()));
                ParserError::unexpected(tok).handled()
            })?;

        let contents = contents(self).catch_deferred(|kind| match kind {
            ParserErrorKind::Unexpected(Some(tok)) if tok.node == pair.close_tok() => {
                self.push_diag(ParserDiag::early_close_pair(pair, open.span, tok.span));
                Err(kind.handled())
            }
            _ => Err(kind.deferred()),
        })?;

        let close = self
            .advance_or_peek(|tok| tok == &pair.close_tok())
            .map_err(|tok| {
                self.push_diag(ParserDiag::unclosed_pair(
                    pair,
                    open.span,
                    self.span_or_eof(&tok),
                ));
                ParserError::unexpected(tok).handled()
            })?;

        Ok((open, contents, close))
    }

    /// Parse something enclosed by parentheses.
    ///
    /// Returns the opening paren span, the parsed contents, and the closing paren span.
    fn parse_parens<T>(
        &mut self,
        contents: impl Fn(&mut Self) -> ParserRes<'s, T>,
    ) -> ParserRes<'s, (Span, T, Span)> {
        let (open, contents, close) = self.parse_pair(Pair::Parens, contents)?;
        Ok((open.span, contents, close.span))
    }

    /// Parse a program.
    ///
    /// Corresponds to the `program` grammar production.
    fn program(&mut self) -> Program<'s> {
        let mut stmts = Vec::new();
        while !self.is_at_end() {
            match self
                // .stmt_old()
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

    /// Parse a statement.
    ///
    /// Corresponds to the `stmt` grammar production.
    fn stmt_old(&mut self) -> ParserRes<'s, Spanned<Stmt<'s>>> {
        let peeked = self.peek().unwrap();
        match peeked.node {
            Token::Var => self.decl_stmt_old(),
            Token::OpenBrace => self.block_stmt(),
            Token::If => self.if_stmt(),
            Token::While => self.while_stmt(),
            tok if tok.is_stmt_start() => self.print_or_expr_stmt_old(),
            _ => {
                self.push_diag(ParserDiag::unexpected_tok(self, peeked, "statement"));
                Err(ParserError::unexpected_tok(peeked).handled())
            }
        }
        .catch_deferred(|kind| match kind {
            ParserErrorKind::Unexpected(Some(
                tok @ Spanned {
                    node: Token::Semicolon | Token::CloseBrace,
                    ..
                },
            )) => {
                self.push_diag(ParserDiag::unexpected_tok(self, tok, None));
                Err(ParserError::spurious_stmt_end().handled())
            }

            _ => Err(kind.deferred()),
        })
    }

    fn stmt(&mut self) -> ParserRes<'s, Spanned<Stmt<'s>>> {
        let peeked = self.peek().unwrap();
        let res = match peeked.node {
            Token::If | Token::While | Token::OpenBrace => self.compound_stmt(),
            _ => self.simple_stmt(),
        };

        res.or_else(|err| match err.kind() {
            ParserErrorKind::Unexpected(Some(tok))
                if matches!(tok.node, Token::Semicolon | Token::CloseBrace) =>
            {
                if err.is_deferred() {
                    if matches!(tok.node, Token::Semicolon) {
                        self.push_diag(ParserDiag::early_terminated_stmt(tok.span));
                    } else {
                        self.push_diag(ParserDiag::unexpected_tok(self, *tok, None));
                    }
                }

                Err(ParserError::spurious_stmt_end().handled())
            }
            _ => Err(err),
        })
    }

    fn simple_stmt(&mut self) -> ParserRes<'s, Spanned<Stmt<'s>>> {
        let stmt = if self.check_next(|tok| matches!(tok, Token::Var)) {
            self.decl_stmt()?
        } else {
            self.print_or_expr_stmt_old()?
        };

        match self.advance_or_peek(|tok| matches!(tok, Token::Semicolon)) {
            Ok(semi) => Ok(stmt.join_with_span(semi)),
            Err(tok) => {
                self.push_diag(ParserDiag::unterminated_stmt(
                    stmt.span,
                    self.span_or_eof(&tok),
                ));
                Err(ParserError::spurious_stmt_end().handled())
            }
        }
    }

    fn compound_stmt(&mut self) -> ParserRes<'s, Spanned<Stmt<'s>>> {
        let peeked = self.peek().unwrap();
        match peeked.node {
            Token::If => self.if_stmt(),
            Token::While => self.while_stmt(),
            Token::OpenBrace => self.block_stmt(),
            _ => {
                self.push_diag(ParserDiag::unexpected_tok(self, peeked, "statement"));
                Err(ParserError::unexpected_tok(peeked).handled())
            }
        }
    }

    /// Parse an if-else statement.
    ///
    /// This expects the next token to be `Token::If`. In debug builds, it will panic if this is not
    /// the case.
    ///
    /// This corresponds to the `if_stmt` grammar production.
    fn if_stmt(&mut self) -> ParserRes<'s, Spanned<Stmt<'s>>> {
        let if_kw = self.advance().unwrap();
        debug_assert!(matches!(if_kw.node, Token::If));

        let (_, cond, _) = self.parse_parens(Self::expr)?;

        // let body = self.stmt_old()?;
        let body = self.stmt()?;

        let (else_body, span) =
            if let Ok(_else_kw) = self.advance_or_peek(|tok| matches!(tok, Token::Else)) {
                // let else_body = self.stmt_old()?;
                let else_body = self.stmt()?;
                let span = if_kw.span.join(else_body.span);
                (Some(else_body), span)
            } else {
                (None, if_kw.span.join(body.span))
            };

        Ok(stmt::if_else(cond, body, else_body).spanned(span))
    }

    /// Parse a while statement.
    ///
    /// This expects the next token in the stream to be `Token::While`. In debug builds, it will
    /// panic if this is not the case.
    ///
    /// Corresponds to the `while_stmt` grammar production.
    fn while_stmt(&mut self) -> ParserRes<'s, Spanned<Stmt<'s>>> {
        let kw_while = self.advance().unwrap();
        debug_assert!(matches!(kw_while.node, Token::While));

        let (_, cond, _) = self.parse_parens(Self::expr)?;

        // let body = self.stmt_old()?;
        let body = self.stmt()?;
        let span = kw_while.span.join(body.span);

        Ok(stmt::while_loop(cond, body).spanned(span))
    }

    fn decl_stmt(&mut self) -> ParserRes<'s, Spanned<Stmt<'s>>> {
        let var = self.advance().unwrap();
        debug_assert!(matches!(var.node, Token::Var));

        let name = self
            .advance_or_peek(|tok| matches!(tok, Token::Ident(_)))
            .map(|tok| {
                tok.map(|node| match node {
                    Token::Ident(name) => name,
                    _ => unreachable!(),
                })
            })
            .map_err(|tok| {
                self.push_diag(ParserDiag::missing_var_name(
                    var.span,
                    self.span_or_eof(&tok),
                ));
                ParserError::unexpected(tok).handled()
            })?;

        let init = if self
            .advance_or_peek(|tok| matches!(tok, Token::Equal))
            .is_ok()
        {
            Some(self.expr()?)
        } else {
            None
        };

        let mut span = var.span;
        if let Some(init) = init.as_ref() {
            span = span.join(init.span);
        }

        Ok(stmt::decl(name, init).spanned(span))
    }

    /// Parse a variable declaration statement.
    ///
    /// This expects the next token in the stream to be `Token::Var`. In debug builds, it will panic
    /// if this is not the case.
    ///
    /// This corresponds to the `decl_stmt` grammar production.
    fn decl_stmt_old(&mut self) -> ParserRes<'s, Spanned<Stmt<'s>>> {
        let var = self.advance().unwrap();
        debug_assert!(matches!(var.node, Token::Var));

        let name = self
            .advance_or_peek(|tok| matches!(tok, Token::Ident(_)))
            .map(|tok| match tok.node {
                Token::Ident(name) => tok.with_node(name),
                _ => unreachable!(),
            })
            .map_err(|tok| {
                self.push_diag(ParserDiag::missing_var_name(
                    var.span,
                    self.span_or_eof(&tok),
                ));
                ParserError::unexpected(tok).handled()
            })?;

        let init = if self
            .advance_or_peek(|tok| matches!(tok, Token::Equal))
            .is_ok()
        {
            let expr = self.expr().catch_deferred(|err| match err {
                ParserErrorKind::Unexpected(Some(tok)) if matches!(tok.node, Token::Semicolon) => {
                    self.push_diag(ParserDiag::early_terminated_stmt(tok.span));
                    Err(ParserError::spurious_stmt_end().handled())
                }
                _ => Err(err.deferred()),
            })?;
            Some(expr)
        } else {
            None
        };

        // let semi = self
        //     .advance_or_peek(|tok| matches!(tok, Token::Semicolon))
        //     .map_err(|tok| {
        //         let expected_semi = self.span_or_eof(&tok);
        //         let stmt_span = var
        //             .span
        //             .join(init.as_ref().map(|expr| expr.span).unwrap_or(name.span));
        //         self.push_diag(ParserDiag::unterminated_stmt(stmt_span, expected_semi));
        //         ParserError::spurious_stmt_end().handled()
        //     })?;

        // let span = var.span.join(semi.span);
        let span = if let Some(init) = init.as_ref() {
            var.span.join(init.span)
        } else {
            var.span.join(name.span)
        };
        Ok(stmt::decl(name, init).spanned(span))
    }

    fn block_stmt(&mut self) -> ParserRes<'s, Spanned<Stmt<'s>>> {
        // We don't use `parse_pair` here cuz there's some intricate recovery logic. We also don't
        // use `program` here because the recovery logic is meaningfully different from what we use
        // in that node
        let obrace = self.advance().unwrap();
        debug_assert!(matches!(obrace.node, Token::OpenBrace));

        let mut stmts = Vec::new();

        while self.check_next(|tok| tok.is_stmt_start()) {
            match self
                // .stmt_old()
                .stmt()
                .catch_deferred(|kind| match kind {
                    ParserErrorKind::Unexpected(Some(tok))
                        if matches!(tok.node, Token::CloseBrace) =>
                    {
                        debug_println!(@"block_stmt: unexpected {tok:?}");
                        self.push_diag(ParserDiag::early_close_brace(obrace.span, tok.span));
                        Err(kind.handled())
                    }
                    _ => Err(kind.deferred()),
                })
                .map_err(ParserError::into_kind)
            {
                Ok(stmt) => {
                    stmts.push(stmt);
                }

                Err(ParserErrorKind::Unexpected(Some(tok)))
                    if matches!(tok.node, Token::CloseBrace) =>
                {
                    debug_println!(@"spurious block end");
                    return Err(ParserError::spurious_stmt_end().handled());
                }

                Err(ParserErrorKind::SpuriousStmtEnd) => {}

                _ => self.sync_to_stmt_boundary(),
            }
        }

        let cbrace = self
            .advance_or_peek(|tok| matches!(tok, Token::CloseBrace))
            .map_err(|tok| {
                self.push_diag(ParserDiag::unclosed_brace(
                    obrace.span,
                    self.span_or_eof(&tok),
                ));
                ParserError::spurious_stmt_end().handled()
            })?;

        Ok(stmt::block(stmts).spanned(obrace.span.join(cbrace.span)))
    }

    fn print_or_expr_stmt(&mut self) -> ParserRes<'s, Spanned<Stmt<'s>>> {
        let maybe_print = self.advance_or_peek(|tok| matches!(tok, Token::Print)).ok();

        todo!()
    }

    /// Parse a print or expression statement.
    ///
    /// Corresponds to the `print_or_expr_stmt` grammar production.
    fn print_or_expr_stmt_old(&mut self) -> ParserRes<'s, Spanned<Stmt<'s>>> {
        let maybe_print = self.advance_or_peek(|tok| matches!(tok, Token::Print)).ok();

        let expr = self.expr().catch_deferred(|kind| match kind {
            ParserErrorKind::Unexpected(Some(tok)) if matches!(tok.node, Token::Semicolon) => {
                self.push_diag(ParserDiag::early_terminated_stmt(tok.span));
                Err(ParserError::spurious_stmt_end().handled())
            }

            ParserErrorKind::Unexpected(tok) => {
                self.push_diag(ParserDiag::unexpected(self, tok, "expression"));
                Err(kind.handled())
            }

            _ => Err(kind.deferred()),
        })?;

        // let semi = self
        //     .advance_or_peek(|tok| matches!(tok, Token::Semicolon))
        //     .map_err(|tok| {
        //         let mut stmt = expr.span;
        //         if let Some(print) = &maybe_print {
        //             stmt = print.span.join(stmt);
        //         }

        //         self.push_diag(ParserDiag::unterminated_stmt(stmt, self.span_or_eof(&tok)));
        //         ParserError::spurious_stmt_end().handled()
        //     })?;

        if let Some(print) = maybe_print {
            let span = print.span.join(expr.span);
            Ok(stmt::print(expr).spanned(span))
        } else {
            // let span = expr.span.join(semi.span);
            let span = expr.span;
            Ok(stmt::expr(expr).spanned(span))
        }
    }

    /// Parse an expression.
    ///
    /// Corresponds to the `expr` grammar production.
    fn expr(&mut self) -> ParserRes<'s, Spanned<Expr<'s>>> {
        self.assign()
    }

    /// Parse a variable assignment or binop chain.
    ///
    /// Corresponds to the `assign` grammar production.
    fn assign(&mut self) -> ParserRes<'s, Spanned<Expr<'s>>> {
        let maybe_place = self.logic_or()?;

        if let Ok(eq) = self.advance_or_peek(|tok| matches!(tok, Token::Equal)) {
            match maybe_place.node.into_place() {
                Ok(place) => {
                    let val = self.assign()?;
                    Ok(expr::assign(place.spanned(maybe_place.span), val))
                }
                Err(_) => {
                    self.push_diag(ParserDiag::invalid_place_expr(maybe_place.span, eq.span));
                    Err(ParserError::invalid_place_expr().handled())
                }
            }
        } else {
            Ok(maybe_place)
        }
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

    /// Parse a boolean `or` chain.
    ///
    /// Corresponds to the `logic_or` grammar production.
    fn logic_or(&mut self) -> ParserRes<'s, Spanned<Expr<'s>>> {
        self.binop_chain_left_assoc(
            Self::logic_and,
            |tok| matches!(tok, Token::Or),
            |_| BinopSym::Bool(BooleanBinopSym::Or),
        )
    }

    /// Parse a boolean `and` chain.
    ///
    /// Corresponds to the `logic_and` grammar production.
    fn logic_and(&mut self) -> ParserRes<'s, Spanned<Expr<'s>>> {
        self.binop_chain_left_assoc(
            Self::equal,
            |tok| matches!(tok, Token::And),
            |_| BinopSym::Bool(BooleanBinopSym::And),
        )
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
        if let Some(tok) = self.advance() {
            match tok.node {
                Token::Number(n) => Ok(tok.with_node(expr::literal(Lit::Num(n)))),
                Token::Str(s) => Ok(tok.with_node(expr::literal(Lit::Str(s)))),
                Token::Boolean(b) => Ok(tok.with_node(expr::literal(Lit::Bool(b)))),
                Token::Nil => Ok(tok.with_node(expr::literal(Lit::Nil))),
                Token::Ident(name) => Ok(tok.with_node(expr::var(name))),
                Token::OpenParen => self.group(tok.span),

                // Error productions

                // Potential spurious ends of larger syntactic constructs:
                Token::CloseParen | Token::CloseBrace | Token::Semicolon => {
                    Err(ParserError::unexpected_tok(tok).deferred())
                }

                // Other unexpected tokens
                _ => {
                    self.push_diag(ParserDiag::unexpected_tok(self, tok, "expression"));
                    Err(ParserError::unexpected_tok(tok).handled())
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
            ParserErrorKind::Unexpected(Some(tok)) if matches!(tok.node, Token::CloseParen) => {
                self.push_diag(ParserDiag::early_close_paren(oparen_span, tok.span));
                Err(kind.handled())
            }
            _ => Err(kind.deferred()),
        })?;

        let cparen_span = self
            .advance_or_peek(|tok| matches!(tok, Token::CloseParen))
            .map(|tok| tok.span)
            .map_err(|tok| {
                self.push_diag(ParserDiag::unclosed_paren(
                    oparen_span,
                    self.span_or_eof(&tok),
                ));
                ParserError::unexpected(tok).handled()
            })?;

        let span = oparen_span.join(cparen_span);
        Ok(expr::group(expr).spanned(span))
    }
}
