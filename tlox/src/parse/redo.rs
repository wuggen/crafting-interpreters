use super::{BinopSym, Lit, Parser, ParserDiag, ParserRes, UnopSym};
use crate::diag::Diagnostic;
use crate::parse::{ParserError, ParserErrorKind, ParserResExt};
use crate::span::{HasSpan, Span, Spannable, Spanned};
use crate::syn::{expr, stmt, Expr, Program, Stmt};
use crate::tok::{Pair, Token};

// => Emit: errors that should be detected by this production (not sub-productions) and immediately
//    emitted
// => Catch: errors that might be deferred by sub-productions that should be emitted by this
//    production
// => Defer: errors that should be detected by this production and deferred to higher productions
// => Outer sync: strategy for syncing after a failed instance of this production in a sequence
//    (defaults to none, propagate error immediately)
// => Inner sync: strategy for syncing after a failed sub-production (defaults to none, propagate
//    error immediately)
//
// ---
//
// open(PAREN) -> '('
// open(BRACE) -> '{'
// close(PAREN) -> ')'
// close(BRACE) -> '}'
//
// pair(kind, production) -> open(kind) production close(kind)
//  => ty_of(production)
//  => Emit missing opening/closing errors
//  => Catch early closing errors
//  => Inner sync to close(kind)
//
// seq(production) -> production*
//  => Inner sync according production's outer sync
//
// program -> stmts EOF
//  => Catch all (panic)
//
// stmts -> seq(stmt)
//
// stmt -> if_stmt | while_stmt | block_stmt | simple_stmt
//  => Outer sync stmt boundary
//
// simple_stmt -> (decl_stmt | print_or_expr_stmt) ';'
//  => Emit missing semicolon errors
//  => Catch early semicolon errors
//
// if_stmt -> 'if' pair(PAREN, expr) stmt ( 'else' stmt )?
//
// while_stmt -> 'while' pair(PAREN, expr) stmt
//
// block_stmt -> pair(BRACE, stmts)
//
// decl_stmt -> 'var' IDENT ('=' expr)?
//  => syn::Stmt (span missing semicolon)
//  => Emit missing keyword/punctuation errors
//
// print_or_expr_stmt -> 'print'? expr
//  => syn::Stmt (span missing semicolon)
//
// expr -> assign
//
// ; Right-assoc
// assign -> place '=' assign | logic_or
//  => Emit invalid place expr errors
//
// place -> IDENT
//
// left_assoc(opd, op) -> opd seq(left_assoc_rest(opd, op))
// left_assoc_rest(opd, op) -> op opd
//
// logic_or -> left_assoc(logic_and, 'or')
//
// logic_and -> left_assoc(equal, 'and')
//
// equal -> left_assoc(comp, '!=' | '==')
//
// comp -> left_assoc(terms, '<' | '<=' | '>' | '>=')
//
// terms -> left_assoc(factors, '+' | '-')
//
// factors -> left_assoc(unary, '*' | '/' | '%')
//
// unary -> ('-' | '!') unary | atom
//
// atom -> NUMBER | STRING | IDENT | 'true' | 'false' | 'nil' | pair(PAREN, expr)
//  => Emit non-deferred unexpected tokens
//  => Defer unexpected semicolon and close delimiter tokens

/// Utility and token stream manipulation methods.
impl<'s> Parser<'s> {
    pub(super) fn push_diag(&mut self, diag: ParserDiag<'s>) {
        self.diags.push(diag);
    }

    pub(super) fn emit_diags(&mut self) {
        for diag in self.diags.drain(..).rev() {
            diag.emit();
        }
    }

    pub(super) fn end_of_source(&self) -> Span {
        self.source.span().collapse_to_end()
    }

    pub(super) fn span_or_eof<S: HasSpan>(&self, val: &Option<S>) -> Span {
        val.as_ref()
            .map(|val| val.span())
            .unwrap_or_else(|| self.end_of_source())
    }

    pub(super) fn is_at_end(&mut self) -> bool {
        self.peek().is_none()
    }

    pub(super) fn peek(&mut self) -> Option<Spanned<Token<'s>>> {
        self.lexer.peek().copied()
    }

    pub(super) fn advance(&mut self) -> Option<Spanned<Token<'s>>> {
        self.lexer.next()
    }

    pub(super) fn advance_map<T>(&mut self, f: impl FnOnce(Token) -> T) -> Option<Spanned<T>> {
        Some(self.advance()?.map(f))
    }

    pub(super) fn check_next(&mut self, test: impl FnOnce(Option<Token<'s>>) -> bool) -> bool {
        test(self.peek().map(|tok| tok.node))
    }

    pub(super) fn check_next_some(&mut self, test: impl FnOnce(Token<'s>) -> bool) -> bool {
        self.check_next(|tok| tok.is_some_and(test))
    }

    pub(super) fn advance_or_peek(
        &mut self,
        test: impl FnOnce(Token) -> bool,
    ) -> Result<Spanned<Token<'s>>, Option<Spanned<Token<'s>>>> {
        if self.check_next_some(test) {
            Ok(self.advance().unwrap())
        } else {
            Err(self.peek())
        }
    }

    pub(super) fn advance_map_or_peek<T>(
        &mut self,
        f: impl FnOnce(&Token<'s>) -> Option<T>,
    ) -> Result<Spanned<T>, Option<Spanned<Token<'s>>>> {
        let peeked = self.peek();
        peeked
            .as_ref()
            .and_then(|tok| {
                f(&tok.node).map(|res| {
                    self.advance().unwrap();
                    res.spanned(tok.span)
                })
            })
            .ok_or(peeked)
    }

    pub(super) fn advance_while(&mut self, test: impl Fn(Token) -> bool) {
        while self.advance_or_peek(&test).is_ok() {}
    }

    pub(super) fn advance_until(&mut self, test: impl Fn(Token) -> bool) {
        self.advance_while(move |tok| !test(tok));
    }

    pub(super) fn sync(&mut self, until: impl Fn(Token) -> bool, after: impl Fn(Token) -> bool) {
        while !self.is_at_end() {
            self.advance_until(&until);
            self.advance();
            if self.check_next_some(&after) {
                break;
            }
        }
    }

    pub(super) fn sync_to_pair_close(&mut self, kind: Pair) {
        self.sync(|tok| tok == kind.close_tok(), |_| true);
    }

    pub(super) fn sync_to_stmt_boundary(&mut self) {
        self.sync(
            |tok| matches!(tok, Token::Semicolon | Token::CloseBrace),
            |tok| tok.is_stmt_start(),
        )
    }

    pub(super) fn pair<T>(
        &mut self,
        kind: Pair,
        inner: impl FnOnce(&mut Self) -> ParserRes<'s, T>,
    ) -> ParserRes<'s, (Spanned<Token<'s>>, T, Spanned<Token<'s>>)> {
        let open = self
            .advance_or_peek(|tok| tok == kind.open_tok())
            .map_err(|tok| {
                self.push_diag(ParserDiag::unexpected(self, tok, kind.open_tok().summary()));
                ParserError::unexpected(tok).handled()
            })?;

        let inner = inner(self).inspect_err(|err| match err.kind() {
            ParserErrorKind::Unexpected(Some(tok))
                if err.is_deferred() && tok.node.is_pair_close() =>
            {
                if tok.node == kind.close_tok() {
                    self.push_diag(ParserDiag::early_close_pair(kind, open.span, tok.span));
                } else {
                    self.push_diag(ParserDiag::mismatched_close(
                        kind,
                        tok.node.pair().unwrap(),
                        open.span,
                        tok.span,
                    ));
                }
            }
            _ => {
                self.sync_to_pair_close(kind);
            }
        })?;

        let close = self
            .advance_or_peek(|tok| tok == kind.close_tok())
            .map_err(|tok| {
                if let Some((close_span, close_kind)) = tok
                    .as_ref()
                    .and_then(|tok| Some((tok.span, tok.node.pair()?)))
                {
                    self.push_diag(ParserDiag::mismatched_close(
                        kind, close_kind, open.span, close_span,
                    ));
                } else {
                    self.push_diag(ParserDiag::unclosed_pair(
                        kind,
                        open.span,
                        self.span_or_eof(&tok),
                    ));
                }

                ParserError::unexpected(tok).handled()
            })?;

        Ok((open, inner, close))
    }

    pub(super) fn seq<'a, T>(
        &mut self,
        check: impl Fn(Option<Token<'s>>) -> bool,
        inner: impl Fn(&mut Self) -> ParserRes<'s, T>,
        sync: impl Fn(&mut Self, ParserError<'s>) -> ParserRes<'s, ()>,
    ) -> ParserRes<'s, Vec<T>> {
        let mut results: ParserRes<'s, Vec<_>> = Ok(Vec::new());

        while self.check_next(&check) {
            match inner(self) {
                Ok(item) => {
                    results.as_mut().map(|res| res.push(item)).ok();
                }

                Err(err) => {
                    results = Err(ParserError::interrupted_seq().handled());
                    if let Err(err) = sync(self, err) {
                        return Err(err);
                    }
                }
            }
        }

        results
    }

    pub(super) fn left_assoc(
        &mut self,
        opd: impl Fn(&mut Self) -> ParserRes<'s, Spanned<Expr<'s>>>,
        op: impl Fn(Token<'s>) -> bool,
    ) -> ParserRes<'s, Spanned<Expr<'s>>> {
        let first = opd(self)?;
        let rest = self.seq(
            |tok| tok.is_some_and(&op),
            |this| {
                let op = this
                    .advance()
                    .unwrap()
                    .map(|tok| BinopSym::from_tok(&tok).unwrap());
                let opd = opd(this)?;
                Ok((op, opd))
            },
            |_, err| Err(err),
        )?;
        Ok(rest
            .into_iter()
            .fold(first, |lhs, (sym, rhs)| expr::binop(sym, lhs, rhs)))
    }
}

/// Grammar implementation.
impl<'s> Parser<'s> {
    pub(super) fn program(&mut self) -> ParserRes<Program<'s>> {
        let stmts = self
            .stmts(true)
            .catch_deferred(|err| panic!("uncaught deferred parser error at top level: {err:?}"))?;
        Ok(Program { stmts })
    }

    pub(super) fn stmts(
        &mut self,
        top_level: bool,
    ) -> ParserRes<'s, Vec<Spanned<Stmt<'s>>>> {
        self.seq(
            if top_level {
                |tok: Option<Token<'_>>| tok.is_some()
            } else {
                |tok: Option<Token<'_>>| tok.is_some_and(|tok| tok.is_stmt_start())
            },
            |this| {
                let res = this.stmt();
                this.emit_diags();
                res
            },
            |this, err| {
                if !matches!(err.kind(), ParserErrorKind::SpuriousStmtEnd) {
                    this.sync_to_stmt_boundary();
                }
                if top_level && err.is_deferred() {
                    Err(err)
                } else {
                    Ok(())
                }
            },
        )
    }

    pub(super) fn stmt(&mut self) -> ParserRes<'s, Spanned<Stmt<'s>>> {
        let peeked = self.peek().ok_or_else(|| {
            self.push_diag(ParserDiag::unexpected(self, None, "statement"));
            ParserError::unexpected(None).handled()
        })?;

        match peeked.node {
            Token::If => self.if_stmt(),
            Token::While => self.while_stmt(),
            Token::OpenBrace => self.block_stmt(),
            _ => self.simple_stmt(),
        }
    }

    pub(super) fn simple_stmt(&mut self) -> ParserRes<'s, Spanned<Stmt<'s>>> {
        let stmt = match self.peek().unwrap().node {
            Token::Var => self.decl_stmt(),
            _ => self.print_or_expr_stmt(),
        }
        .catch_deferred(|err| match err {
            ParserErrorKind::Unexpected(Some(tok)) if matches!(tok.node, Token::Semicolon) => {
                self.push_diag(ParserDiag::early_terminated_stmt(tok.span));
                Err(ParserError::spurious_stmt_end().handled())
            }
            _ => Err(err.deferred()),
        })?;

        let semi = self
            .advance_or_peek(|tok| matches!(tok, Token::Semicolon))
            .map_err(|tok| {
                self.push_diag(ParserDiag::unterminated_stmt(
                    stmt.span,
                    self.span_or_eof(&tok),
                ));
                ParserError::spurious_stmt_end().handled()
            })?;

        Ok(stmt.join_with_span(&semi))
    }

    pub(super) fn if_stmt(&mut self) -> ParserRes<'s, Spanned<Stmt<'s>>> {
        let kw_if = self.advance().unwrap();
        debug_assert!(matches!(kw_if.node, Token::If));

        let (_, cond, _) = self.pair(Pair::Parens, Self::expr)?;

        let true_body = self.stmt()?;

        let false_body = if self
            .advance_or_peek(|tok| matches!(tok, Token::Else))
            .is_ok()
        {
            Some(self.stmt()?)
        } else {
            None
        };

        let span = kw_if.span.join(
            false_body
                .as_ref()
                .map(HasSpan::span)
                .unwrap_or_else(|| true_body.span),
        );

        Ok(stmt::if_else(cond, true_body, false_body).spanned(span))
    }

    pub(super) fn while_stmt(&mut self) -> ParserRes<'s, Spanned<Stmt<'s>>> {
        let kw_while = self.advance().unwrap();
        debug_assert!(matches!(kw_while.node, Token::While));

        let (_, cond, _) = self.pair(Pair::Parens, Self::expr)?;
        let body = self.stmt()?;

        let span = kw_while.span.join(body.span);
        Ok(stmt::while_loop(cond, body).spanned(span))
    }

    pub(super) fn block_stmt(&mut self) -> ParserRes<'s, Spanned<Stmt<'s>>> {
        debug_assert!(matches!(self.peek().unwrap().node, Token::OpenBrace));

        let (open, stmts, close) = self.pair(Pair::Braces, |this| this.stmts(false))?;

        let span = open.span.join(close.span);
        Ok(stmt::block(stmts).spanned(span))
    }

    pub(super) fn decl_stmt(&mut self) -> ParserRes<'s, Spanned<Stmt<'s>>> {
        let kw_var = self.advance().unwrap();
        debug_assert!(matches!(kw_var.node, Token::Var));

        let name = self
            .advance_map_or_peek(|tok| match tok {
                Token::Ident(name) => Some(*name),
                _ => None,
            })
            .map_err(|tok| {
                self.push_diag(ParserDiag::missing_var_name(
                    kw_var.span,
                    self.span_or_eof(&tok),
                ));

                if matches!(tok.map(|tok| tok.node), Some(Token::Semicolon)) {
                    ParserError::spurious_stmt_end().handled()
                } else {
                    ParserError::unexpected(tok).handled()
                }
            })?;

        let init = if self
            .advance_or_peek(|tok| matches!(tok, Token::Equal))
            .is_ok()
        {
            Some(self.expr()?)
        } else {
            None
        };

        let span = kw_var
            .span
            .join(init.as_ref().map(|init| init.span).unwrap_or(name.span));

        Ok(stmt::decl(name, init).spanned(span))
    }

    pub(super) fn print_or_expr_stmt(&mut self) -> ParserRes<'s, Spanned<Stmt<'s>>> {
        let print = self.advance_or_peek(|tok| matches!(tok, Token::Print)).ok();
        let val = self.expr()?;

        if let Some(print) = print {
            let span = print.span.join(val.span);
            Ok(stmt::print(val).spanned(span))
        } else {
            let span = val.span;
            Ok(stmt::expr(val).spanned(span))
        }
    }

    pub(super) fn expr(&mut self) -> ParserRes<'s, Spanned<Expr<'s>>> {
        self.assign()
    }

    pub(super) fn assign(&mut self) -> ParserRes<'s, Spanned<Expr<'s>>> {
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

    pub(super) fn logic_or(&mut self) -> ParserRes<'s, Spanned<Expr<'s>>> {
        self.left_assoc(Self::logic_and, |tok| matches!(tok, Token::Or))
    }

    pub(super) fn logic_and(&mut self) -> ParserRes<'s, Spanned<Expr<'s>>> {
        self.left_assoc(Self::equality, |tok| matches!(tok, Token::And))
    }

    pub(super) fn equality(&mut self) -> ParserRes<'s, Spanned<Expr<'s>>> {
        self.left_assoc(Self::comparison, |tok| {
            matches!(tok, Token::EqualEqual | Token::BangEqual)
        })
    }

    pub(super) fn comparison(&mut self) -> ParserRes<'s, Spanned<Expr<'s>>> {
        self.left_assoc(Self::terms, |tok| {
            matches!(
                tok,
                Token::Less | Token::LessEqual | Token::Greater | Token::GreaterEqual,
            )
        })
    }

    pub(super) fn terms(&mut self) -> ParserRes<'s, Spanned<Expr<'s>>> {
        self.left_assoc(Self::factors, |tok| {
            matches!(tok, Token::Plus | Token::Minus)
        })
    }

    pub(super) fn factors(&mut self) -> ParserRes<'s, Spanned<Expr<'s>>> {
        self.left_assoc(Self::unary, |tok| {
            matches!(tok, Token::Star | Token::Slash | Token::Percent)
        })
    }

    pub(super) fn unary(&mut self) -> ParserRes<'s, Spanned<Expr<'s>>> {
        if let Ok(tok) = self.advance_or_peek(|tok| matches!(tok, Token::Minus | Token::Bang)) {
            let sym = tok.map(|tok| UnopSym::from_tok(&tok).unwrap());
            let opd = self.unary()?;
            Ok(expr::unop(sym, opd))
        } else {
            self.atom()
        }
    }

    pub(super) fn atom(&mut self) -> ParserRes<'s, Spanned<Expr<'s>>> {
        if self.check_next_some(|tok| matches!(tok, Token::OpenParen)) {
            let (open, inner, close) = self.pair(Pair::Parens, Self::expr)?;
            let span = open.span.join(close.span);
            Ok(expr::group(inner).spanned(span))
        } else if let Some(next_tok) = self.advance() {
            match next_tok.node {
                Token::Number(n) => Ok(next_tok.with_node(expr::literal(Lit::Num(n)))),
                Token::Str(s) => Ok(next_tok.with_node(expr::literal(Lit::Str(s)))),
                Token::Boolean(b) => Ok(next_tok.with_node(expr::literal(Lit::Bool(b)))),
                Token::Ident(name) => Ok(next_tok.with_node(expr::var(name))),
                Token::Nil => Ok(next_tok.with_node(expr::literal(Lit::Nil))),

                Token::Semicolon | Token::CloseParen | Token::CloseBrace => {
                    Err(ParserError::unexpected_tok(next_tok).deferred())
                }

                _ => {
                    self.push_diag(ParserDiag::unexpected_tok(self, next_tok, "expression"));
                    Err(ParserError::unexpected_tok(next_tok).handled())
                }
            }
        } else {
            self.push_diag(ParserDiag::unexpected(self, None, "expression"));
            Err(ParserError::unexpected(None).handled())
        }
    }
}

impl Drop for Parser<'_> {
    fn drop(&mut self) {
        if !self.diags.is_empty() {
            panic!("Parser dropped with pending diagnostics");
        }
    }
}
