//! Parser for Lox.

use std::iter::Peekable;

use crate::diag::{Diag, DiagKind, Diagnostic};
use crate::session::{Session, SessionKey};
use crate::span::{Source, Span, Spannable, Spanned};
use crate::syn::*;
use crate::tok::{Lexer, Token};
use crate::util::oxford_or;

#[cfg(test)]
mod test;

/// Scan and parse the source with the given index in the current session's source map.
pub fn parse_source(key: SessionKey, source_idx: usize) -> Option<Program> {
    let lexer = Lexer::new(key, key.get().sm.source(source_idx));
    let parser = Parser::new(lexer);
    parser.parse()
}

/// Parser for Lox.
#[derive(Debug, Clone)]
pub struct Parser<'s> {
    lexer: Peekable<Lexer<'s>>,
    source: Source<'s>,
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

/// Control flow and error recovery in the parser is mediated via these Results.
///
/// The errors that are actually reported to the user go through the diagnostic context instead.
type ParserRes<T> = Result<T, ParserError>;

enum ParserError {
    Handled(ParserErrorKind),
    Defered(ParserErrorKind),
}

impl ParserError {
    fn handled(self) -> Self {
        match self {
            ParserError::Defered(kind) => ParserError::Handled(kind),
            _ => self,
        }
    }

    fn new(kind: ParserErrorKind) -> Self {
        ParserError::Defered(kind)
    }

    fn spurious_close_paren(close: Span) -> Self {
        Self::new(ParserErrorKind::SpuriousCloseParen { close })
    }

    fn lone_binop(location: Span, level: BinopLevel) -> Self {
        Self::new(ParserErrorKind::LoneBinop { location, level })
    }

    fn unterminated_stmt() -> Self {
        Self::new(ParserErrorKind::UnterminatedStmt)
    }

    fn spurious_semi(location: Span) -> Self {
        Self::new(ParserErrorKind::SpuriousSemi { location })
    }

    fn eof() -> Self {
        Self::new(ParserErrorKind::Eof)
    }

    fn other() -> Self {
        Self::new(ParserErrorKind::Other)
    }

    fn kind(&self) -> &ParserErrorKind {
        match self {
            ParserError::Handled(kind) | ParserError::Defered(kind) => kind,
        }
    }

    fn into_kind(self) -> ParserErrorKind {
        match self {
            ParserError::Handled(kind) | ParserError::Defered(kind) => kind,
        }
    }
}

trait ParserResExt<T> {
    fn catch_deferred(self, f: impl FnOnce(ParserErrorKind) -> ParserRes<T>) -> ParserRes<T>;
}

impl<T> ParserResExt<T> for ParserRes<T> {
    fn catch_deferred(self, f: impl FnOnce(ParserErrorKind) -> ParserRes<T>) -> ParserRes<T> {
        match self {
            Err(ParserError::Defered(kind)) => f(kind),
            other => other,
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum ParserErrorKind {
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
    },

    /// Thrown when encountering an unexpected binary operator.
    ///
    /// Carries the binding level of the operator, to allow catching and recovering at the
    /// appropriate level of the parse tree.
    LoneBinop {
        location: Span,
        level: BinopLevel,
    },

    /// Thrown when a statement that requires a terminating semicolon doesn't have one.
    ///
    /// This indicates to the `program` rule that it might not need to synchronize to a semicolon;
    /// there was supposed to be a semicolon at the current position, and we assume in its absence
    /// that the next token (if it is a valid statement starting token) starts a statement.
    UnterminatedStmt,

    /// Thrown upon encountering a semicolon in a position unacceptable as an end of statement.
    SpuriousSemi {
        location: Span,
    },

    Eof,
    Other,
}

impl ParserErrorKind {
    fn handled(self) -> ParserError {
        ParserError::Handled(self)
    }

    fn defered(self) -> ParserError {
        ParserError::Defered(self)
    }
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

impl<'s> Parser<'s> {
    const ATOM_STARTS: [&'static str; 6] =
        ["number", "string", "`true`", "`false`", "`nil`", "`(`"];

    /// Get the span associated with the given error, if any.
    fn err_span(&self, err: &ParserErrorKind) -> Option<Span> {
        match err {
            ParserErrorKind::SpuriousCloseParen { close, .. } => Some(*close),
            ParserErrorKind::LoneBinop { location, .. } => Some(*location),
            ParserErrorKind::Eof => Some(self.end_of_source()),
            ParserErrorKind::SpuriousSemi { location } => Some(*location),
            _ => None,
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
    fn peek(&mut self) -> Option<&Token<'s>> {
        self.lexer.peek().map(|tok| &tok.node)
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

    /// Advances one token, and tests the result.
    ///
    /// Returns the advanced-over token, as an `Ok` if it passed the test and as an `Err`
    /// otherwise. Returns `Err(None)` if it encounters EOF.
    ///
    /// Does not emit any diagnostics.
    fn advance_test(
        &mut self,
        test: impl FnOnce(&Token) -> bool,
    ) -> Result<Spanned<Token<'s>>, Option<Spanned<Token<'s>>>> {
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
    fn advance_if(&mut self, test: impl FnOnce(&Token) -> bool) -> Option<Spanned<Token<'s>>> {
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
        while !self.is_at_end() {
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
    fn sync_to_stmt(&mut self) {
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
                .catch_deferred(|kind| {
                    panic!("uncaught deferred parser error {kind:?}");
                })
                .map_err(ParserError::into_kind)
            {
                Ok(stmt) => {
                    debug_println!("got stmt {stmt}, adding to program");
                    stmts.push(stmt);
                }

                Err(ParserErrorKind::UnterminatedStmt | ParserErrorKind::SpuriousSemi { .. }) => {
                    debug_println!("unterminated or spuriously terminated stmt, maybe not syncing");
                    if !self.check_next(|tok| tok.is_stmt_start()) {
                        debug_println!("=> next token is not a stmt start, syncing");
                        self.sync_to_stmt();
                    }
                }
                _ => {
                    debug_println!("error in parsing stmt, syncing");
                    self.sync_to_stmt();
                }
            }
        }

        debug_println!("no more stmts, returning accumulated program");

        Program { stmts }
    }

    fn stmt(&mut self) -> ParserRes<Spanned<Stmt<'s>>> {
        debug_println!("parsing stmt");
        let maybe_print = self.advance_if(|tok| matches!(tok, Token::Print));
        debug_println!("=> maybe print? {maybe_print:?}");

        let expr = self.expr()?;

        let semi = self
            .advance_if(|tok| matches!(tok, Token::Semicolon))
            .ok_or_else(|| {
                debug_println!("=> no semicolon at end of stmt");
                let mut stmt = expr.span;
                if let Some(print) = &maybe_print {
                    stmt = print.span.join(stmt);
                }

                ParserDiag::unterminated_stmt(stmt).emit();

                ParserError::unterminated_stmt().handled()
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
    fn expr(&mut self) -> ParserRes<Spanned<Expr<'s>>> {
        debug_println!("parsing expression");
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
        operand: impl Fn(&mut Self) -> ParserRes<Spanned<Expr<'s>>>,
        sym_test: impl Fn(&Token) -> bool,
        sym_map: impl Fn(Token) -> BinopSym,
    ) -> ParserRes<Spanned<Expr<'s>>> {
        debug_println!("parsing binop chain {level:?} initial LHS");

        let mut lhs = operand(self).catch_deferred(|kind| match kind {
            ParserErrorKind::LoneBinop {
                location,
                level: lv,
            } if lv == level => {
                debug_println!("=> found lone {lv:?} binop parsing LHS, attempting to parse RHS");
                let rhs = operand(self)
                    .map(|expr| expr.span)
                    .or_else(|err| self.err_span(err.kind()).ok_or(()))
                    .ok();

                debug_println!("=> maybe parsed {level:?} RHS after missing LHS, emitting diag");
                ParserDiag::missing_lhs(location, rhs).emit();

                let dummy_span = if let Some(rhs) = rhs {
                    location.join(rhs)
                } else {
                    location
                };

                Ok(expr::literal(Lit::Nil).spanned(dummy_span))
            }
            _ => Err(kind.defered()),
        })?;

        debug_println!("=> got {level:?} LHS {lhs}");

        while self.check_next(&sym_test) {
            let sym = self.advance_map(&sym_map).unwrap();
            debug_println!("=> got {level:?} operator {sym}");

            let rhs = operand(self).catch_deferred(|kind| match kind {
                ParserErrorKind::SpuriousCloseParen { .. }
                | ParserErrorKind::SpuriousSemi { .. }
                | ParserErrorKind::Eof => {
                    debug_println!("=> missing {level:?} RHS (paren, semi, or EOF), emitting");
                    let expected_rhs = self.err_span(&kind).unwrap();
                    ParserDiag::missing_rhs(lhs.span, sym.span, expected_rhs).emit();
                    Err(kind.handled())
                }
                _ => Err(kind.defered()),
            })?;

            debug_println!("=> got {level:?} RHS {rhs}");

            lhs = expr::binop(sym, lhs, rhs);
            debug_println!("=> current {level:?} chain {lhs}");
        }

        debug_println!("=> final {level:?} chain {lhs}");
        Ok(lhs)
    }

    /// Parse an equality operator chain.
    ///
    /// Corresponds to the `equal` grammar production.
    fn equal(&mut self) -> ParserRes<Spanned<Expr<'s>>> {
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
    fn comp(&mut self) -> ParserRes<Spanned<Expr<'s>>> {
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
    fn terms(&mut self) -> ParserRes<Spanned<Expr<'s>>> {
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
    fn factors(&mut self) -> ParserRes<Spanned<Expr<'s>>> {
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
    fn unary(&mut self) -> ParserRes<Spanned<Expr<'s>>> {
        debug_println!("parsing unary");
        if self.check_next(|tok| matches!(tok, Token::Minus | Token::Bang)) {
            let sym = self
                .advance_map(|tok| match tok {
                    Token::Minus => UnopSym::Neg,
                    Token::Bang => UnopSym::Not,
                    _ => unreachable!(),
                })
                .unwrap();
            debug_println!("got sym {sym}");

            let operand = self.unary().catch_deferred(|kind| match kind {
                ParserErrorKind::SpuriousCloseParen { .. }
                | ParserErrorKind::SpuriousSemi { .. }
                | ParserErrorKind::Eof => {
                    ParserDiag::missing_unop(sym.span, self.err_span(&kind).unwrap()).emit();
                    Err(kind.handled())
                }
                _ => Err(kind.defered()),
            })?;

            Ok(expr::unop(sym, operand))
        } else {
            self.atom()
        }
    }

    /// Parse an atomic (literal/identifier/parenthesized) expression.
    ///
    /// Corresponds to the `atom` grammar production.
    fn atom(&mut self) -> ParserRes<Spanned<Expr<'s>>> {
        debug_println!("parsing atom");
        if let Some(Spanned { node: tok, span }) = self.advance() {
            match tok {
                Token::Number(n) => Ok(expr::literal(Lit::Num(n)).spanned(span)),
                Token::Str(s) => Ok(expr::literal(Lit::Str(s)).spanned(span)),
                Token::Boolean(b) => Ok(expr::literal(Lit::Bool(b)).spanned(span)),
                Token::Nil => Ok(expr::literal(Lit::Nil).spanned(span)),
                Token::LeftParen => self.group(span),

                // Error productions
                Token::RightParen => Err(ParserError::spurious_close_paren(span)),

                Token::Semicolon => Err(ParserError::spurious_semi(span)),

                tok if tok.is_binop() => {
                    let level = BinopLevel::from_tok(&tok);
                    Err(ParserError::lone_binop(span, level))
                }

                _ => {
                    ParserDiag::unexpected_tok(span, Self::ATOM_STARTS).emit();
                    Err(ParserError::other().handled())
                }
            }
        } else {
            Err(ParserError::eof())
        }
    }

    /// Parse a parenthesized expression.
    ///
    /// Assumes that the opening parenthesis has already been advanced over. Uses the given span as
    /// the span for the opening paren, for diagnostic reporting.
    ///
    /// Corresponds to the parenthesized expression arm of the `atom` grammar production.
    fn group(&mut self, oparen_span: Span) -> ParserRes<Spanned<Expr<'s>>> {
        debug_println!("parsing group");
        let expr = match self.expr().catch_deferred(|kind| {
            if let ParserErrorKind::SpuriousCloseParen { close } = kind {
                ParserDiag::early_close_paren(oparen_span, close, Self::ATOM_STARTS).emit();
                Err(kind.handled())
            } else {
                Err(kind.defered())
            }
        }) {
            Ok(expr) => expr,
            Err(err) => match err.kind() {
                ParserErrorKind::SpuriousCloseParen { close } => {
                    // Close the group and return a dummy expression to allow checking for further
                    // errors in this expression
                    let dummy_span = oparen_span.join(*close);
                    return Ok(expr::literal(Lit::Nil).spanned(dummy_span));
                }
                _ => return Err(err),
            },
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
                return Err(ParserError::other().handled());
            }
        };

        Ok(expr.node.spanned(oparen_span.join(cparen_span)))
    }
}

#[derive(Debug)]
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

    MissingUnop {
        operator: Span,
        expected_op: Span,
    },

    UnterminatedStmt {
        stmt: Span,
    },

    UnexpectedStmtEnd {
        semi: Span,
        expected: Vec<&'static str>,
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
            Self::MissingUnop { .. } => "unary operator without operand",
            Self::UnterminatedStmt { .. } => "missing semicolon after statement",
            Self::UnexpectedStmtEnd { .. } => "unexpected statement end",
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

            Self::MissingUnop {
                operator,
                expected_op,
            } => diag
                .with_primary(expected_op, "expected operand expression here")
                .with_secondary(operator, "this operator")
                .with_note(format!("expected {}", oxford_or(&Parser::ATOM_STARTS))),

            Self::UnterminatedStmt { stmt } => {
                diag.with_primary(stmt, "expected semicolon after this statement")
            }

            Self::UnexpectedStmtEnd { semi, expected } => diag
                .with_primary(semi, "statement ended unexpectedly here")
                .with_note(format!("expected {}", oxford_or(&expected))),
        }
    }
}

impl Diagnostic for ParserDiag {
    fn into_diag(self) -> Diag {
        debug_println!("EMIT {self:?}");
        let message = self.message();
        self.elaborate(Diag::new(DiagKind::Error, message))
    }
}

#[derive(Debug)]
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

    fn missing_unop(operator: Span, expected_op: Span) -> Self {
        Self::MissingUnop {
            operator,
            expected_op,
        }
    }

    fn unterminated_stmt(stmt: Span) -> Self {
        Self::UnterminatedStmt { stmt }
    }

    fn unexpected_stmt_end(semi: Span, expected: impl IntoIterator<Item = &'static str>) -> Self {
        Self::UnexpectedStmtEnd {
            semi,
            expected: expected.into_iter().collect(),
        }
    }
}
