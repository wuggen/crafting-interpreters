//! Parser for Lox.

use std::fmt::Write;

use crate::diag::{Diag, DiagKind, Diagnostic};
use crate::span::{Span, Spannable, Spanned};
use crate::syn::*;
use crate::tok::{Lexer, Token, TokenKind};

#[derive(Debug, Clone)]
pub struct Parser<'sm> {
    lexer: Lexer<'sm>,
    peeked: Option<Option<Token>>,
}

// Grammar:
//
// expr -> equal
//
// ; Left-assoc
// equal -> comp ( ('!=' | '==') comp )*
//
// ; Left-assoc
// comp -> term ( ('<' | '<=' | '>' | '>=') term )*
//
// ; Left-assoc
// term -> factor ( ('+' | '-') factor )*
//
// ; Left-assoc
// factor -> unary ( ('*' | '/' | '%') unary )*
//
// unary -> ('-' | '!') unary
//        | atom
//
// atom -> NUMBER | STRING | 'true' | 'false' | 'nil'
//       | '(' expr ')'

impl<'sm> Parser<'sm> {
    pub fn new(lexer: Lexer<'sm>) -> Self {
        Self {
            lexer,
            peeked: None,
        }
    }

    pub fn parse(mut self) -> Option<Spanned<Expr>> {
        let res = self.expr();
        debug_assert!(self.lexer.next().is_none(), "input was not exhausted");
        res
    }

    fn emit_error(
        &self,
        kind: ParserErrorKind,
        span: Span,
        expected: impl IntoIterator<Item = &'static str>,
        desc: impl Into<Option<&'static str>>,
    ) {
        let diag = ParserError {
            kind,
            span,
            expected: expected.into_iter().collect(),
            desc: desc.into(),
        };

        diag.emit();
    }

    fn emit_unexpected(
        &self,
        span: Span,
        expected: impl IntoIterator<Item = &'static str>,
        desc: impl Into<Option<&'static str>>,
    ) {
        self.emit_error(ParserErrorKind::Unexpected, span, expected, desc);
    }

    fn emit_eof(
        &self,
        expected: impl IntoIterator<Item = &'static str>,
        desc: impl Into<Option<&'static str>>,
    ) {
        let source_span = self.lexer.source().span();
        let source_span_len = source_span.len();
        let span = source_span
            .subspan(source_span_len.saturating_sub(1)..)
            .unwrap();
        self.emit_error(ParserErrorKind::EndOfInput, span, expected, desc);
    }

    fn advance(&mut self) -> Option<Token> {
        let res = self.peeked.take().unwrap_or_else(|| self.lexer.next());
        debug_println!("--> Advanced over {res:?}");
        res
    }

    fn peek(&mut self) -> Option<&Token> {
        let lexer = &mut self.lexer;
        self.peeked.get_or_insert_with(|| lexer.next()).as_ref()
    }

    fn advance_if(&mut self, f: impl FnOnce(&TokenKind) -> bool) -> Option<Token> {
        if f(&self.peek()?.node) {
            self.advance()
        } else {
            None
        }
    }

    fn advance_match(
        &mut self,
        expected_tok: TokenKind,
        expected: &'static str,
        desc: impl Into<Option<&'static str>>,
    ) -> Option<Token> {
        debug_println!("--> Advancing, expecting {expected}");
        if let Some(tok) = self.advance() {
            if tok.node != expected_tok {
                debug_println!(
                    "!! Token did not match {expected}, emitting error and returning None"
                );
                self.emit_unexpected(tok.span, Some(expected), desc);
                None
            } else {
                Some(tok)
            }
        } else {
            debug_println!(
                "!! No further tokens, expecting {expected}, emitting error and returning None"
            );
            self.emit_eof(Some(expected), desc);
            None
        }
    }

    fn advance_until(&mut self, test: impl Fn(&TokenKind) -> bool) -> Vec<Token> {
        let mut res = vec![];
        while let Some(tok) = self.advance_if(&test) {
            res.push(tok);
        }
        res
    }

    fn recovery_advance_to_sync(
        &mut self,
        test: impl Fn(&TokenKind) -> bool,
        message: impl Into<String>,
        label: impl FnOnce(&[Token]) -> Option<String>,
        notes: impl FnOnce(&[Token]) -> Vec<String>,
    ) {
        let toks = self.advance_until(test);
        if !toks.is_empty() {
            let span = toks.first().unwrap().span.join(toks.last().unwrap().span);
            let message = message.into();
            let label = label(&toks).unwrap_or("".into());
            let notes = notes(&toks);
            let diag = notes.into_iter().fold(
                Diag::new(DiagKind::Warning, message, span, label),
                Diag::with_note,
            );
            diag.emit();
        }
    }

    fn binop_chain_left(
        &mut self,
        opnd: impl Fn(&mut Self) -> Option<Spanned<Expr>>,
        op: impl Fn(&TokenKind) -> Option<BinopSym>,
    ) -> Option<Spanned<Expr>> {
        debug_println!("== Initial recurse on operand");
        let mut res = opnd(self)?;
        debug_println!("== Initial operand {res}");

        while let Some(tok) = self.peek() {
            if let Some(sym) = op(&tok.node) {
                let sym = sym.spanned(tok.span);
                self.advance();
                debug_println!("== Recurse on operand");
                if let Some(rhs) = opnd(self) {
                    debug_println!("== Operand {rhs}");
                    let span = res.span.join(rhs.span);
                    res = Expr::binop(sym, res, rhs).spanned(span);
                    debug_println!("== Current chain: {res}");
                } else {
                    debug_println!("!! RHS missing, should have emitted error");
                    break;
                }
            } else {
                debug_println!("== No further binops");
                break;
            }
        }

        Some(res)
    }

    fn expr(&mut self) -> Option<Spanned<Expr>> {
        debug_println!("= Parsing expression");
        self.equal()
    }

    fn equal(&mut self) -> Option<Spanned<Expr>> {
        debug_println!("= Parsing equality chain");
        self.binop_chain_left(Self::comp, |tok| match tok {
            TokenKind::EqualEqual => Some(BinopSym::Eq),
            TokenKind::BangEqual => Some(BinopSym::Ne),
            _ => None,
        })
    }

    fn comp(&mut self) -> Option<Spanned<Expr>> {
        debug_println!("= Parsing comparison chain");
        self.binop_chain_left(Self::term, |tok| match tok {
            TokenKind::Less => Some(BinopSym::Lt),
            TokenKind::LessEqual => Some(BinopSym::Le),
            TokenKind::Greater => Some(BinopSym::Gt),
            TokenKind::GreaterEqual => Some(BinopSym::Ge),
            _ => None,
        })
    }

    fn term(&mut self) -> Option<Spanned<Expr>> {
        debug_println!("= Parsing term chain");
        self.binop_chain_left(Self::factor, |tok| match tok {
            TokenKind::Plus => Some(BinopSym::Add),
            TokenKind::Minus => Some(BinopSym::Sub),
            _ => None,
        })
    }

    fn factor(&mut self) -> Option<Spanned<Expr>> {
        debug_println!("= Parsing factor chain");
        self.binop_chain_left(Self::unary, |tok| match tok {
            TokenKind::Star => Some(BinopSym::Mul),
            TokenKind::Slash => Some(BinopSym::Div),
            TokenKind::Percent => Some(BinopSym::Mod),
            _ => None,
        })
    }

    fn unary(&mut self) -> Option<Spanned<Expr>> {
        debug_println!("= Parsing unary expression");
        let tok = self.peek()?;
        let sym = match tok.node {
            TokenKind::Bang => UnopSym::Not,
            TokenKind::Minus => UnopSym::Neg,
            _ => {
                debug_println!("== No unary operator, continuing down");
                return self.atom();
            }
        }
        .spanned(tok.span);
        self.advance();

        debug_println!("== Recursing on unary operand");
        let opnd = self.unary()?;
        debug_println!("== Unary operand {opnd}");
        let span = sym.span.join(opnd.span);
        Some(Expr::unop(sym, opnd).spanned(span))
    }

    fn atom(&mut self) -> Option<Spanned<Expr>> {
        debug_println!("= Parsing atom");
        const EXPECTED: [&str; 7] = [
            "`true`",
            "`false`",
            "`nil`",
            "`(`",
            "number",
            "string",
            "identifier",
        ];

        if let Some(tok) = self.advance() {
            let expr = match tok.node {
                TokenKind::Boolean(b) => Expr::literal(Lit::Bool(b)),
                TokenKind::Nil => Expr::literal(Lit::Nil),
                TokenKind::Number(n) => Expr::literal(Lit::Num(n)),
                TokenKind::StringLiteral(s) => Expr::literal(Lit::Str(s)),
                TokenKind::Ident(_id) => todo!(),
                TokenKind::LeftParen => {
                    debug_println!("== Parenthesized expr, recursing from top");
                    let res = self.expr();

                    if let Some(res) = res.as_ref() {
                        debug_println!("== Parenthesized expr {res}");
                    } else {
                        debug_println!("!! Parenthesized expression returned None; should have emitted error, looking for closing paren and continuing");
                    }

                    let close = if let Some(close) =
                        self.advance_match(TokenKind::RightParen, "`)`", None)
                    {
                        close
                    } else {
                        debug_println!("!! No closing paren, returning None");
                        return None;
                    };
                    return res.map(|e| e.node.spanned(tok.span.join(close.span)));
                }
                _ => {
                    debug_println!(
                        "!! No valid atom starting token, emitting error and returning None"
                    );
                    self.emit_error(
                        ParserErrorKind::Unexpected,
                        tok.span,
                        EXPECTED,
                        "an expression",
                    );
                    return None;
                }
            };

            Some(expr.spanned(tok.span))
        } else {
            debug_println!("!! EOF before atom token, emitting error and returning None");
            self.emit_eof(EXPECTED, "an expression");
            None
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum ParserErrorKind {
    Unexpected,
    EndOfInput,
}

#[derive(Debug, Clone)]
pub struct ParserError {
    kind: ParserErrorKind,
    span: Span,
    expected: Vec<&'static str>,
    desc: Option<&'static str>,
}

impl Diagnostic for ParserError {
    fn into_diag(self) -> crate::diag::Diag {
        let message = match self.kind {
            ParserErrorKind::Unexpected => "unexpected token",
            ParserErrorKind::EndOfInput => "unexpected end of input",
        };

        let label = if self.expected.is_empty() {
            String::new()
        } else if self.expected.len() == 1 {
            format!("expected {} here", self.expected[0])
        } else {
            let mut s = String::from("expected ");
            for tok in &self.expected[..self.expected.len() - 1] {
                write!(&mut s, "{tok}, ").unwrap();
            }
            write!(&mut s, "or {} here", self.expected.last().unwrap()).unwrap();

            s
        };

        let diag = Diag::new(DiagKind::Error, message, self.span, label);

        if let Some(desc) = self.desc {
            diag.with_note(format!("note: expecting to parse {desc}"))
        } else {
            diag
        }
    }
}

#[cfg(test)]
mod test {
    use indoc::indoc;
    use insta::assert_snapshot;

    use crate::context::{with_new_interpreter, with_source_map, with_source_map_mut};
    use crate::diag::render::render_dcx;

    use super::*;

    fn parse_source(source: &str) -> Option<Spanned<Expr>> {
        let source_idx = with_source_map_mut(|sm| sm.add_source(0, source));

        with_source_map(|sm| {
            let lexer = Lexer::new(sm.source(source_idx));
            let mut parser = Parser::new(lexer);
            let res = parser.expr();
            if let Some(res) = res.as_ref() {
                debug_println!("PARSED: {res}\n");
            } else {
                debug_println!("PARSED: None\n");
            }

            res
        })
    }

    #[test]
    fn literals() {
        with_new_interpreter(|_| {
            let res = parse_source("true");
            assert_snapshot!(res.unwrap(), @"true{1:1..1:4}");
            assert!(render_dcx().is_empty());

            let res = parse_source("134");
            assert_snapshot!(res.unwrap(), @"134{1:1..1:3}");
            assert!(render_dcx().is_empty());

            let res = parse_source(r#""lol hey\ndude""#);
            assert_snapshot!(res.unwrap(), @r#""lol hey\ndude"{1:1..1:15}"#);
            assert!(render_dcx().is_empty());
        });
    }

    #[test]
    fn comp_chain() {
        with_new_interpreter(|_| {
            let res = parse_source(indoc! {r#"
            45 < nil >= false
                <= "wow" > 003.32
            "#});
            assert_snapshot!(res.unwrap().node, @r#"(> (<= (>= (< 45 nil) false) "wow") 3.32)"#);
            assert!(render_dcx().is_empty());
        });
    }

    #[test]
    fn comp_chain_with_parens() {
        with_new_interpreter(|_| {
            let res = parse_source(r#"45 < ("wow" >= nil)"#);
            assert_snapshot!(res.unwrap().node, @r#"(< 45 (>= "wow" nil))"#);
            assert!(render_dcx().is_empty());
        });
    }

    #[test]
    fn lotsa_parens() {
        with_new_interpreter(|_| {
            let res = parse_source(indoc! {r#"
            (((true + "false") - (nil / nil) >= 0 * "hey") % ("what")) + (0)
            "#});
            assert_snapshot!(res.unwrap().node, @r#"(+ (% (>= (- (+ true "false") (/ nil nil)) (* 0 "hey")) "what") 0)"#);
            assert!(render_dcx().is_empty());
        });
    }

    #[test]
    fn err_missing_lhs() {
        with_new_interpreter(|_| {
            let res = parse_source("+ 4");
            assert!(res.is_none());
            assert_snapshot!(render_dcx(), @r#"
            error: unexpected token
              --> %i0:1:1
              |
            1 | + 4
              | ^ expected `true`, `false`, `nil`, `(`, number, string, or identifier here
              |
              = note: expecting to parse an expression

            "#);

            let res = parse_source("4 + (* nil) - 5");
            assert_snapshot!(res.unwrap().node, @"4");
            assert_snapshot!(render_dcx(), @r#"
            error: unexpected token
              --> %i0:1:6
              |
            1 | 4 + (* nil) - 5
              |      ^ expected `true`, `false`, `nil`, `(`, number, string, or identifier here
              |
              = note: expecting to parse an expression

            error: unexpected token
              --> %i0:1:8
              |
            1 | 4 + (* nil) - 5
              |        ^^^ expected `)` here

            "#);
        });
    }
}