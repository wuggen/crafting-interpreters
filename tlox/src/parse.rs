//! Parser for Lox.

use std::fmt::Write;

use crate::diag::{Diag, DiagKind, Diagnostic};
use crate::span::{Span, Spannable, Spanned};
use crate::syn::*;
use crate::tok::{Lexer, Token, TokenKind};

#[derive(Debug, Clone)]
pub struct Parser<'sm, 'dcx> {
    lexer: Lexer<'sm, 'dcx>,
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

impl<'sm, 'dcx> Parser<'sm, 'dcx> {
    pub fn new(lexer: Lexer<'sm, 'dcx>) -> Self {
        Self {
            lexer,
            peeked: None,
        }
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

        self.lexer.diag_context().emit(diag);
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
        //eprintln!("--> Advanced over {res:?}");
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
        //eprintln!("--> Advancing, expecting {expected}");
        if let Some(tok) = self.advance() {
            if tok.node != expected_tok {
                //eprintln!("!! Token did not match {expected}, emitting error and returning None");
                self.emit_unexpected(tok.span, Some(expected), desc);
                None
            } else {
                Some(tok)
            }
        } else {
            //eprintln!(
            //    "!! No further tokens, expecting {expected}, emitting error and returning None"
            //);
            self.emit_eof(Some(expected), desc);
            None
        }
    }

    fn binop_chain_left(
        &mut self,
        opnd: impl Fn(&mut Self) -> Option<Spanned<Expr>>,
        op: impl Fn(&TokenKind) -> Option<BinopSym>,
    ) -> Option<Spanned<Expr>> {
        //eprintln!("== Initial recurse on operand");
        let mut res = opnd(self)?;
        //eprintln!("== Initial operand {res}");

        while let Some(tok) = self.peek() {
            if let Some(sym) = op(&tok.node) {
                let sym = sym.spanned(tok.span);
                self.advance();
                //eprintln!("== Recurse on operand");
                if let Some(rhs) = opnd(self) {
                    //eprintln!("== Operand {rhs}");
                    let span = res.span.join(rhs.span);
                    res = Expr::binop(sym, res, rhs).spanned(span);
                    //eprintln!("== Current chain: {res}");
                } else {
                    //eprintln!("!! RHS missing, should have emitted error");
                    break;
                }
            } else {
                //eprintln!("== No further binops");
                break;
            }
        }

        Some(res)
    }

    fn expr(&mut self) -> Option<Spanned<Expr>> {
        //eprintln!("= Parsing expression");
        self.equal()
    }

    fn equal(&mut self) -> Option<Spanned<Expr>> {
        //eprintln!("= Parsing equality chain");
        self.binop_chain_left(Self::comp, |tok| match tok {
            TokenKind::EqualEqual => Some(BinopSym::Eq),
            TokenKind::BangEqual => Some(BinopSym::Ne),
            _ => None,
        })
    }

    fn comp(&mut self) -> Option<Spanned<Expr>> {
        //eprintln!("= Parsing comparison chain");
        self.binop_chain_left(Self::term, |tok| match tok {
            TokenKind::Less => Some(BinopSym::Lt),
            TokenKind::LessEqual => Some(BinopSym::Le),
            TokenKind::Greater => Some(BinopSym::Gt),
            TokenKind::GreaterEqual => Some(BinopSym::Ge),
            _ => None,
        })
    }

    fn term(&mut self) -> Option<Spanned<Expr>> {
        //eprintln!("= Parsing term chain");
        self.binop_chain_left(Self::factor, |tok| match tok {
            TokenKind::Plus => Some(BinopSym::Add),
            TokenKind::Minus => Some(BinopSym::Sub),
            _ => None,
        })
    }

    fn factor(&mut self) -> Option<Spanned<Expr>> {
        //eprintln!("= Parsing factor chain");
        self.binop_chain_left(Self::unary, |tok| match tok {
            TokenKind::Star => Some(BinopSym::Mul),
            TokenKind::Slash => Some(BinopSym::Div),
            TokenKind::Percent => Some(BinopSym::Mod),
            _ => None,
        })
    }

    fn unary(&mut self) -> Option<Spanned<Expr>> {
        //eprintln!("= Parsing unary expression");
        let tok = self.peek()?;
        let sym = match tok.node {
            TokenKind::Bang => UnopSym::Not,
            TokenKind::Minus => UnopSym::Neg,
            _ => {
                //eprintln!("== No unary operator, continuing down");
                return self.atom();
            }
        }
        .spanned(tok.span);
        self.advance();

        //eprintln!("== Recursing on unary operand");
        let opnd = self.unary()?;
        //eprintln!("== Unary operand {opnd}");
        let span = sym.span.join(opnd.span);
        Some(Expr::unop(sym, opnd).spanned(span))
    }

    fn atom(&mut self) -> Option<Spanned<Expr>> {
        //eprintln!("= Parsing atom");
        const EXPECTED: [&'static str; 7] = [
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
                    //eprintln!("== Parenthesized expr, recursing from top");
                    let res = self.expr();
                    if let Some(res) = res.as_ref() {
                        //eprintln!("== Parenthesized expr {res}");
                    } else {
                        //eprintln!("!! Parenthesized expression returned None; should have emitted error, looking for closing paren and continuing");
                    }
                    let close =
                        if let Some(close) = self.advance_match(TokenKind::RightParen, ")", None) {
                            close
                        } else {
                            //eprintln!("!! No closing paren, returning None");
                            return None;
                        };
                    return res.map(|e| e.node.spanned(tok.span.join(close.span)));
                }
                _ => {
                    //eprintln!("!! No valid atom starting token, emitting error and returning None");
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
            //eprintln!("!! EOF before atom token, emitting error and returning None");
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
            format!("expected `{}` here", self.expected[0])
        } else {
            let mut s = String::from("expected ");
            for tok in &self.expected[..self.expected.len() - 1] {
                write!(&mut s, "`{tok}`, ").unwrap();
            }
            write!(&mut s, "or `{}` here", self.expected.last().unwrap()).unwrap();

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
    use insta::{assert_debug_snapshot, assert_snapshot};

    use crate::diag::render::render_dcx;
    use crate::diag::DiagContext;
    use crate::span::SourceMap;

    use super::*;

    fn parse_source(source: &str) -> (SourceMap, DiagContext, Option<Spanned<Expr>>) {
        let mut sm = SourceMap::new();
        sm.add_source(0, source);
        let dcx = DiagContext::new();
        let lexer = Lexer::new(sm.source(0), &dcx);
        let mut parser = Parser::new(lexer);
        let res = parser.expr();

        (sm, dcx, res)
    }

    #[test]
    fn literals() {
        let (sm, dcx, res) = parse_source("true");
        assert_snapshot!(res.unwrap(), @"true{0..4}");
        assert!(render_dcx(sm, dcx).is_empty());

        let (sm, dcx, res) = parse_source("134");
        assert_snapshot!(res.unwrap(), @"134{0..3}");
        assert!(render_dcx(sm, dcx).is_empty());

        let (sm, dcx, res) = parse_source(r#""lol hey\ndude""#);
        assert_snapshot!(res.unwrap(), @r#""lol hey\ndude"{0..15}"#);
        assert!(render_dcx(sm, dcx).is_empty());
    }

    #[test]
    fn comp_chain() {
        let (sm, dcx, res) = parse_source(indoc! {r#"
        45 < nil >= false
            <= "wow" > 003.32
        "#});
        assert_snapshot!(res.unwrap().node, @r#"(> (<= (>= (< 45 nil) false) "wow") 3.32)"#);
        assert!(render_dcx(sm, dcx).is_empty());
    }

    #[test]
    fn comp_chain_with_parens() {
        let (sm, dcx, res) = parse_source(r#"45 < ("wow" >= nil)"#);
        assert_snapshot!(res.unwrap().node, @r#"(< 45 (>= "wow" nil))"#);
        assert!(render_dcx(sm, dcx).is_empty());
    }

    #[test]
    fn lotsa_parens() {
        let (sm, dcx, res) = parse_source(indoc! {r#"
        (((true + "false") - (nil / nil) >= 0 * "hey") % ("what")) + (0)
        "#});
        assert_snapshot!(res.unwrap().node, @r#"(+ (% (>= (- (+ true "false") (/ nil nil)) (* 0 "hey")) "what") 0)"#);
        assert!(render_dcx(sm, dcx).is_empty());
    }
}
