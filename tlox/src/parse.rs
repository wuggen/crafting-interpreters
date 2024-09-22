//! Parser for Lox.

use std::fmt::Write;
use std::iter::Peekable;

use crate::diag::{Diag, DiagKind, Diagnostic};
use crate::span::{Source, Span, Spannable, Spanned};
use crate::syn::*;
use crate::tok::{Lexer, Token};

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

#[derive(Debug, Clone, Copy)]
enum ParserError {
    EarlyCloseParen,
    Eof,
    Other,
}

/// Control flow and error recovery in the parser is mediated via these Results.
///
/// The errors that are actually reported to the user go through the diagnostic context instead.
type ParserRes = Result<Spanned<Expr>, ParserError>;

impl Parser<'_> {
    fn peek(&mut self) -> Option<&Token> {
        self.lexer.peek().map(|tok| &tok.node)
    }

    fn advance(&mut self) -> Option<Spanned<Token>> {
        self.lexer.next()
    }

    fn advance_map<T>(&mut self, f: impl FnOnce(Token) -> T) -> Option<Spanned<T>> {
        let tok = self.advance()?;
        Some(f(tok.node).spanned(tok.span))
    }

    fn advance_test(
        &mut self,
        test: impl FnOnce(&Token) -> bool,
        expected: impl IntoIterator<Item = &'static str>,
    ) -> Result<Spanned<Token>, ParserError> {
        if let Some(tok) = self.advance() {
            if test(&tok.node) {
                Ok(tok)
            } else {
                Unexpected::token(tok.span, expected).emit();
                Err(ParserError::Other)
            }
        } else {
            Unexpected::eof(self.source, expected).emit();
            Err(ParserError::Eof)
        }
    }

    fn check_next(&mut self, test: impl FnOnce(&Token) -> bool) -> bool {
        self.peek().map(test).unwrap_or_default()
    }

    fn advance_until(&mut self, test: impl Fn(&Token) -> bool) -> Vec<Spanned<Token>> {
        let mut toks = vec![];
        while self.check_next(&test) {
            toks.push(self.advance().unwrap());
        }
        toks
    }

    fn synchronize(&mut self, until: impl Fn(&Token) -> bool, next: impl Fn(&Token) -> bool) {
        loop {
            self.advance_until(&until);
            if self.check_next(&next) {
                break;
            }
        }
    }

    fn expr(&mut self) -> ParserRes {
        debug_println!("= Parsing expression");
        self.equal()
    }

    fn binop_chain_left_assoc(
        &mut self,
        operand: impl Fn(&mut Self) -> ParserRes,
        sym_test: impl Fn(&Token) -> bool,
        sym_map: impl Fn(Token) -> BinopSym,
    ) -> ParserRes {
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

    fn equal(&mut self) -> ParserRes {
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

    fn comp(&mut self) -> ParserRes {
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

    fn terms(&mut self) -> ParserRes {
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

    fn factors(&mut self) -> ParserRes {
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

    fn unary(&mut self) -> ParserRes {
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

    fn atom(&mut self) -> ParserRes {
        const EXPECTED: [&str; 6] = ["number", "string", "`true`", "`false`", "`nil`", "`(`"];

        if let Some(Spanned { node: tok, span }) = self.advance() {
            match tok {
                Token::Number(n) => Ok(Expr::literal(Lit::Num(n)).spanned(span)),
                Token::StringLiteral(s) => Ok(Expr::literal(Lit::Str(s)).spanned(span)),
                Token::Boolean(b) => Ok(Expr::literal(Lit::Bool(b)).spanned(span)),
                Token::Nil => Ok(Expr::literal(Lit::Nil).spanned(span)),

                Token::LeftParen => {
                    let expr = self.expr()?;
                    self.advance_test(|tok| matches!(tok, Token::RightParen), Some("`)`"))?;
                    Ok(expr)
                }

                Token::RightParen => {
                    Diag::new(
                        DiagKind::Error,
                        "premature closing parenthesis",
                        span,
                        "parentheses closed early",
                    )
                    .emit();
                    Err(ParserError::EarlyCloseParen)
                }

                _ => {
                    Unexpected::token(span, EXPECTED).emit();
                    Err(ParserError::Other)
                }
            }
        } else {
            Unexpected::eof(self.source, EXPECTED).emit();
            Err(ParserError::Eof)
        }
    }
}

struct Unexpected {
    message: &'static str,
    span: Span,
    expected: Vec<&'static str>,
}

impl Diagnostic for Unexpected {
    fn into_diag(self) -> Diag {
        let mut primary_label = String::new();
        if self.expected.len() == 1 {
            write!(primary_label, "expected {} here", self.expected[0]).unwrap();
        } else {
            primary_label.push_str("expected ");
            for val in &self.expected[..self.expected.len() - 1] {
                write!(primary_label, "{val}, ").unwrap();
            }
            write!(primary_label, "or {} here", self.expected.last().unwrap()).unwrap();
        }

        Diag::new(DiagKind::Error, self.message, self.span, primary_label)
    }
}

impl Unexpected {
    fn new(
        message: &'static str,
        span: Span,
        expected: impl IntoIterator<Item = &'static str>,
    ) -> Self {
        Self {
            message,
            span,
            expected: expected.into_iter().collect(),
        }
    }

    fn eof(source: Source, expected: impl IntoIterator<Item = &'static str>) -> Self {
        let len = source.span().len();
        let span = source.span().subspan(len - 1..).unwrap();
        Self::new("unexpected end of input", span, expected)
    }

    fn token(span: Span, expected: impl IntoIterator<Item = &'static str>) -> Self {
        Self::new("unexpected token in input", span, expected)
    }
}

#[cfg(test)]
mod test {
    use indoc::indoc;
    use insta::assert_snapshot;

    use crate::context::with_new_interpreter;
    use crate::diag::render::render_dcx;
    use crate::span::SourceMap;

    use super::*;

    fn parse_source(source: &str) -> Option<Spanned<Expr>> {
        let source_idx = SourceMap::with_current_mut(|sm| sm.add_source(0, source));

        SourceMap::with_current(|sm| {
            let lexer = Lexer::new(sm.source(source_idx));
            let parser = Parser::new(lexer);
            let res = parser.parse();
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
            parse_source("+ 4");
            assert_snapshot!(render_dcx(), @r#"
            error: unexpected token in input
              --> %i0:1:1
              |
            1 | + 4
              | ^ expected number, string, `true`, `false`, `nil`, or `(` here

            "#);

            parse_source("4 + (* nil) - 5");
            assert_snapshot!(render_dcx(), @r#"
            error: unexpected token in input
              --> %i0:1:6
              |
            1 | 4 + (* nil) - 5
              |      ^ expected number, string, `true`, `false`, `nil`, or `(` here

            "#);
        });
    }

    #[test]
    fn err_missing_rhs() {
        with_new_interpreter(|_| {
            parse_source("4 +");
            assert_snapshot!(render_dcx(), @r#"
            error: unexpected end of input
              --> %i0:1:4
              |
            1 | 4 +
              |    ^ expected number, string, `true`, `false`, `nil`, or `(` here

            "#);
        });
    }

    #[test]
    fn err_early_close_paren() {
        with_new_interpreter(|_| {
            parse_source("4 + (nil *) - 5");
            assert_snapshot!(render_dcx(), @r#"
            error: premature closing parenthesis
              --> %i0:1:11
              |
            1 | 4 + (nil *) - 5
              |           ^ parentheses closed early

            "#);
        });
    }

    #[test]
    // TODO Parser actually can't detect this one yet, it just assumes it's at the end of an
    // expression and quits lol
    #[ignore = "parser not equipped to detect this condition yet"]
    fn err_spurious_close_paren() {
        with_new_interpreter(|_| {
            parse_source("45 - nil ) / false");
            assert_snapshot!(render_dcx(), @"");
        });
    }
}
