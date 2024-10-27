use std::fmt::Debug;
use std::ops::{Range, RangeInclusive};

use indoc::indoc;
use insta::assert_snapshot;

use super::*;
use crate::diag::render::render_dcx;
use crate::session::Session;
use crate::span::Location;
use crate::sym;

trait TokenTestable<'s> {
    fn check(&self, tok: &Spanned<Token<'s>>) -> bool;
}

impl<'s> TokenTestable<'s> for Token<'s> {
    fn check(&self, tok: &Spanned<Token<'s>>) -> bool {
        self == &tok.node
    }
}

impl<'s> TokenTestable<'s> for Span {
    fn check(&self, tok: &Spanned<Token<'s>>) -> bool {
        *self == tok.span
    }
}

impl<'s> TokenTestable<'s> for Range<usize> {
    fn check(&self, tok: &Spanned<Token<'s>>) -> bool {
        &tok.span.range() == self
    }
}

impl<'s> TokenTestable<'s> for (Location, Location) {
    fn check(&self, tok: &Spanned<Token<'s>>) -> bool {
        Session::with_current(|key| *self == key.get().sm.span_extents(tok.span).unwrap())
    }
}

impl<'s> TokenTestable<'s> for RangeInclusive<(usize, usize)> {
    fn check(&self, tok: &Spanned<Token<'s>>) -> bool {
        Session::with_current(|key| {
            let (start, end) = key.get().sm.span_extents(tok.span).unwrap();
            ((start.line, start.column), (end.line, end.column)) == self.clone().into_inner()
        })
    }
}

impl<'s, A, B> TokenTestable<'s> for (A, B)
where
    A: TokenTestable<'s>,
    B: TokenTestable<'s>,
{
    fn check(&self, tok: &Spanned<Token<'s>>) -> bool {
        self.0.check(tok) && self.1.check(tok)
    }
}

fn check_scan<'s, I, T>(key: &'s SessionKey<'s>, source: &str, expected: I)
where
    I: IntoIterator<Item = T>,
    T: TokenTestable<'s> + Debug,
{
    let source_idx = key.get().sm.add_source(0, source);
    let mut success = true;
    let mut lexer = Lexer::new(key, key.get().sm.source(source_idx));

    let mut expected = expected.into_iter();

    loop {
        match (lexer.next(), expected.next()) {
            (None, None) => break,
            (None, Some(expected)) => {
                eprintln!("Reached end of scan earlier than expected (next expected {expected:?})");
                success = false;
                break;
            }

            (Some(tok), None) => {
                eprintln!("Scanned more tokens than expected (next scanned {tok:?})");
                success = false;
                break;
            }

            (Some(tok), Some(expected)) => {
                if !expected.check(&tok) {
                    eprintln!("Spanned<Token> mismatch: expected {expected:?}, got {tok:?}");
                    success = false;
                }
            }
        }
    }

    assert!(success);
}

/// Lex the given source in the context of a new, ephemeral interpreter.
///
/// Checks the resulting token stream against the given expected stream, panicking if there are any
/// mismatches. Renders and returns any resulting diagnostics.
fn check_and_render<'s, I, T>(key: &'s SessionKey<'s>, source: &str, expected: I) -> String
where
    I: IntoIterator<Item = T>,
    T: TokenTestable<'s> + Debug,
{
    check_scan(key, source, expected);
    render_dcx()
}

use Token::*;

fn ident<'s>(key: &SessionKey<'s>, s: &str) -> Token<'s> {
    Ident(sym!(key, s))
}

fn strlit<'s>(key: &SessionKey<'s>, s: &str) -> Token<'s> {
    Str(sym!(key, s))
}

fn num(n: f64) -> Token<'static> {
    Number(n)
}

#[test]
fn keywords() {
    Session::with_default(|key| {
        let source =
            "and or true false if else while for fun print var this super class nil return";
        let expected = [
            (And, 0..3),
            (Or, 4..6),
            (Boolean(true), 7..11),
            (Boolean(false), 12..17),
            (If, 18..20),
            (Else, 21..25),
            (While, 26..31),
            (For, 32..35),
            (Fun, 36..39),
            (Print, 40..45),
            (Var, 46..49),
            (This, 50..54),
            (Super, 55..60),
            (Class, 61..66),
            (Nil, 67..70),
            (Return, 71..77),
        ];
        assert!(check_and_render(&key, source, expected).is_empty());
    });
}

#[test]
fn one_char_punctuation() {
    Session::with_default(|key| {
        let source = "(){},.-+;*%";
        let expected = [
            (LeftParen, 0..1),
            (RightParen, 1..2),
            (LeftBrace, 2..3),
            (RightBrace, 3..4),
            (Comma, 4..5),
            (Dot, 5..6),
            (Minus, 6..7),
            (Plus, 7..8),
            (Semicolon, 8..9),
            (Star, 9..10),
            (Percent, 10..11),
        ];
        assert!(check_and_render(&key, source, expected).is_empty());
    });
}

#[test]
fn multi_char_punctuation() {
    Session::with_default(|key| {
        let source = "! != = == > >= < <=";
        let expected = [
            (Bang, 0..1),
            (BangEqual, 2..4),
            (Equal, 5..6),
            (EqualEqual, 7..9),
            (Greater, 10..11),
            (GreaterEqual, 12..14),
            (Less, 15..16),
            (LessEqual, 17..19),
        ];
        assert!(check_and_render(&key, source, expected).is_empty());
    });
}

#[test]
fn idents() {
    Session::with_default(|key| {
        let source = "hey what num_3 _unused __ n1234 fortune iface orange";
        let expected = [
            ident(&key, "hey"),
            ident(&key, "what"),
            ident(&key, "num_3"),
            ident(&key, "_unused"),
            ident(&key, "__"),
            ident(&key, "n1234"),
            ident(&key, "fortune"),
            ident(&key, "iface"),
            ident(&key, "orange"),
        ];
        assert!(check_and_render(&key, source, expected).is_empty())
    });
}

#[test]
fn mixed_punctuation_idents_keywords_newlines_comments() {
    Session::with_default(|key| {
        let source = indoc::indoc! {r#"
        if (hey) {
            var x = lmao; // what even
            now(what,lol);
        } // as if
        // lol"#};

        let expected = [
            (If, (0, 0)..=(0, 1)),
            (LeftParen, (0, 3)..=(0, 3)),
            (ident(&key, "hey"), (0, 4)..=(0, 6)),
            (RightParen, (0, 7)..=(0, 7)),
            (LeftBrace, (0, 9)..=(0, 9)),
            (Var, (1, 4)..=(1, 6)),
            (ident(&key, "x"), (1, 8)..=(1, 8)),
            (Equal, (1, 10)..=(1, 10)),
            (ident(&key, "lmao"), (1, 12)..=(1, 15)),
            (Semicolon, (1, 16)..=(1, 16)),
            (ident(&key, "now"), (2, 4)..=(2, 6)),
            (LeftParen, (2, 7)..=(2, 7)),
            (ident(&key, "what"), (2, 8)..=(2, 11)),
            (Comma, (2, 12)..=(2, 12)),
            (ident(&key, "lol"), (2, 13)..=(2, 15)),
            (RightParen, (2, 16)..=(2, 16)),
            (Semicolon, (2, 17)..=(2, 17)),
            (RightBrace, (3, 0)..=(3, 0)),
        ];
        assert!(check_and_render(&key, source, expected).is_empty());
    });
}

#[test]
fn multi_char_punctuation_pathological() {
    Session::with_default(|key| {
        let source = "!!== <<== !====";
        let expected = [
            Bang, BangEqual, Equal, Less, LessEqual, Equal, BangEqual, EqualEqual, Equal,
        ];
        assert!(check_and_render(&key, source, expected).is_empty());
    });
}

#[test]
fn string_literal_no_escapes() {
    Session::with_default(|key| {
        let source = r#""hey what's up""#;
        let expected = [strlit(&key, "hey what's up")];
        assert!(check_and_render(&key, source, expected).is_empty());
    });
}

#[test]
fn string_literal_escapes() {
    Session::with_default(|key| {
        let source = r#""hey \"nerd\"\n\twhat's up?""#;
        let expected = [strlit(&key, "hey \"nerd\"\n\twhat's up?")];
        assert!(check_and_render(&key, source, expected).is_empty());
    });
}

#[test]
fn string_literal_assignment() {
    Session::with_default(|key| {
        let source = r#"var s = "heya";"#;
        let expected = [
            Var,
            ident(&key, "s"),
            Equal,
            strlit(&key, "heya"),
            Semicolon,
        ];
        assert!(check_and_render(&key, source, expected).is_empty());
    });
}

#[test]
fn string_literal_including_comment() {
    Session::with_default(|key| {
        let source = r#"var s = "hey // what?"; // lol"#;
        let expected = [
            Var,
            ident(&key, "s"),
            Equal,
            strlit(&key, "hey // what?"),
            Semicolon,
        ];
        assert!(check_and_render(&key, source, expected).is_empty());
    });
}

#[test]
fn unrecognized_token() {
    Session::with_default(|key| {
        assert_snapshot!(
            check_and_render(
                &key,
                "$^&0 lol",
                [num(0.0), ident(&key, "lol")],
            ),
            @r#"
        error: unrecognized token
          --> %i0:1:1
          |
        1 | $^&0 lol
          | ^^^ this character sequence is not a valid token

        "#);
    });
}

#[test]
fn unterminated_string() {
    Session::with_default(|key| {
        assert_snapshot!(
            check_and_render(
                &key,
                indoc! {r#"
                var s = "hey;
                do(something);"#},
                [
                    Var,
                    ident(&key, "s"),
                    Equal,
                    ident(&key, "do"),
                    LeftParen,
                    ident(&key, "something"),
                    RightParen,
                    Semicolon,
                ],
            ),
             @r#"
        error: unterminated string literal
          --> %i0:1:9
          |
        1 | var s = "hey;
          |         ^^^^^ this string is missing a closing `"`

        "#);
    });
}

#[test]
fn continued_string() {
    Session::with_default(|key| {
        let source = indoc! {r#"var s = "hey \
            there";
        lmao();"#};
        let expected = [
            (Var, (0, 0)..=(0, 2)),
            (ident(&key, "s"), (0, 4)..=(0, 4)),
            (Equal, (0, 6)..=(0, 6)),
            (strlit(&key, "hey there"), (0, 8)..=(1, 9)),
            (Semicolon, (1, 10)..=(1, 10)),
            (ident(&key, "lmao"), (2, 0)..=(2, 3)),
            (LeftParen, (2, 4)..=(2, 4)),
            (RightParen, (2, 5)..=(2, 5)),
            (Semicolon, (2, 6)..=(2, 6)),
        ];
        assert!(check_and_render(&key, source, expected).is_empty());
    });
}

#[test]
fn unrecognized_escape() {
    Session::with_default(|key| {
        assert_snapshot!(
            check_and_render(
                &key,
                r#""what \even \the \fuck""#,
                [(strlit(&key, "what ven \the uck"), (0, 0)..=(0, 22))],
            ),
            @r#"
        error: unrecognized escape sequence
          --> %i0:1:7
          |
        1 | "what \even \the \fuck"
          |       ^^ this escape sequence is invalid
          |
          = note: sequence replaced with the character 'e'

        error: unrecognized escape sequence
          --> %i0:1:18
          |
        1 | "what \even \the \fuck"
          |                  ^^ this escape sequence is invalid
          |
          = note: sequence replaced with the character 'f'

        "#);
    });
}

#[test]
fn number() {
    Session::with_default(|key| {
        let source = "0 1 1.0 0033 3.500";
        let expected = [num(0.0), num(1.0), num(1.0), num(33.0), num(3.5)];
        assert!(check_and_render(&key, source, expected).is_empty());
    });
}

#[test]
fn block_comments() {
    Session::with_default(|key| {
        let source = indoc! {"
        hey /* there
        you little */ buddy"};

        let expected = [
            (ident(&key, "hey"), (0, 0)..=(0, 2)),
            (ident(&key, "buddy"), (1, 14)..=(1, 18)),
        ];
        assert!(check_and_render(&key, source, expected).is_empty());
    });
}

#[test]
fn nested_block_comments() {
    Session::with_default(|key| {
        let source = "now /* what /* even */ is */ this";
        let expected = [ident(&key, "now"), This];
        assert!(check_and_render(&key, source, expected).is_empty());
    });
}

#[test]
fn unterminated_block_comment() {
    Session::with_default(|key| {
        assert_snapshot!(
            check_and_render(
                &key,
                "ababa /* lmao",
                [ident(&key, "ababa")],
            ),
            @r#"
        error: unterminated block comment
          --> %i0:1:7
          |
        1 | ababa /* lmao
          |       ^^^^^^^^ this comment is missing a closing `*/`

        "#);
    });
}

#[test]
fn unterminated_nested_block_comment() {
    Session::with_default(|key| {
        assert_snapshot!(
            check_and_render(
                &key,
                "wee /* hehe /* yay */ wow",
                [ident(&key, "wee")],
            ),
            @r#"
        error: unterminated block comment
          --> %i0:1:5
          |
        1 | wee /* hehe /* yay */ wow
          |     ^^^^^^^^^^^^^^^^^^^^^^ this comment is missing a closing `*/`

        "#);
    });
}
