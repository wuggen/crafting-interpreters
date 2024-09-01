use super::*;

use LexerErrorKind::*;

use std::fmt::Debug;

trait TokenTestable {
    fn check(&self, tok: &Token) -> bool;
}

trait TokenErrorTestable {
    fn check_err(&self, err: &LexerError) -> bool;
}

trait TokenResTestable {
    fn check_res(&self, res: &Result<Token, LexerError>) -> bool;
}

impl TokenTestable for TokenType {
    fn check(&self, tok: &Token) -> bool {
        self == &tok.ty
    }
}

impl TokenTestable for (usize, usize) {
    fn check(&self, tok: &Token) -> bool {
        self.0 == tok.location.line && self.1 == tok.location.column
    }
}

impl TokenErrorTestable for (usize, usize) {
    fn check_err(&self, err: &LexerError) -> bool {
        self.0 == err.location.line && self.1 == err.location.column
    }
}

impl TokenErrorTestable for LexerErrorKind {
    fn check_err(&self, err: &LexerError) -> bool {
        self == &err.kind
    }
}

impl<A, B> TokenErrorTestable for (A, B)
where
    A: TokenErrorTestable,
    B: TokenErrorTestable,
{
    fn check_err(&self, err: &LexerError) -> bool {
        self.0.check_err(err) && self.1.check_err(err)
    }
}

impl<A, B> TokenTestable for (A, B)
where
    A: TokenTestable,
    B: TokenTestable,
{
    fn check(&self, tok: &Token) -> bool {
        self.0.check(tok) && self.1.check(tok)
    }
}

impl<T> TokenResTestable for T
where
    T: TokenTestable,
{
    fn check_res(&self, res: &Result<Token, LexerError>) -> bool {
        res.as_ref().map(|t| self.check(t)).unwrap_or(false)
    }
}

impl<T, E> TokenResTestable for Result<T, E>
where
    T: TokenTestable,
    E: TokenErrorTestable,
{
    fn check_res(&self, res: &Result<Token, LexerError>) -> bool {
        match (self, res) {
            (Ok(_), Err(_)) | (Err(_), Ok(_)) => false,
            (Ok(t1), Ok(t2)) => t1.check(t2),
            (Err(e1), Err(e2)) => e1.check_err(e2),
        }
    }
}

fn check_scan<I, T>(source: &str, expected: I) -> bool
where
    I: IntoIterator<Item = T>,
    T: TokenResTestable + Debug,
{
    let mut success = true;
    let mut lexer = Lexer::new(source);
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
                if !expected.check_res(&tok) {
                    eprintln!("Token mismatch: expected {expected:?}, got {tok:?}");
                    success = false;
                }
            }
        }
    }

    success
}

use TokenType::*;

fn ident(s: impl Into<String>) -> TokenType {
    Ident(s.into())
}

fn strlit(s: impl Into<String>) -> TokenType {
    StringLiteral(s.into())
}

fn num(n: f64) -> TokenType {
    Number(n)
}

fn unrecognized(token: impl Into<String>) -> LexerErrorKind {
    UnrecognizedToken {
        token: token.into(),
    }
}

#[test]
fn keywords() {
    let source = "and or true false if else while for fun print var this super class nil return";
    let expected = [
        (And, (0, 0)),
        (Or, (0, 4)),
        (Boolean(true), (0, 7)),
        (Boolean(false), (0, 12)),
        (If, (0, 18)),
        (Else, (0, 21)),
        (While, (0, 26)),
        (For, (0, 32)),
        (Fun, (0, 36)),
        (Print, (0, 40)),
        (Var, (0, 46)),
        (This, (0, 50)),
        (Super, (0, 55)),
        (Class, (0, 61)),
        (Nil, (0, 67)),
        (Return, (0, 71)),
    ];

    assert!(check_scan(source, expected));
}

#[test]
fn one_char_punctuation() {
    let source = "(){},.-+;*";
    let expected = [
        (LeftParen, (0, 0)),
        (RightParen, (0, 1)),
        (LeftBrace, (0, 2)),
        (RightBrace, (0, 3)),
        (Comma, (0, 4)),
        (Dot, (0, 5)),
        (Minus, (0, 6)),
        (Plus, (0, 7)),
        (Semicolon, (0, 8)),
        (Star, (0, 9)),
    ];
    assert!(check_scan(source, expected));
}

#[test]
fn multi_char_punctuation() {
    let source = "! != = == > >= < <=";
    let expected = [
        (Bang, (0, 0)),
        (BangEqual, (0, 2)),
        (Equal, (0, 5)),
        (EqualEqual, (0, 7)),
        (Greater, (0, 10)),
        (GreaterEqual, (0, 12)),
        (Less, (0, 15)),
        (LessEqual, (0, 17)),
    ];
    assert!(check_scan(source, expected));
}

#[test]
fn idents() {
    let source = "hey what num_3 _unused __ n1234 fortune iface orange";
    let expected = [
        ident("hey"),
        ident("what"),
        ident("num_3"),
        ident("_unused"),
        ident("__"),
        ident("n1234"),
        ident("fortune"),
        ident("iface"),
        ident("orange"),
    ];
    assert!(check_scan(source, expected));
}

#[test]
fn mixed_punctuation_idents_keywords_newlines_comments() {
    let source = r#"if (hey) {
    var x = lmao; // what even
    now(what,lol);
} // as if
  // lol"#;
    let expected = [
        (If, (0, 0)),
        (LeftParen, (0, 3)),
        (ident("hey"), (0, 4)),
        (RightParen, (0, 7)),
        (LeftBrace, (0, 9)),
        (Var, (1, 4)),
        (ident("x"), (1, 8)),
        (Equal, (1, 10)),
        (ident("lmao"), (1, 12)),
        (Semicolon, (1, 16)),
        (ident("now"), (2, 4)),
        (LeftParen, (2, 7)),
        (ident("what"), (2, 8)),
        (Comma, (2, 12)),
        (ident("lol"), (2, 13)),
        (RightParen, (2, 16)),
        (Semicolon, (2, 17)),
        (RightBrace, (3, 0)),
    ];
    assert!(check_scan(source, expected));
}

#[test]
fn multi_char_punctuation_pathological() {
    let source = "!!== <<== !====";
    let expected = [
        Bang, BangEqual, Equal, Less, LessEqual, Equal, BangEqual, EqualEqual, Equal,
    ];
    assert!(check_scan(source, expected));
}

#[test]
fn string_literal_no_escapes() {
    let source = r#""hey what's up""#;
    let expected = [strlit("hey what's up")];
    assert!(check_scan(source, expected));
}

#[test]
fn string_literal_escapes() {
    let source = r#""hey \"nerd\"\n\twhat's up?""#;
    let expected = [strlit(
        r#"hey "nerd"
	what's up?"#,
    )];
    assert!(check_scan(source, expected));
}

#[test]
fn string_literal_assignment() {
    let source = r#"var s = "heya";"#;
    let expected = [Var, ident("s"), Equal, strlit("heya"), Semicolon];
    assert!(check_scan(source, expected));
}

#[test]
fn string_literal_including_comment() {
    let source = r#"var s = "hey // what?"; // lol"#;
    let expected = [Var, ident("s"), Equal, strlit("hey // what?"), Semicolon];
    assert!(check_scan(source, expected));
}

#[test]
fn unrecognized_token() {
    let source = "%^&0 lol";
    let expected = [
        Err((unrecognized("%^&"), (0, 0))),
        Ok(num(0.0)),
        Ok(ident("lol")),
    ];
    assert!(check_scan(source, expected));
}

#[test]
fn unterminated_string() {
    let source = r#"var s = "hey;
do(something);"#;
    let expected = [
        Ok(Var),
        Ok(ident("s")),
        Ok(Equal),
        Err(UnterminatedString),
        Ok(ident("do")),
        Ok(LeftParen),
        Ok(ident("something")),
        Ok(RightParen),
        Ok(Semicolon),
    ];
    assert!(check_scan(source, expected));
}

#[test]
fn continued_string() {
    let source = r#"var s = "hey \
    there";
lmao();"#;
    let expected = [
        (Var, (0, 0)),
        (ident("s"), (0, 4)),
        (Equal, (0, 6)),
        (strlit("hey there"), (0, 8)),
        (Semicolon, (1, 10)),
        (ident("lmao"), (2, 0)),
        (LeftParen, (2, 4)),
        (RightParen, (2, 5)),
        (Semicolon, (2, 6)),
    ];
    assert!(check_scan(source, expected));
}

#[test]
fn unrecognized_escape() {
    let source = r#""what \even \the \fuck""#;
    let expected = [
        Err((UnrecognizedEscapeCharacter, (0, 7))),
        Err((UnrecognizedEscapeCharacter, (0, 18))),
        Ok((strlit("what ven \the uck"), (0, 0))),
    ];
    assert!(check_scan(source, expected));
}

#[test]
fn number() {
    let source = "0 1 1.0 0033 3.500";
    let expected = [num(0.0), num(1.0), num(1.0), num(33.0), num(3.5)];
    assert!(check_scan(source, expected));
}

#[test]
fn block_comments() {
    let source = "hey /* there\nyou little */ buddy";
    let expected = [(ident("hey"), (0, 0)), (ident("buddy"), (1, 14))];
    assert!(check_scan(source, expected));
}

#[test]
fn nested_block_comments() {
    let source = "now /* what /* even */ is */ this";
    let expected = [ident("now"), This];
    assert!(check_scan(source, expected));
}

#[test]
fn unterminated_block_comment() {
    let source = "ababa /* lmao";
    let expected = [Ok(ident("ababa")), Err(UnterminatedBlockComment)];
    assert!(check_scan(source, expected));
}

#[test]
fn unterminated_nested_block_comment() {
    let source = "wee /* hehe /* yay */ wow";
    let expected = [Ok(ident("wee")), Err(UnterminatedBlockComment)];
    assert!(check_scan(source, expected));
}
