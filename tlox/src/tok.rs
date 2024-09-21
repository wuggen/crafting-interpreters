//! Lexical definitions and lexer implementation for Lox.
//!
//! [`Lexer`] is an iterator over a borrowed string, yielding `Result`s of [`Token`] and
//! [`LexerError`].
//!
//! A [`Token`] consists of a [`TokenKind`] (which includes content in the case of identifier,
//! string literal, and number tokens) and the [`Location`] (0-based line and column numbers) of
//! the first character of its occurrence in the source.
//!
//! Maybe one day I'll upgrade that to actual spans, and maybe even intern identifier names and
//! string values.

use std::fmt::{self, Display, Formatter};
use std::num::ParseFloatError;

use crate::diag::{Diag, DiagContext, DiagKind, Diagnostic};
use crate::span::{Cursor, Source, Span, Spannable, Spanned};

#[cfg(test)]
mod test;

#[derive(Debug, Clone, PartialEq)]
pub enum TokenKind {
    LeftParen,
    RightParen,
    LeftBrace,
    RightBrace,
    Comma,
    Dot,
    Minus,
    Plus,
    Semicolon,
    Slash,
    Star,
    Bang,
    BangEqual,
    Equal,
    EqualEqual,
    Greater,
    GreaterEqual,
    Less,
    LessEqual,
    Ident(String),
    StringLiteral(String),
    Number(f64),
    Boolean(bool),
    And,
    Class,
    Else,
    Fun,
    For,
    If,
    Nil,
    Or,
    Print,
    Return,
    Super,
    This,
    Var,
    While,
}

impl Display for TokenKind {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            TokenKind::LeftParen => write!(f, "("),
            TokenKind::RightParen => write!(f, ")"),
            TokenKind::LeftBrace => write!(f, "{{"),
            TokenKind::RightBrace => write!(f, "}}"),
            TokenKind::Comma => write!(f, ","),
            TokenKind::Dot => write!(f, "."),
            TokenKind::Minus => write!(f, "-"),
            TokenKind::Plus => write!(f, "+"),
            TokenKind::Semicolon => write!(f, ";"),
            TokenKind::Slash => write!(f, "/"),
            TokenKind::Star => write!(f, "*"),
            TokenKind::Bang => write!(f, "!"),
            TokenKind::BangEqual => write!(f, "!="),
            TokenKind::Equal => write!(f, "="),
            TokenKind::EqualEqual => write!(f, "=="),
            TokenKind::Greater => write!(f, ">"),
            TokenKind::GreaterEqual => write!(f, ">="),
            TokenKind::Less => write!(f, "<"),
            TokenKind::LessEqual => write!(f, "<="),
            TokenKind::Ident(s) => write!(f, "{s}"),
            TokenKind::StringLiteral(s) => write!(f, "{s:?}"),
            TokenKind::Number(x) => write!(f, "{x}"),
            TokenKind::Boolean(b) => write!(f, "{b}"),
            TokenKind::And => write!(f, "and"),
            TokenKind::Class => write!(f, "class"),
            TokenKind::Else => write!(f, "else"),
            TokenKind::Fun => write!(f, "fun"),
            TokenKind::For => write!(f, "for"),
            TokenKind::If => write!(f, "if"),
            TokenKind::Nil => write!(f, "nil"),
            TokenKind::Or => write!(f, "or"),
            TokenKind::Print => write!(f, "print"),
            TokenKind::Return => write!(f, "return"),
            TokenKind::Super => write!(f, "super"),
            TokenKind::This => write!(f, "this"),
            TokenKind::Var => write!(f, "var"),
            TokenKind::While => write!(f, "while"),
        }
    }
}

pub type Token = Spanned<TokenKind>;

pub struct Lexer<'sm, 'dcx> {
    cursor: Cursor<'sm>,
    span_start: Cursor<'sm>,
    dcx: &'dcx mut DiagContext,
    buffer: String,
}

impl<'sm, 'dcx> Lexer<'sm, 'dcx> {
    pub fn new(source: Source<'sm>, dcx: &'dcx mut DiagContext) -> Self {
        Self {
            cursor: source.cursor(),
            span_start: source.cursor(),
            dcx,
            buffer: String::new(),
        }
    }
}

impl<'sm, 'dcx> Iterator for Lexer<'sm, 'dcx> {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        self.scan()
    }
}

#[derive(Debug)]
pub struct LexerError {
    pub(crate) kind: LexerErrorKind,
    pub(crate) span: Span,
}

impl LexerError {
    pub fn kind(&self) -> &LexerErrorKind {
        &self.kind
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum LexerErrorKind {
    UnterminatedBlockComment,
    UnterminatedString,
    UnrecognizedEscapeCharacter { c: char },
    InvalidNumber { source: ParseFloatError },
    UnrecognizedToken,
}

impl Diagnostic for LexerError {
    fn into_diag(self) -> crate::diag::Diag {
        let (message, label, notes): (String, String, Vec<String>) = match self.kind {
            LexerErrorKind::UnterminatedBlockComment => (
                "unterminated block comment".into(),
                "this comment is missing a closing `*/`".into(),
                vec![],
            ),

            LexerErrorKind::UnterminatedString => (
                "unterminated string literal".into(),
                "this string is missing a closing `\"`".into(),
                vec![],
            ),

            LexerErrorKind::UnrecognizedEscapeCharacter { c } => (
                "unrecognized escape sequence".into(),
                "this escape sequence is invalid".into(),
                vec![format!("sequence replaced with the character {c:?}")],
            ),

            LexerErrorKind::InvalidNumber { source } => (
                "invalid number literal".into(),
                format!("failed to parse this number: {source}"),
                vec![],
            ),

            LexerErrorKind::UnrecognizedToken => (
                "unrecognized token".into(),
                "this character sequence is not a valid token".into(),
                vec![],
            ),
        };

        notes.into_iter().fold(
            Diag::new(DiagKind::Error, message, self.span, label),
            |diag, note| diag.with_note(note),
        )
    }
}

fn is_ident_start(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_'
}

fn is_ident_continue(c: char) -> bool {
    is_ident_start(c) || c.is_ascii_digit()
}

fn is_token_start(c: char) -> bool {
    const NON_IDENT_STARTS: &str = "(){},.-+;/*!=<>\"";
    is_ident_start(c) || c.is_ascii_digit() || NON_IDENT_STARTS.contains(c)
}

fn unescape(c: char) -> Option<char> {
    match c {
        'n' => Some('\n'),
        '"' => Some('"'),
        't' => Some('\t'),
        'r' => Some('\r'),
        '\\' => Some('\\'),
        _ => None,
    }
}

impl<'sm> Lexer<'sm, '_> {
    /// The current cursor.
    fn cursor(&self) -> Cursor<'sm> {
        self.cursor.clone()
    }

    /// The current span, from the span start to the current cursor.
    fn span(&self) -> Span {
        self.cursor.span_from(&self.span_start).unwrap()
    }

    /// The current contents of the buffer.
    fn buffer(&self) -> &str {
        &self.buffer
    }

    /// Clear the buffer.
    fn clear_buffer(&mut self) {
        self.buffer.clear();
    }

    /// Set the span start to the given cursor.
    fn set_span_start(&mut self, start: Cursor<'sm>) {
        self.span_start = start;
    }

    /// Set the token start location to the current cursor.
    fn reset_span_start(&mut self) {
        self.set_span_start(self.cursor.clone());
    }

    /// Advance over a character, but do not add it to the buffer.
    ///
    /// Returns the skipped character, or `None` if at the end of the input.
    fn skip(&mut self) -> Option<char> {
        self.cursor.advance()
    }

    /// Advance the cursor and add the advanced-over character to the buffer.
    ///
    /// Returns the advanced-over character, or `None` if at the end of the input.
    fn advance(&mut self) -> Option<char> {
        self.skip().inspect(|c| {
            self.buffer.push(*c);
        })
    }

    /// Peek at the next character in the input, but do not advance the cursor or modify the
    /// buffer.
    fn peek(&mut self) -> Option<char> {
        self.cursor.peek()
    }

    /// Advance over the next character if it is exactly `expected`.
    ///
    /// Does not modify the cursor if the next character does not match.
    ///
    /// Returns whether the next character matched the expected character.
    fn match_next(&mut self, expected: char) -> bool {
        self.advance_if(|c| c == expected).is_some()
    }

    /// Advance over and buffer the next character if it satisfies the given predicate.
    ///
    /// Does not modify the cursor if the next character does not satisfy the predicate.
    ///
    /// Returns the advanced-over character, or `None` if either the next character does not
    /// satisfy the predicate or the cursor is at the end of the input.
    fn advance_if(&mut self, pred: impl FnOnce(char) -> bool) -> Option<char> {
        if pred(self.peek()?) {
            self.advance()
        } else {
            None
        }
    }

    /// Advance over and buffer as many consecutive characters as satisfy the predicate.
    fn advance_while(&mut self, mut pred: impl FnMut(char) -> bool) {
        while self.peek().map(&mut pred).unwrap_or(false) {
            self.advance();
        }
    }

    /// Skip (do not buffer) as many consecutive characters as satisfy the predicate.
    fn skip_while(&mut self, mut pred: impl FnMut(char) -> bool) {
        while self.peek().map(&mut pred).unwrap_or(false) {
            self.skip();
        }
    }

    /// Advance over and buffer as many consecutive characters as fail the predicate.
    fn advance_until(&mut self, mut pred: impl FnMut(char) -> bool) {
        self.advance_while(move |c| !pred(c));
    }

    /// Skip (do not buffer) as many consecutive characters as fail the predicate.
    fn skip_until(&mut self, mut pred: impl FnMut(char) -> bool) {
        self.skip_while(move |c| !pred(c));
    }

    /// Skip characters until a non-whitespace character is reached.
    fn skip_whitespace(&mut self) {
        self.skip_while(char::is_whitespace);
    }

    /// Skip characters until a newline character is reached.
    fn skip_to_newline(&mut self) {
        self.skip_until(|c| c == '\n');
    }

    /// Skip over a block comment.
    ///
    /// This assumes that the cursor is at the first character of the comment body, i.e. after the
    /// opening `/*`. It will skip characters until the matching `*/`, and leave the cursor one
    /// character after the closer.
    ///
    /// This will recursively invoke itself on nested block comments.
    fn skip_block_comment(&mut self) {
        loop {
            match self.skip() {
                None => {
                    self.emit_error(LexerErrorKind::UnterminatedBlockComment);
                    break;
                }

                Some('/') => {
                    if self.peek() == Some('*') {
                        let outer_comment_start = self.span_start.clone();
                        let mut inner_comment_start = self.cursor();
                        inner_comment_start.retract();
                        self.set_span_start(inner_comment_start);

                        self.skip();
                        self.skip_block_comment();

                        self.set_span_start(outer_comment_start);
                    }
                }

                Some('*') => {
                    if self.peek() == Some('/') {
                        self.skip();
                        break;
                    }
                }

                _ => {}
            }
        }
    }

    /// Advance over and buffer consecutive unrecognized characters.
    ///
    /// This buffers characters until one is reached that is either whitespace or a valid token
    /// start character.
    fn advance_unrecognized(&mut self) {
        self.advance_until(|c| is_token_start(c) || c.is_whitespace());
    }

    /// Create a token of the given type with the current span.
    fn token(&self, ty: TokenKind) -> Option<Token> {
        Some(ty.spanned(self.span()))
    }

    /// Create a token with the current span, constructing the token type from the current buffer.
    fn token_with_buffer(&self, f: impl FnOnce(String) -> TokenKind) -> Option<Token> {
        self.token(f(self.buffer().into()))
    }

    /// Emit an error with the given kind, using the current span.
    fn emit_error(&mut self, kind: LexerErrorKind) {
        self.emit_error_with_span(kind, self.span());
    }

    /// Emit an error with the given kind and the given span.
    fn emit_error_with_span(&mut self, kind: LexerErrorKind, span: Span) {
        self.dcx.emit(LexerError { kind, span });
    }

    /// Scan and de-escape a string literal.
    ///
    /// This assumes that the cursor is at the first character of the string body, i.e. after the
    /// opening `"`, and that the span start is exactly the opening `"`. When it returns, the
    /// cursor will be at the character after the closing `"`.
    fn scan_string(&mut self) -> Option<Token> {
        use LexerErrorKind::*;

        self.clear_buffer();

        loop {
            let c = match self.skip() {
                None => {
                    self.emit_error(UnterminatedString);
                    break None;
                }
                Some(c) => c,
            };

            match c {
                '"' => {
                    break self.token_with_buffer(TokenKind::StringLiteral);
                }

                '\\' => match self.peek() {
                    None => {
                        self.emit_error(UnterminatedString);
                        break None;
                    }

                    Some('\n') => {
                        self.skip_whitespace();
                    }

                    Some(c) => {
                        if let Some(c) = unescape(c) {
                            self.buffer.push(c);
                            self.skip();
                        } else {
                            let mut start = self.cursor();
                            start.retract();
                            self.skip();

                            let span = self.cursor().span_from(&start).unwrap();
                            self.emit_error_with_span(UnrecognizedEscapeCharacter { c }, span);
                        }
                    }
                },

                '\n' => {
                    let mut end = self.cursor();
                    end.retract();
                    let span = end.span_from(&self.span_start).unwrap();

                    self.emit_error_with_span(UnterminatedString, span);
                    break None;
                }

                c => {
                    self.buffer.push(c);
                }
            }
        }
    }

    /// Scan an identifier or keyword token.
    ///
    /// This assumes that the first character of the token is already advanced over and buffered.
    /// It will scan until a non-identifier character is encountered. If the resulting buffer
    /// matches a keyword, the appropriate token will be returned; otherwise, returns an identifier
    /// token.
    fn scan_ident(&mut self) -> Option<Token> {
        use TokenKind::*;

        self.advance_while(is_ident_continue);
        match self.buffer() {
            "and" => self.token(And),
            "class" => self.token(Class),
            "else" => self.token(Else),
            "false" => self.token(Boolean(false)),
            "true" => self.token(Boolean(true)),
            "fun" => self.token(Fun),
            "for" => self.token(For),
            "if" => self.token(If),
            "nil" => self.token(Nil),
            "or" => self.token(Or),
            "print" => self.token(Print),
            "return" => self.token(Return),
            "super" => self.token(Super),
            "this" => self.token(This),
            "var" => self.token(Var),
            "while" => self.token(While),
            _ => self.token_with_buffer(Ident),
        }
    }

    /// Scan a number token.
    fn scan_number(&mut self) -> Option<Token> {
        self.advance_while(|c| c.is_ascii_digit());

        if self.peek() == Some('.') {
            self.advance();
            self.advance_while(|c| c.is_ascii_digit());
        }

        match self.buffer().parse::<f64>() {
            Ok(n) => self.token(TokenKind::Number(n)),
            Err(e) => {
                self.emit_error(LexerErrorKind::InvalidNumber { source: e });
                None
            }
        }
    }

    /// Scan from the current cursor, yielding a single token or error.
    ///
    /// Returns `None` if the end of the input has been reached.
    fn scan(&mut self) -> Option<Token> {
        use TokenKind::*;

        loop {
            self.skip_whitespace();
            self.clear_buffer();
            self.reset_span_start();

            let c = match self.advance() {
                None => break None,
                Some(c) => c,
            };

            break match c {
                '(' => self.token(LeftParen),
                ')' => self.token(RightParen),
                '{' => self.token(LeftBrace),
                '}' => self.token(RightBrace),
                ',' => self.token(Comma),
                '.' => self.token(Dot),
                '-' => self.token(Minus),
                '+' => self.token(Plus),
                ';' => self.token(Semicolon),
                '*' => self.token(Star),

                '/' => match self.peek() {
                    Some('/') => {
                        self.skip_to_newline();
                        continue;
                    }

                    Some('*') => {
                        self.skip();
                        self.skip_block_comment();
                        continue;
                    }

                    _ => self.token(Slash),
                },

                '!' => {
                    if self.match_next('=') {
                        self.token(BangEqual)
                    } else {
                        self.token(Bang)
                    }
                }

                '=' => {
                    if self.match_next('=') {
                        self.token(EqualEqual)
                    } else {
                        self.token(Equal)
                    }
                }

                '>' => {
                    if self.match_next('=') {
                        self.token(GreaterEqual)
                    } else {
                        self.token(Greater)
                    }
                }

                '<' => {
                    if self.match_next('=') {
                        self.token(LessEqual)
                    } else {
                        self.token(Less)
                    }
                }

                '"' => {
                    if let tok @ Some(_) = self.scan_string() {
                        tok
                    } else {
                        continue;
                    }
                }

                c if is_ident_start(c) => self.scan_ident(),

                c if c.is_ascii_digit() => {
                    if let tok @ Some(_) = self.scan_number() {
                        tok
                    } else {
                        continue;
                    }
                }

                _ => {
                    self.advance_unrecognized();
                    self.emit_error(LexerErrorKind::UnrecognizedToken);
                    continue;
                }
            };
        }
    }
}
