//! Lexical definitions and lexer implementation for Lox.
//!
//! [`Lexer`] is an iterator over a borrowed string, yielding `Result`s of [`Token`] and
//! [`LexerError`].
//!
//! A [`Token`] consists of a [`TokenType`] (which includes content in the case of identifier,
//! string literal, and number tokens) and the [`Location`] (0-based line and column numbers) of
//! the first character of its occurrence in the source.
//!
//! Maybe one day I'll upgrade that to actual spans, and maybe even intern identifier names and
//! string values.

use std::collections::VecDeque;
use std::fmt::{self, Display, Formatter};
use std::iter::Peekable;
use std::num::ParseFloatError;
use std::str::Chars;

#[cfg(test)]
mod test;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Location {
    pub line: usize,
    pub column: usize,
}

impl Display for Location {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}:{}", self.line + 1, self.column + 1)
    }
}
#[derive(Debug, Clone, PartialEq)]
pub enum TokenType {
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

impl Display for TokenType {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            TokenType::LeftParen => write!(f, "("),
            TokenType::RightParen => write!(f, ")"),
            TokenType::LeftBrace => write!(f, "{{"),
            TokenType::RightBrace => write!(f, "}}"),
            TokenType::Comma => write!(f, ","),
            TokenType::Dot => write!(f, "."),
            TokenType::Minus => write!(f, "-"),
            TokenType::Plus => write!(f, "+"),
            TokenType::Semicolon => write!(f, ";"),
            TokenType::Slash => write!(f, "/"),
            TokenType::Star => write!(f, "*"),
            TokenType::Bang => write!(f, "!"),
            TokenType::BangEqual => write!(f, "!="),
            TokenType::Equal => write!(f, "="),
            TokenType::EqualEqual => write!(f, "=="),
            TokenType::Greater => write!(f, ">"),
            TokenType::GreaterEqual => write!(f, ">="),
            TokenType::Less => write!(f, "<"),
            TokenType::LessEqual => write!(f, "<="),
            TokenType::Ident(s) => write!(f, "{s}"),
            TokenType::StringLiteral(s) => write!(f, "{s:?}"),
            TokenType::Number(x) => write!(f, "{x}"),
            TokenType::Boolean(b) => write!(f, "{b}"),
            TokenType::And => write!(f, "and"),
            TokenType::Class => write!(f, "class"),
            TokenType::Else => write!(f, "else"),
            TokenType::Fun => write!(f, "fun"),
            TokenType::For => write!(f, "for"),
            TokenType::If => write!(f, "if"),
            TokenType::Nil => write!(f, "nil"),
            TokenType::Or => write!(f, "or"),
            TokenType::Print => write!(f, "print"),
            TokenType::Return => write!(f, "return"),
            TokenType::Super => write!(f, "super"),
            TokenType::This => write!(f, "this"),
            TokenType::Var => write!(f, "var"),
            TokenType::While => write!(f, "while"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Token {
    pub ty: TokenType,
    pub location: Location,
}

pub struct Lexer<'a> {
    source: Peekable<Chars<'a>>,
    buffer: String,
    location: Location,
    line: usize,
    column: usize,
    queued: VecDeque<Result<Token, LexerError>>,
}

impl<'a> Lexer<'a> {
    pub fn new(source: &'a str) -> Self {
        Self {
            source: source.chars().peekable(),
            buffer: String::new(),
            location: Location { line: 0, column: 0 },
            line: 0,
            column: 0,
            queued: VecDeque::new(),
        }
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Result<Token, LexerError>;

    fn next(&mut self) -> Option<Self::Item> {
        self.scan()
    }
}

#[derive(Debug, thiserror::Error)]
#[error("Error at {location}: {kind}")]
pub struct LexerError {
    pub(crate) kind: LexerErrorKind,
    pub(crate) location: Location,
}

impl LexerError {
    pub fn kind(&self) -> &LexerErrorKind {
        &self.kind
    }

    pub fn location(&self) -> Location {
        self.location
    }
}

#[derive(Debug, PartialEq, Eq, thiserror::Error)]
pub enum LexerErrorKind {
    #[error("unterminated block comment")]
    UnterminatedBlockComment,

    #[error("unterminated string")]
    UnterminatedString,

    #[error("unrecognized escape character")]
    UnrecognizedEscapeCharacter,

    #[error("invalid number literal: {source}")]
    InvalidNumber { source: ParseFloatError },

    #[error("unrecognized token {token:?}")]
    UnrecognizedToken { token: String },
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

impl Lexer<'_> {
    /// The `Location` of the character that will be next advanced over.
    fn cursor(&self) -> Location {
        Location {
            line: self.line,
            column: self.column,
        }
    }

    /// The current contents of the buffer.
    fn buffer(&self) -> &str {
        &self.buffer
    }

    /// Clear the buffer.
    fn clear_buffer(&mut self) {
        self.buffer.clear();
    }

    /// Set the token start location to the current value of [`cursor()`].
    fn reset_token_start(&mut self) {
        self.location = self.cursor();
    }

    /// Advance over a character, but do not add it to the buffer.
    ///
    /// Returns the skipped character, or `None` if at the end of the input.
    fn skip(&mut self) -> Option<char> {
        let c = self.source.next()?;
        if c == '\n' {
            self.line += 1;
            self.column = 0;
        } else {
            self.column += 1;
        }
        Some(c)
    }

    /// Advance the cursor and add the advanced-over character to the buffer.
    ///
    /// Returns the advanced-over character, or `None` if at the end of the input.
    fn advance(&mut self) -> Option<char> {
        self.skip().map(|c| {
            self.buffer.push(c);
            c
        })
    }

    /// Peek at the next character in the input, but do not advance the cursor or modify the
    /// buffer.
    fn peek(&mut self) -> Option<char> {
        self.source.peek().copied()
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
                    self.queue_error_at_cursor(LexerErrorKind::UnterminatedBlockComment);
                    break;
                }

                Some('/') => {
                    if self.peek() == Some('*') {
                        self.skip();
                        self.skip_block_comment();
                    }
                }

                Some('*') => {
                    if self.peek() == Some('/') {
                        self.skip();
                        break;
                    }
                }

                _ => (),
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

    /// Create a token of the given type with the current token start location.
    fn token(&self, ty: TokenType) -> Option<Result<Token, LexerError>> {
        Some(Ok(Token {
            ty,
            location: self.location,
        }))
    }

    /// Create a token with the current start location, constructing the token type from the
    /// current buffer.
    fn token_with_buffer(
        &self,
        f: impl FnOnce(String) -> TokenType,
    ) -> Option<Result<Token, LexerError>> {
        self.token(f(self.buffer().into()))
    }

    /// Create an error with the given message and the current start location.
    fn error(&self, kind: LexerErrorKind) -> Option<Result<Token, LexerError>> {
        Some(Err(LexerError {
            kind,
            location: self.location,
        }))
    }

    /// Create an error with the given message and the current cursor location.
    fn error_at_cursor(&self, kind: LexerErrorKind) -> Option<Result<Token, LexerError>> {
        Some(Err(LexerError {
            kind,
            location: self.cursor(),
        }))
    }

    /// Queue a token to be yielded before continuing to scan.
    ///
    /// The queued token will have the start location at the time of calling this function, and a
    /// type constructed from the buffer at the time of calling this function.
    fn queue_token_with_buffer(&mut self, f: impl FnOnce(String) -> TokenType) {
        let tok = self.token_with_buffer(f).unwrap();
        self.queued.push_back(tok);
    }

    /// Queue an error to be yielded before continuing to scan.
    ///
    /// The queued error will have the start location at the time of calling this function.
    fn queue_error(&mut self, kind: LexerErrorKind) {
        let res = self.error(kind).unwrap();
        self.queued.push_back(res);
    }

    /// Queue an error to be yielded before continuing to scan.
    ///
    /// The queued error will have the cursor location at the time of calling this function.
    fn queue_error_at_cursor(&mut self, kind: LexerErrorKind) {
        let res = self.error_at_cursor(kind).unwrap();
        self.queued.push_back(res);
    }

    /// Scan and de-escape a string literal.
    ///
    /// This assumes that the cursor is at the first character of the string body, i.e. after the
    /// opening `"`. When it returns, the cursor will be at the character after the closing `"`.
    ///
    /// Since this function can encounter multiple errors in the course of scanning a single token,
    /// it queues all of its errors and the final string token, rather than simply returning them.
    fn scan_string(&mut self) {
        use LexerErrorKind::*;

        self.clear_buffer();

        loop {
            let c = match self.skip() {
                None => {
                    self.queue_error(UnterminatedString);
                    break;
                }
                Some(c) => c,
            };

            match c {
                '"' => {
                    self.queue_token_with_buffer(TokenType::StringLiteral);
                    break;
                }

                '\\' => match self.peek() {
                    None => {
                        self.queue_error(UnterminatedString);
                        break;
                    }

                    Some('\n') => {
                        self.skip_whitespace();
                    }

                    Some(c) => {
                        if let Some(c) = unescape(c) {
                            self.buffer.push(c);
                            self.skip();
                        } else {
                            self.queue_error_at_cursor(UnrecognizedEscapeCharacter);
                            self.skip();
                        }
                    }
                },

                '\n' => {
                    self.queue_error(UnterminatedString);
                    break;
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
    fn scan_ident(&mut self) -> Option<Result<Token, LexerError>> {
        use TokenType::*;

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
    fn scan_number(&mut self) -> Option<Result<Token, LexerError>> {
        self.advance_while(|c| c.is_ascii_digit());

        if self.peek() == Some('.') {
            self.advance();
            self.advance_while(|c| c.is_ascii_digit());
        }

        let n = match self.buffer().parse::<f64>() {
            Ok(n) => n,
            Err(e) => return self.error(LexerErrorKind::InvalidNumber { source: e }),
        };

        self.token(TokenType::Number(n))
    }

    /// Scan from the current cursor, yielding a single token or error.
    ///
    /// Returns `None` if the end of the input has been reached.
    fn scan(&mut self) -> Option<Result<Token, LexerError>> {
        use TokenType::*;

        loop {
            if let Some(res) = self.queued.pop_front() {
                break Some(res);
            }

            self.skip_whitespace();
            self.clear_buffer();
            self.reset_token_start();

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
                    self.scan_string();
                    continue;
                }

                c if is_ident_start(c) => self.scan_ident(),

                c if c.is_ascii_digit() => self.scan_number(),

                _ => {
                    self.advance_unrecognized();
                    self.error(LexerErrorKind::UnrecognizedToken {
                        token: self.buffer().into(),
                    })
                }
            };
        }
    }
}
