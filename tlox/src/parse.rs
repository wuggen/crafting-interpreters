//! Parser for Lox.

use std::fmt::{self, Display, Formatter};
use std::iter::Peekable;

use crate::syn::{Literal, SynTree, UnopSym};
use crate::tok::{LexerError, LexerErrorKind, Location, Token, TokenType};

#[derive(Debug)]
pub struct Parser<T: Iterator<Item = Result<Token, LexerError>>> {
    tokens: Peekable<T>,
    errors: Vec<ParserError>,
}

use crate::tok::TokenType::*;

impl<T> Parser<T>
where
    T: Iterator<Item = Result<Token, LexerError>>,
{
    pub fn new(tokens: T) -> Self {
        Self {
            tokens: tokens.peekable(),
            errors: Vec::new(),
        }
    }

    // Grammar:
    //
    // expression -> equality
    // equality -> comparison (eq_binop comparison)*
    // comparison -> term (comp_binop term)*
    // term -> factor (add_binop factor)*
    // factor -> unary (mul_binop unary)*
    // unary -> unop unary | atom
    // atom -> NUMBER | STRING | bool | "nil" | "(" expression ")"
    //
    // eq_binop -> "!=" | "=="
    // comp_binop -> "<" | "<=" | ">" | ">="
    // add_binop -> "+" | "-"
    // mul_binop -> "*" | "/"
    // unop -> "!" | "-"
    // bool -> "true" | "false"

    fn queue_lexer_errors(&mut self) {
        while let Some(res) = self.tokens.peek() {
            if res.is_err() {
                self.errors
                    .push(ParserError::lexer(self.tokens.next().unwrap().unwrap_err()));
            } else {
                break;
            }
        }
    }

    fn peek(&mut self) -> Option<&Token> {
        self.queue_lexer_errors();
        self.tokens.peek().map(|res| res.as_ref().unwrap())
    }

    fn advance(&mut self) -> Option<Token> {
        self.queue_lexer_errors();
        self.tokens.next().map(|res| res.unwrap())
    }

    fn peek_type(&mut self) -> Option<&TokenType> {
        self.peek().map(|t| &t.ty)
    }

    fn advance_if(
        &mut self,
        p: impl FnOnce(&TokenType) -> bool,
        err: impl FnOnce(Option<&Token>, &mut Vec<ParserError>),
    ) -> Option<Token> {
        self.queue_lexer_errors();
        match self.tokens.peek().map(|res| res.as_ref().unwrap()) {
            None => {
                err(None, &mut self.errors);
                None
            }

            Some(tok @ Token { ty, .. }) => {
                if p(ty) {
                    self.advance()
                } else {
                    err(Some(tok), &mut self.errors);
                    None
                }
            }
        }
    }

    fn match_next(&mut self, ty: &TokenType) -> Option<Location> {
        self.advance_if(
            |t| t == ty,
            |tok, errs| match tok {
                Some(t) => {
                    errs.push(ParserError::unexpected_token(
                        Expected::Token(ty.clone()),
                        t.clone(),
                    ));
                }

                None => {
                    errs.push(ParserError::unexpected_eof(Expected::Token(ty.clone())));
                }
            },
        )
        .map(|t| t.location)
    }

    fn parse_expression(&mut self) -> Option<SynTree> {
        self.parse_equality()
    }

    fn parse_equality(&mut self) -> Option<SynTree> {
        todo!()
    }

    fn parse_comparison(&mut self) -> Option<SynTree> {
        todo!()
    }

    fn parse_term(&mut self) -> Option<SynTree> {
        todo!()
    }

    fn parse_factor(&mut self) -> Option<SynTree> {
        todo!()
    }

    fn parse_unary(&mut self) -> Option<SynTree> {
        if let Some(ty) = self.peek_type() {
            let op = match ty {
                Bang => UnopSym::Not,
                Minus => UnopSym::Neg,
                _ => {
                    return self.parse_atom();
                }
            };

            let Token { location, .. } = self.advance().unwrap();
            let oprd = self.parse_unary()?;

            Some(SynTree::unop(location, op, oprd))
        } else {
            self.errors
                .push(ParserError::unexpected_eof(Expected::Expression));
            None
        }
    }

    fn parse_atom(&mut self) -> Option<SynTree> {
        if let Some(Token { ty, location }) = self.advance() {
            match ty {
                Number(n) => Some(SynTree::literal(location, Literal::Num(n))),
                StringLiteral(s) => Some(SynTree::literal(location, Literal::Str(s))),
                Boolean(b) => Some(SynTree::literal(location, Literal::Bool(b))),
                Nil => Some(SynTree::literal(location, Literal::Nil)),
                LeftParen => {
                    let val = self.parse_expression()?;
                    self.match_next(&RightParen);
                    Some(SynTree { location, ..val })
                }
                ty => {
                    let tok = Token { location, ty };
                    self.errors
                        .push(ParserError::unexpected_token(Expected::Expression, tok));
                    None
                }
            }
        } else {
            self.errors
                .push(ParserError::unexpected_eof(Expected::Expression));
            None
        }
    }

    pub fn parse(&mut self) -> Result<SynTree, Vec<ParserError>> {
        if let Some(tree) = self.parse_expression() {
            Ok(tree)
        } else {
            let mut errors = Vec::new();
            std::mem::swap(&mut errors, &mut self.errors);
            Err(errors)
        }
    }
}

#[derive(Debug, thiserror::Error)]
pub struct ParserError {
    kind: ParserErrorKind,
    location: Option<Location>,
}

impl Display for ParserError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "error")?;
        if let Some(location) = self.location {
            write!(f, " at {location}")?;
        }
        write!(f, ": {}", self.kind)
    }
}

impl ParserError {
    fn lexer(error: LexerError) -> Self {
        let LexerError { kind, location } = error;
        Self {
            kind: ParserErrorKind::Lexer { source: kind },
            location: Some(location),
        }
    }

    fn unexpected_token(expected: Expected, found: Token) -> Self {
        let Token { ty, location } = found;
        Self {
            kind: ParserErrorKind::UnexpectedToken {
                expected,
                found: ty,
            },
            location: Some(location),
        }
    }

    fn unexpected_eof(expected: Expected) -> Self {
        Self {
            kind: ParserErrorKind::UnexpectedEndOfInput { expected },
            location: None,
        }
    }
}

#[derive(Debug, PartialEq, thiserror::Error)]
pub enum ParserErrorKind {
    #[error(transparent)]
    Lexer { source: LexerErrorKind },

    #[error("unexpected token; expected {expected}, found `{found}`")]
    UnexpectedToken {
        expected: Expected,
        found: TokenType,
    },

    #[error("unexpected end of input; expected {expected}")]
    UnexpectedEndOfInput { expected: Expected },
}

#[derive(Debug, Clone, PartialEq, thiserror::Error)]
pub enum Expected {
    #[error("expression (number, string, boolean, nil, unary operation, binary operation, parenthesized expression)")]
    Expression,

    #[error("token {0}")]
    Token(TokenType),
}
