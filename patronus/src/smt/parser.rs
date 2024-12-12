// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::expr::{Context, ExprRef};
use crate::smt::parser::LexState::Searching;
use rustc_hash::FxHashMap;
use std::fmt::{Debug, Formatter};
use std::io::{BufRead, Read};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum SmtParserError {
    #[error("[smt] unsupported feature {0}")]
    Unsupported(String),
    #[error("[smt] I/O operation failed")]
    Io(#[from] std::io::Error),
}

type Result<T> = std::result::Result<T, SmtParserError>;

type SymbolTable = FxHashMap<String, ExprRef>;

pub fn parse_expr(
    ctx: &mut Context,
    st: &mut SymbolTable,
    input: &mut impl BufRead,
) -> Result<ExprRef> {
    todo!()
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Lexer
////////////////////////////////////////////////////////////////////////////////////////////////////

struct Lexer<'a> {
    input: &'a [u8],
    state: LexState,
    pos: usize,
}

enum Token<'a> {
    Open,
    Close,
    Value(&'a [u8]),
}

impl<'a> Debug for Token<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Token::Open => write!(f, "("),
            Token::Close => write!(f, ")"),
            Token::Value(v) => write!(f, "{}", String::from_utf8_lossy(v)),
        }
    }
}

#[derive(Debug, Copy, Clone)]
enum LexState {
    Searching,
    ParsingToken(usize),
    ParsingEscapedToken(usize),
}

impl<'a> Lexer<'a> {
    fn new(input: &'a [u8]) -> Self {
        Self {
            input,
            state: Searching,
            pos: 0,
        }
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Token<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        use LexState::*;

        // are we already done?
        if self.pos >= self.input.len() {
            return None;
        }

        for &c in self.input.iter().skip(self.pos) {
            match self.state {
                Searching => {
                    // when we are searching, we always consume the character
                    self.pos += 1;
                    self.state = match c {
                        b'|' => ParsingEscapedToken(self.pos),
                        b'(' => return Some(Token::Open),
                        b')' => return Some(Token::Close),
                        // White Space Characters: tab, line feed, carriage return or space
                        b' ' | b'\n' | b'\r' | b'\t' => Searching,
                        // string literals are currently not supported
                        b'"' => todo!("String literals are currently not supported!"),
                        _ => ParsingToken(self.pos - 1),
                    }
                }
                ParsingToken(start) => {
                    debug_assert!(start <= self.pos, "{start} > {}", self.pos);
                    match c {
                        // done
                        b'|' | b'(' | b')' | b' ' | b'\n' | b'\r' | b'\t' => {
                            self.state = Searching; // do not consume the character
                            return Some(Token::Value(&self.input[start..self.pos]));
                        }
                        _ => {
                            // consume character
                            self.pos += 1;
                        }
                    }
                }
                ParsingEscapedToken(start) => {
                    // consume character
                    self.pos += 1;
                    if c == b'|' {
                        self.state = Searching;
                        return Some(Token::Value(&self.input[start..(self.pos - 1)]));
                    }
                }
            };
        }

        debug_assert_eq!(self.pos, self.input.len() - 1);
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lex_to_token_str(input: &str) -> String {
        let tokens = Lexer::new(input.as_bytes())
            .map(|token| format!("{token:?}"))
            .collect::<Vec<_>>();
        tokens.join(" ")
    }

    #[test]
    fn test_lexer() {
        let inp = "(+ a b)";
        assert_eq!(lex_to_token_str(inp), "( + a b )");
        let inp = "(+ |a|    b     (      )";
        assert_eq!(lex_to_token_str(inp), "( + a b ( )");
    }

    #[test]
    fn test_parser() {
        let mut ctx = Context::default();
        let a = ctx.bv_symbol("a", 2);
        let mut symbols = FxHashMap::from_iter([("a".to_string(), a)]);
        let expr = parse_expr(&mut ctx, &mut symbols, &mut "(bvand a #b00)".as_bytes()).unwrap();
        assert_eq!(expr, ctx.build(|c| c.add(a, c.bit_vec_val(0, 2))));
    }
}
