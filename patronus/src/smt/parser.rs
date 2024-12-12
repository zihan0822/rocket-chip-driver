// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::expr::{Context, ExprRef};
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
    let on_token = |token: Token| {
        println!("TODO: {:?}", token);
        Ok(())
    };

    lex(input, on_token)?;

    todo!()
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

#[derive(Debug)]
enum LexState {
    Searching,
    ParsingToken,
    ParsingEscapedToken,
}

/// lex SMTLib
fn lex(input: &mut impl BufRead, mut on_token: impl FnMut(Token) -> Result<()>) -> Result<()> {
    use LexState::*;
    let mut token_buf = Vec::with_capacity(128);
    let mut state = Searching;

    for c in input.bytes() {
        let c = c?;
        state = match state {
            Searching => {
                debug_assert!(token_buf.is_empty());
                match c {
                    b'|' => ParsingEscapedToken,
                    b'(' => {
                        on_token(Token::Open)?;
                        Searching
                    }
                    b')' => {
                        on_token(Token::Close)?;
                        Searching
                    }
                    // White Space Characters: tab, line feed, carriage return or space
                    b' ' | b'\n' | b'\r' | b'\t' => Searching,
                    // string literals are currently not supported
                    b'"' => return Err(SmtParserError::Unsupported("String Literal".to_string())),
                    other => {
                        token_buf.push(other);
                        ParsingToken
                    }
                }
            }
            ParsingToken => {
                debug_assert!(!token_buf.is_empty());
                match c {
                    b'|' => {
                        on_token(Token::Value(&token_buf))?;
                        token_buf.clear();
                        ParsingEscapedToken
                    }
                    b'(' => {
                        on_token(Token::Value(&token_buf))?;
                        token_buf.clear();
                        on_token(Token::Open)?;
                        Searching
                    }
                    b')' => {
                        on_token(Token::Value(&token_buf))?;
                        token_buf.clear();
                        on_token(Token::Close)?;
                        Searching
                    }
                    // White Space Characters: tab, line feed, carriage return or space
                    b' ' | b'\n' | b'\r' | b'\t' => {
                        on_token(Token::Value(&token_buf))?;
                        token_buf.clear();
                        Searching
                    }
                    other => {
                        token_buf.push(other);
                        ParsingToken
                    }
                }
            }
            ParsingEscapedToken => {
                if c == b'|' {
                    on_token(Token::Value(&token_buf))?;
                    token_buf.clear();
                    Searching
                } else {
                    token_buf.push(c);
                    ParsingEscapedToken
                }
            }
        };
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lex_to_token_str(input: &str) -> String {
        let mut tokens = vec![];
        lex(&mut input.as_bytes(), |token| {
            tokens.push(format!("{token:?}"));
            Ok(())
        })
        .unwrap();

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
