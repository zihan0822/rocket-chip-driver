// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use std::fmt::{Debug, Formatter};
use std::io::{BufRead, Read};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum SmtParserError {
    #[error("I/O operation failed")]
    Io(#[from] std::io::Error),
}

type Result<T> = std::result::Result<T, SmtParserError>;

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

/// lex SMTLib
fn lex(input: &mut impl BufRead, mut on_token: impl FnMut(Token) -> Result<()>) -> Result<()> {
    let mut in_escaped = false;
    let mut token_buf = Vec::with_capacity(128);

    for c in input.bytes() {
        let c = c?;
        if in_escaped {
            if c == b'|' {
                on_token(Token::Value(&token_buf))?;
                token_buf.clear();
                in_escaped = false;
            } else {
                token_buf.push(c);
            }
        } else {
            match c {
                b'|' => {
                    in_escaped = true;
                }
                b'(' => {
                    if !token_buf.is_empty() {
                        on_token(Token::Value(&token_buf))?;
                        token_buf.clear();
                    }
                    on_token(Token::Open)?;
                }
                b')' => {
                    if !token_buf.is_empty() {
                        on_token(Token::Value(&token_buf))?;
                        token_buf.clear();
                    }
                    on_token(Token::Close)?;
                }
                b' ' | b'\n' | b'\r' => {
                    if !token_buf.is_empty() {
                        on_token(Token::Value(&token_buf))?;
                        token_buf.clear();
                    }
                }
                other => {
                    token_buf.push(other);
                }
            }
        }
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
}
