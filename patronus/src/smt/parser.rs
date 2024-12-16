// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::expr::{ArrayType, Context, ExprRef, Type, TypeCheck, WidthInt};
use regex::bytes::RegexSet;
use rustc_hash::FxHashMap;
use std::cmp::Ordering;
use std::fmt::{Debug, Formatter};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum SmtParserError {
    #[error("[smt] get-value response: {0}")]
    GetValueResponse(String),
    #[error("[smt] expected an expression but got: {0}")]
    ExpectedExpr(String),
    #[error("[smt] expected a type but got: {0}")]
    ExpectedType(String),
    #[error("[smt] unknown pattern: {0}")]
    Pattern(String),
    #[error("[smt] missing opening parenthesis for closing parenthesis")]
    MissingOpen,
    #[error("[smt] unsupported feature {0}")]
    Unsupported(String),
    #[error("[smt] unknown symbol {0}")]
    UnknownSymbol(String),
    #[error("[smt] failed to parse integer {0}")]
    ParseInt(String),
    #[error("[smt] not valid UTF-8 (and thus also not valid ASCII!)")]
    Utf8(#[from] std::str::Utf8Error),
    #[error("[smt] I/O operation failed")]
    Io(#[from] std::io::Error),
}

impl From<baa::ParseIntError> for SmtParserError {
    fn from(value: baa::ParseIntError) -> Self {
        SmtParserError::ParseInt(format!("{value:?}"))
    }
}

impl From<std::num::ParseIntError> for SmtParserError {
    fn from(value: std::num::ParseIntError) -> Self {
        SmtParserError::ParseInt(format!("{value:?}"))
    }
}

type Result<T> = std::result::Result<T, SmtParserError>;

type SymbolTable = FxHashMap<String, ExprRef>;

pub fn parse_expr(ctx: &mut Context, st: &mut SymbolTable, input: &[u8]) -> Result<ExprRef> {
    let lexer = Lexer::new(input);
    let (expr, extra_closing_parens) = parse_expr_internal(ctx, st, lexer)?;
    if extra_closing_parens == 0 {
        Ok(expr)
    } else {
        Err(SmtParserError::MissingOpen)
    }
}

fn parse_expr_internal(
    ctx: &mut Context,
    st: &mut SymbolTable,
    lexer: Lexer,
) -> Result<(ExprRef, u64)> {
    use ParserItem::*;
    let mut stack: Vec<ParserItem> = Vec::with_capacity(64);
    // keep track of how many closing parenthesis without an opening one are encountered
    let mut orphan_closing_count = 0u64;
    for token in lexer {
        match token {
            Token::Open => {
                if orphan_closing_count > 0 {
                    return Err(SmtParserError::MissingOpen);
                }
                stack.push(Open);
            }
            Token::Close => {
                // find the closest Open
                if let Some(p) = stack.iter().rev().position(|i| matches!(i, Open)) {
                    let open_pos = stack.len() - 1 - p;
                    let pattern = &stack[open_pos + 1..];
                    let result = parse_pattern(ctx, st, pattern)?;
                    stack.truncate(open_pos);
                    stack.push(result);
                } else {
                    // no matching open parenthesis
                    orphan_closing_count += 1;
                }
            }
            Token::Value(value) => {
                if orphan_closing_count > 0 {
                    return Err(SmtParserError::MissingOpen);
                }
                // we eagerly parse number literals, but we do not make decisions on symbols yet
                stack.push(early_parse_number_literals(ctx, value)?);
            }
            Token::EscapedValue(value) => {
                if orphan_closing_count > 0 {
                    return Err(SmtParserError::MissingOpen);
                }
                stack.push(PExpr(lookup_sym(st, value)?))
            }
        }
    }

    if let [PExpr(e)] = stack.as_slice() {
        Ok((*e, orphan_closing_count))
    } else {
        todo!("error message!: {stack:?}")
    }
}

/// Extracts the value expression from SMT solver responses of the form ((... value))
/// We expect value to be self contained and thus no symbol table should be necessary.
pub fn parse_get_value_response(ctx: &mut Context, input: &[u8]) -> Result<ExprRef> {
    let mut lexer = Lexer::new(input);

    // skip `(`
    let open_one = lexer.next() == Some(Token::Open);
    let open_two = lexer.next() == Some(Token::Open);
    if !open_one || !open_two {
        return Err(SmtParserError::GetValueResponse(
            "expected two opening parentheses".to_string(),
        ));
    }

    // skip next expr
    if !skip_expr(&mut lexer) {
        return Err(SmtParserError::GetValueResponse(
            "failed to find first expression".to_string(),
        ));
    }

    // parse next expr
    let mut st = FxHashMap::default();
    let (expr, extra_closing_parens) = parse_expr_internal(ctx, &mut st, lexer)?;
    match extra_closing_parens.cmp(&2) {
        Ordering::Less => Err(SmtParserError::GetValueResponse(
            "expected two closing parentheses".to_string(),
        )),
        Ordering::Equal => Ok(expr),
        Ordering::Greater => Err(SmtParserError::MissingOpen),
    }
}

fn skip_expr(lexer: &mut Lexer) -> bool {
    let mut open_count = 0u64;
    for token in lexer.by_ref() {
        match token {
            Token::Open => {
                open_count += 1;
            }
            Token::Close => {
                open_count -= 1;
                if open_count == 0 {
                    return true;
                }
            }
            _ => {
                if open_count == 0 {
                    return true;
                }
            }
        }
    }
    // reached end of tokens
    false
}

fn lookup_sym(st: &SymbolTable, name: &[u8]) -> Result<ExprRef> {
    let name = std::str::from_utf8(name)?;
    match st.get(name) {
        Some(s) => Ok(*s),
        None => Err(SmtParserError::UnknownSymbol(name.to_string())),
    }
}

fn parse_pattern<'a>(
    ctx: &mut Context,
    st: &SymbolTable,
    pattern: &[ParserItem<'a>],
) -> Result<ParserItem<'a>> {
    use ParserItem::*;
    let item = match pattern {
        // bit vector type
        [Sym(b"_"), Sym(b"BitVec"), Sym(width)] => PType(Type::BV(parse_width(width)?)),
        // bit vector expressions
        [Sym(b"bvand"), a, b] => PExpr(ctx.and(expr(st, a)?, expr(st, b)?)),
        [Sym(b"bvadd"), a, b] => PExpr(ctx.add(expr(st, a)?, expr(st, b)?)),
        // array type
        [Sym(b"Array"), PType(Type::BV(index_width)), PType(Type::BV(data_width))] => {
            PType(Type::Array(ArrayType {
                index_width: *index_width,
                data_width: *data_width,
            }))
        }
        // array expressions
        [Sym(b"as"), Sym(b"const"), PType(Type::Array(tpe))] => AsConst(*tpe),
        [AsConst(tpe), PExpr(data)] => {
            debug_assert_eq!(tpe.data_width, data.get_bv_type(ctx).unwrap());
            PExpr(ctx.array_const(*data, tpe.index_width))
        }
        [Sym(b"store"), PExpr(array), PExpr(index), PExpr(data)] => {
            PExpr(ctx.array_store(*array, *index, *data))
        }
        other => {
            return Err(SmtParserError::Pattern(format!("{other:?}")));
        }
    };
    Ok(item)
}

fn parse_width(value: &[u8]) -> Result<WidthInt> {
    Ok(std::str::from_utf8(value)?.parse()?)
}

/// errors if the item cannot be directly converted to an expression
fn expr(st: &SymbolTable, item: &ParserItem<'_>) -> Result<ExprRef> {
    match item {
        ParserItem::PExpr(e) => Ok(*e),
        ParserItem::Sym(name) => lookup_sym(st, name),
        other => Err(SmtParserError::ExpectedExpr(format!("{other:?}"))),
    }
}

fn early_parse_number_literals<'a>(ctx: &mut Context, value: &'a [u8]) -> Result<ParserItem<'a>> {
    if let Some(match_id) = NUM_LIT_REGEX.matches(value).into_iter().next() {
        match match_id {
            0 => {
                // binary
                let value = baa::BitVecValue::from_bit_str(std::str::from_utf8(&value[2..])?)?;
                Ok(ParserItem::PExpr(ctx.bv_lit(&value)))
            }
            1 => {
                // hex
                let value = baa::BitVecValue::from_hex_str(std::str::from_utf8(&value[2..])?)?;
                Ok(ParserItem::PExpr(ctx.bv_lit(&value)))
            }
            2 => Err(SmtParserError::Unsupported(format!(
                "decimal constant: {}",
                String::from_utf8_lossy(value)
            ))),
            3 => Ok(ParserItem::PExpr(ctx.tru())),
            4 => Ok(ParserItem::PExpr(ctx.fals())),
            _ => unreachable!("not part of the regex!"),
        }
    } else {
        Ok(ParserItem::Sym(value))
    }
}

/// represents intermediate parser results
enum ParserItem<'a> {
    /// opening parenthesis
    Open,
    /// parsed expression
    PExpr(ExprRef),
    /// parsed type
    PType(Type),
    /// either a built-in or a user defined symbol
    Sym(&'a [u8]),
    /// as const function from the array theory
    AsConst(ArrayType),
}

impl<'a> Debug for ParserItem<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            ParserItem::Open => write!(f, "("),
            ParserItem::PExpr(e) => write!(f, "{e:?}"),
            ParserItem::PType(t) => write!(f, "{t:?}"),
            ParserItem::Sym(v) => write!(f, "S({})", String::from_utf8_lossy(v)),
            ParserItem::AsConst(tpe) => write!(f, "AsConst({tpe:?})"),
        }
    }
}

lazy_static! {
    static ref NUM_LIT_REGEX: RegexSet = RegexSet::new([
        r"^#b[01]+$",                    // binary
        r"^#x[[:xdigit:]]+$",            // hex
        r"^[[:digit:]]+\.[[:digit:]]+$", // decimal
        r"^true$",                       // true == 1
        r"^false$",                       // false == 0
    ]).unwrap();
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Lexer
////////////////////////////////////////////////////////////////////////////////////////////////////

struct Lexer<'a> {
    input: &'a [u8],
    state: LexState,
    pos: usize,
}

#[derive(Eq, PartialEq)]
enum Token<'a> {
    Open,
    Close,
    Value(&'a [u8]),
    EscapedValue(&'a [u8]),
}

impl<'a> Debug for Token<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Token::Open => write!(f, "("),
            Token::Close => write!(f, ")"),
            Token::Value(v) => write!(f, "{}", String::from_utf8_lossy(v)),
            Token::EscapedValue(v) => write!(f, "{}", String::from_utf8_lossy(v)),
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
            state: LexState::Searching,
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
                        return Some(Token::EscapedValue(&self.input[start..(self.pos - 1)]));
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
    use crate::expr::SerializableIrNode;

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
        let expr = parse_expr(&mut ctx, &mut symbols, "(bvand a #b00)".as_bytes()).unwrap();
        assert_eq!(expr, ctx.build(|c| c.and(a, c.bit_vec_val(0, 2))));
    }

    #[test]
    fn test_get_value_parser() {
        let mut ctx = Context::default();
        let expr = parse_get_value_response(&mut ctx, "((a #b011))".as_bytes()).unwrap();
        assert_eq!(expr, ctx.bit_vec_val(3, 3));

        // calling get-value on a more complext response
        let solver_response = "(((bvadd ((_ zero_extend 1) a) (ite false #b0001 #b0000)) #b0001))";
        let expr = parse_get_value_response(&mut ctx, solver_response.as_bytes()).unwrap();
        assert_eq!(expr, ctx.bit_vec_val(1, 4));
    }

    #[test]
    fn test_parse_smt_array_const_and_store() {
        let mut ctx = Context::default();
        let mut symbols = FxHashMap::default();

        let base =
            "((as const (Array (_ BitVec 5) (_ BitVec 32))) #b00000000000000000000000000110011)";
        let expr = parse_expr(&mut ctx, &mut symbols, base.as_bytes()).unwrap();
        assert_eq!(expr.serialize_to_str(&ctx), "([32'x00000033] x 2^5)");

        let store_1 = format!("(store {base} #b01110 #x00000000)");
        let expr = parse_expr(&mut ctx, &mut symbols, store_1.as_bytes()).unwrap();
        assert_eq!(
            expr.serialize_to_str(&ctx),
            "([32'x00000033] x 2^5)[5'b01110 := 32'x00000000]"
        );

        let store_2 = format!("(store {store_1} #b01110 #x00000011)");
        let expr = parse_expr(&mut ctx, &mut symbols, store_2.as_bytes()).unwrap();
        assert_eq!(
            expr.serialize_to_str(&ctx),
            "([32'x00000033] x 2^5)[5'b01110 := 32'x00000000][5'b01110 := 32'x00000011]"
        );
    }
}
