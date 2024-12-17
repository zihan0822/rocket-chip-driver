// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use clap::Parser;
use patronus::expr::*;
use patronus::smt::{parse_command, SmtCommand};
use patronus::*;
use rustc_hash::FxHashMap;
use std::io::{BufRead, BufReader};
use std::path::PathBuf;

#[derive(Parser, Debug)]
#[command(name = "simplify")]
#[command(author = "Kevin Laeufer <laeufer@berkeley.edu>")]
#[command(version)]
#[command(about = "Parses a SMT file, simplifies it and writes the simplified version to an output file.", long_about = None)]
struct Args {
    #[arg(value_name = "INPUT", index = 1)]
    input_file: PathBuf,
    #[arg(value_name = "OUTPUT", index = 2)]
    output_file: PathBuf,
}

fn main() {
    let args = Args::parse();

    // read SMT file
    let in_file = std::fs::File::open(args.input_file).expect("failed to open input file");
    let mut in_reader = BufReader::new(in_file);
    let mut ctx = Context::default();
    let mut st = FxHashMap::default();
    let cmds = read_cmds(&mut in_reader, &mut ctx, &mut st);

    todo!();
}

fn read_cmds(inp: &mut impl BufRead, ctx: &mut Context, st: &mut SymbolTable) -> Vec<SmtCommand> {
    let mut out = vec![];
    while let Some(cmd) = read_cmd(inp, ctx, st).unwrap() {
        out.push(cmd);
    }
    out
}

type SymbolTable = FxHashMap<String, ExprRef>;

fn read_cmd(
    inp: &mut impl BufRead,
    ctx: &mut Context,
    st: &mut SymbolTable,
) -> std::io::Result<Option<SmtCommand>> {
    let mut response = String::new();
    inp.read_line(&mut response)?;

    // skip lines that are just comments
    while is_comment(&response) {
        response.clear();
        inp.read_line(&mut response)?;
    }

    // ensure that the response contains balanced parentheses
    while count_parens(&response) > 0 {
        response.push(' ');
        inp.read_line(&mut response)?;
    }

    // debug print
    println!("{response}");
    let cmd = parse_command(ctx, st, response.as_bytes());
    println!("{cmd:?}");
    let cmd = cmd.unwrap();

    // add symbols to table
    match cmd {
        SmtCommand::DefineConst(sym, _) | SmtCommand::DeclareConst(sym) => {
            st.insert(ctx.get_symbol_name(sym).unwrap().into(), sym);
        }
        _ => {}
    }
    Ok(Some(cmd))
}

fn is_comment(line: &str) -> bool {
    for c in line.chars() {
        if !c.is_ascii_whitespace() {
            return c == ';';
        }
    }
    // all whilespace
    false
}

fn count_parens(s: &str) -> i64 {
    s.chars().fold(0, |count, cc| match cc {
        '(' => count + 1,
        ')' => count - 1,
        _ => count,
    })
}
