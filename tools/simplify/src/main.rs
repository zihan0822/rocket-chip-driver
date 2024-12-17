// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use clap::Parser;
use patronus::expr::*;
use patronus::smt::{parse_command, serialize_cmd, SmtCommand};
use patronus::*;
use rustc_hash::FxHashMap;
use std::io::{BufRead, BufReader, BufWriter};
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

    // open input file
    let in_file = std::fs::File::open(args.input_file).expect("failed to open input file");
    let mut in_reader = BufReader::new(in_file);

    // open output file
    let out_file =
        std::fs::File::create(args.output_file).expect("failed to open output file for writing");
    let mut out = BufWriter::new(out_file);

    // read and write commands
    let mut ctx = Context::default();
    let mut st = FxHashMap::default();
    while let Some(cmd) =
        read_cmd(&mut in_reader, &mut ctx, &mut st).expect("failed to read command")
    {
        serialize_cmd(&mut out, Some(&ctx), &cmd).expect("failed to write command");
    }
}

type SymbolTable = FxHashMap<String, ExprRef>;

fn read_cmd(
    inp: &mut impl BufRead,
    ctx: &mut Context,
    st: &mut SymbolTable,
) -> std::io::Result<Option<SmtCommand>> {
    let mut cmd_str = String::new();
    inp.read_line(&mut cmd_str)?;

    // skip lines that are just comments
    while is_comment(&cmd_str) {
        cmd_str.clear();
        inp.read_line(&mut cmd_str)?;
    }

    // ensure that the response contains balanced parentheses
    while count_parens(&cmd_str) > 0 {
        cmd_str.push(' ');
        inp.read_line(&mut cmd_str)?;
    }

    // if we did not get anything, we are probably done
    if cmd_str.trim().is_empty() {
        return Ok(None);
    }

    // debug print
    let cmd = parse_command(ctx, st, cmd_str.as_bytes()).expect("failed to parse command");

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
