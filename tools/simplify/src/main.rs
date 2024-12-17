// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use clap::Parser;
use patronus::expr::*;
use patronus::smt::SmtCommand;
use patronus::*;
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
    let cmds = parse_commands(&mut in_reader, &mut ctx);

    todo!();
}

fn parse_commands(inp: &mut impl BufRead, ctx: &mut Context) -> Vec<SmtCommand> {
    let mut out = vec![];

    out
}
