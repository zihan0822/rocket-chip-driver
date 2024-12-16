// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use clap::Parser;
use patronus::expr::*;
use patronus::*;

#[derive(Parser, Debug)]
#[command(name = "simplify")]
#[command(author = "Kevin Laeufer <laeufer@berkeley.edu>")]
#[command(version)]
#[command(about = "Parses a SMT file, simplifies it and writes the simplified version to an output file.", long_about = None)]
struct Args {
    #[arg(value_name = "INPUT", index = 1)]
    input_file: String,
    #[arg(value_name = "OUTPUT", index = 2)]
    output_file: String,
}

fn main() {
    let args = Args::parse();
    todo!();
}