// Copyright 2025 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use clap::Parser;
use patronus::expr::SerializableIrNode;
use patronus::system::transform::{replace_anonymous_inputs_with_zero, simplify_expressions};

#[derive(Parser, Debug)]
#[command(name = "view")]
#[command(author = "Kevin Laeufer <laeufer@cornell.edu>")]
#[command(version)]
#[command(about = "Displays a transition system from a btor file.", long_about = None)]
struct Args {
    #[arg(long)]
    simplify: bool,
    #[arg(long)]
    remove_anonymous_inputs: bool,
    #[arg(value_name = "INPUT", index = 1)]
    input_file: std::path::PathBuf,
}

fn main() {
    let args = Args::parse();

    // open input file
    let (mut ctx, mut sys) =
        patronus::btor2::parse_file(args.input_file).expect("failed to open input file");

    if args.remove_anonymous_inputs {
        replace_anonymous_inputs_with_zero(&mut ctx, &mut sys);
    }

    if args.simplify {
        simplify_expressions(&mut ctx, &mut sys);
    }

    println!("{}", sys.serialize_to_str(&ctx));
}
