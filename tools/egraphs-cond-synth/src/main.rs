// Copyright 2024 Cornell University
// Copyright 2024 Princeton University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Amelia Dobis <amelia.dobis@princeton.edu>
// author: Mohanna Shahrad <mohanna@princeton.edu>

mod features;
mod rewrites;
mod samples;
mod summarize;

use crate::features::{apply_features, FeatureResult};
use crate::rewrites::create_rewrites;
use crate::samples::{get_rule_info, get_var_name, Samples};
use crate::summarize::bdd_summarize;
use clap::Parser;
use patronus::expr::*;
use std::io::Write;
use std::path::{Path, PathBuf};

#[derive(Parser, Debug)]
#[command(name = "patronus-egraphs-cond-synth")]
#[command(version)]
#[command(about = "Synthesizes rewrite conditions..", long_about = None)]
struct Args {
    #[arg(long, default_value = "8")]
    max_width: WidthInt,
    #[arg(long)]
    print_samples: bool,
    #[arg(long)]
    dump_smt: bool,
    #[arg(long)]
    bdd_formula: bool,
    #[arg(
        long,
        help = "checks the current condition, prints out if it disagrees with the examples we generate"
    )]
    check_cond: bool,
    #[arg(long, help = "write the generated assignments to a JSON file")]
    write_assignments: Option<PathBuf>,
    #[arg(
        long,
        help = "read assignments from a JSON file instead of generating and checking them"
    )]
    read_assignments: Option<PathBuf>,
    #[arg(
        long,
        help = "writes assignments, features and equivalence into a CSV table"
    )]
    write_csv: Option<PathBuf>,
    #[arg(value_name = "RULE", index = 1)]
    rule: String,
}

fn main() {
    let args = Args::parse();

    // find rule and extract both sides
    let rewrites = create_rewrites();
    let rule = match rewrites.iter().find(|r| r.name.as_str() == args.rule) {
        Some(r) => r,
        None => {
            let available = rewrites.iter().map(|r| r.name.as_str()).collect::<Vec<_>>();
            panic!(
                "Failed to find rewrite rule `{}`!\nAvailable rules are: {:?}",
                args.rule, available
            );
        }
    };

    // generate and check samples
    let samples = if let Some(in_filename) = args.read_assignments {
        let file = std::fs::File::open(&in_filename).expect("failed to open input JSON");
        let mut reader = std::io::BufReader::new(file);
        let samples = Samples::from_json(&mut reader).expect("failed to parse input JSON");
        println!("Assignments loaded from {:?}", in_filename);
        samples
    } else {
        // remember start time
        let start = std::time::Instant::now();
        let samples =
            samples::generate_samples(rule, args.max_width, true, args.dump_smt, args.check_cond);
        let delta_t = std::time::Instant::now() - start;
        println!(
            "Took {delta_t:?} on {} threads.",
            rayon::current_num_threads()
        );
        samples
    };

    println!("Found {} equivalent rewrites.", samples.num_equivalent());
    println!(
        "Found {} unequivalent rewrites.",
        samples.num_unequivalent()
    );

    if let Some(out_filename) = args.write_assignments {
        let mut file = std::fs::File::create(&out_filename).expect("failed to open output JSON");
        samples
            .clone()
            .to_json(&mut file)
            .expect("failed to write output JSON");
        println!("Wrote assignments to `{:?}`", out_filename);
    }

    if args.print_samples {
        for sample in samples.iter() {
            println!("{:?}", sample);
        }
    }

    // check features
    let feature_start = std::time::Instant::now();
    let rule_info = get_rule_info(rule);
    let features = apply_features(&rule_info, &samples);
    let feature_delta_t = std::time::Instant::now() - feature_start;
    println!("{feature_delta_t:?} to apply all features");

    if let Some(filename) = args.write_csv {
        write_csv(filename, &samples, &features).expect("failed to write CSV");
    }

    if args.bdd_formula {
        let summarize_start = std::time::Instant::now();
        let formula = bdd_summarize(&features);
        let summarize_delta_t = std::time::Instant::now() - summarize_start;
        println!("Generated formula in {summarize_delta_t:?}:\n{}", formula);
    }
}

fn write_csv(
    filename: impl AsRef<Path>,
    samples: &Samples,
    features: &FeatureResult,
) -> std::io::Result<()> {
    let mut o = std::io::BufWriter::new(std::fs::File::create(filename)?);

    // header
    write!(o, "equivalent?,")?;
    for var in samples.vars() {
        write!(o, "{},", get_var_name(&var).unwrap())?;
    }
    let num_features = features.num_features();
    for (ii, feature) in features.labels().iter().enumerate() {
        write!(o, "{}", feature)?;
        if ii < num_features - 1 {
            write!(o, ",")?;
        }
    }
    writeln!(o)?;

    // data
    for ((a, a_is_eq), (s, s_is_eq)) in samples.iter().zip(features.iter()) {
        assert_eq!(a_is_eq, s_is_eq);
        write!(o, "{},", a_is_eq as u8)?;
        for (_var, value) in a.iter() {
            write!(o, "{},", *value)?;
        }
        for (ii, feature_on) in s.iter().enumerate() {
            let feature_on = *feature_on;
            write!(o, "{}", feature_on as u8)?;
            if ii < num_features - 1 {
                write!(o, ",")?;
            }
        }
        writeln!(o)?;
    }

    Ok(())
}
