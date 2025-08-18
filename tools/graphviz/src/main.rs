use anyhow::Context;
use anyhow::bail;
use patronus::expr::{self, *};
use patronus::system::*;
use rayon::prelude::*;
use std::collections::HashSet;
use std::io::Write;
use std::path::Path;

use clap::{Args, Parser, Subcommand};

#[derive(Parser, Debug)]
struct GraphvizArgs {
    #[arg(short, long, required = true)]
    file: String,

    #[arg(short, long)]
    query: Option<String>,

    #[command(subcommand)]
    command: Option<Command>,
}

#[derive(Subcommand, Debug)]
enum Command {
    Probe(ProbeArgs),
}

#[derive(Args, Debug)]
struct ProbeArgs {
    /// Only consider expr nodes that have at least `min_num_nodes` child nodes
    #[arg(long, default_value_t = 1)]
    min_num_nodes: usize,

    /// Only consider expr nodes that have at most `max_num_nodes` child nodes
    #[arg(long, default_value_t = 1000)]
    max_num_nodes: usize,

    /// A comma separated list to specify operations of interest
    #[arg(long, value_parser, num_args = 1.., value_delimiter = ',')]
    op: Vec<String>,

    /// Path to output directory
    #[arg(long, default_value_t = String::from("dot-graphs"))]
    output: String,

    /// Target file format dot string will be converted to
    /// `dot` command is required for conversion
    #[arg(long, verbatim_doc_comment)]
    format: Option<String>,

    /// Regular expression used for filtering state name
    #[arg(short, long)]
    regex: Option<String>,
}

fn main() {
    if let Err(err) = graphviz() {
        eprintln!("{err:?}");
        std::process::exit(1);
    }
}

fn graphviz() -> anyhow::Result<()> {
    let args = GraphvizArgs::parse();
    let (ctx, sys) =
        patronus::btor2::parse_file(&args.file).context("unable to parse input btor file")?;
    let mut drawer = expr::graphviz::ComputeGraphDrawerBuilder::new(&ctx)
        .with_data_type()
        .with_symbol_name()
        .finish();

    if let Some(query) = args.query.as_ref() {
        let found_expr = sys
            .lookup_output(&ctx, query)
            .or(sys
                .get_state_by_name(&ctx, query)
                .and_then(|state| state.next))
            .with_context(|| format!("queried state `{query}` not found"))?;
        let dot_graph = drawer.dot_graph(found_expr);
        println!("{dot_graph}");
        return Ok(());
    }

    let Some(command) = args.command else {
        return Ok(());
    };

    match command {
        Command::Probe(args) => {
            let validated_args = args.try_into_validated_args()?;
            let filter = validated_args.to_filter();
            let mut unnamed_idx = 0;
            let dot_graphs: Vec<_> = all_root_expr_candidates(&sys)
                .filter_map(|expr| {
                    if filter(&ctx, expr) {
                        let symbol_name = ctx.get_symbol_name(expr).map_or_else(
                            || {
                                let name = format!("unnamed_{unnamed_idx}");
                                unnamed_idx += 1;
                                name
                            },
                            |name| name.to_string(),
                        );
                        Some((symbol_name, drawer.dot_graph(expr)))
                    } else {
                        None
                    }
                })
                .collect();
            let save_directory = Path::new(&validated_args.output_directory);
            std::fs::create_dir_all(save_directory)?;

            let results: Vec<Result<_, _>> = dot_graphs
                .par_iter()
                .map(|(expr_name, dot_graph)| -> anyhow::Result<()> {
                    let dot_save_path = save_directory.join(format!("{expr_name}.txt"));
                    std::fs::File::create(&dot_save_path)?.write_all(dot_graph.as_bytes())?;
                    let Some(ref format) = validated_args.target_format else {
                        return Ok(());
                    };
                    let converted_file_path = dot_save_path.with_extension(format);
                    let mut dot_command = std::process::Command::new("dot")
                        .args([
                            &format!("-T{format}"),
                            "-o",
                            converted_file_path.to_str().unwrap(),
                        ])
                        .stdin(std::process::Stdio::piped())
                        .spawn()?;
                    dot_command
                        .stdin
                        .as_mut()
                        .unwrap()
                        .write_all(dot_graph.as_bytes())?;
                    if !dot_command.wait()?.success() {
                        bail!("failed when trying to convert to {format}");
                    }
                    Ok(())
                })
                .collect();

            for dot_conversion_result in results {
                dot_conversion_result?;
            }
        }
    };
    Ok(())
}

fn all_root_expr_candidates<'a>(sys: &'a TransitionSystem) -> impl Iterator<Item = ExprRef> + 'a {
    sys.outputs
        .iter()
        .map(|out| out.expr)
        .chain(sys.states.iter().filter_map(|s| s.next))
}

impl ProbeArgs {
    fn try_into_validated_args(self) -> anyhow::Result<ValidatedProbeArgs> {
        const SUPPORTED_TARGET_FORMAT: &[&str] = &["png"];
        if self.max_num_nodes < self.min_num_nodes {
            bail!(
                "invalid num nodes range: [{}, {}]",
                self.min_num_nodes,
                self.max_num_nodes
            );
        }
        let op_of_interest = if !self.op.is_empty() {
            Some(HashSet::from_iter(self.op))
        } else {
            None
        };
        let target_format = if let Some(target_format) = self.format {
            if !SUPPORTED_TARGET_FORMAT
                .iter()
                .any(|&supported| supported.eq(&target_format))
            {
                bail!(
                    "unsupported target file format {target_format}, please select from {}",
                    SUPPORTED_TARGET_FORMAT.join(", ")
                );
            }
            Some(target_format)
        } else {
            None
        };
        Ok(ValidatedProbeArgs {
            num_nodes_range: self.min_num_nodes..(self.max_num_nodes + 1),
            op_of_interest,
            output_directory: self.output,
            target_format,
            regex: self.regex.and_then(|pat| regex::Regex::new(&pat).ok()),
        })
    }
}

struct ValidatedProbeArgs {
    num_nodes_range: std::ops::Range<usize>,
    op_of_interest: Option<HashSet<String>>,
    output_directory: String,
    target_format: Option<String>,
    regex: Option<regex::Regex>,
}

type Filter<'a> = dyn Fn(&expr::Context, ExprRef) -> bool + 'a;
impl ValidatedProbeArgs {
    pub fn to_filter<'a>(&'a self) -> Box<Filter<'a>> {
        let filter =
            move |ctx: &expr::Context, expr: ExprRef| {
                self.op_of_interest.as_ref().is_none_or(|op_of_interest| {
                    op_of_interest.contains(ctx[expr].expr_kind_literal())
                }) && self.regex.as_ref().is_none_or(|pat| {
                    ctx.get_symbol_name(expr)
                        .is_some_and(|name| pat.is_match(name))
                }) && self.satisfy_num_nodes_condition(ctx, expr)
            };
        Box::new(filter)
    }

    fn satisfy_num_nodes_condition(&self, ctx: &expr::Context, expr: ExprRef) -> bool {
        let mut num_children = 0usize;
        expr::traversal::top_down(ctx, expr, |ctx, current| {
            num_children += ctx[current].num_children();
            if num_children >= self.num_nodes_range.end {
                expr::traversal::TraversalCmd::Stop
            } else {
                expr::traversal::TraversalCmd::Continue
            }
        });
        self.num_nodes_range.contains(&num_children)
    }
}
