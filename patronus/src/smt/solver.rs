// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::expr::{Context, ExprRef};
use std::io::Write;
use std::io::{BufRead, BufReader, BufWriter};
use std::process::{ChildStdin, Command, Stdio};
use thiserror::Error;

/// A SMT Solver Error.
#[derive(Error, Debug)]
pub enum Error {
    #[error("[smt] I/O operation failed")]
    Io(#[from] std::io::Error),
    #[error("[smt] cannot pop because the stack is already empty")]
    StackUnderflow,
    #[error("[smt] {0} reported an error:\n{1}")]
    FromSolver(String, String),
    #[error("[smt] {0} returned an unexpected response:\n{1}")]
    UnexpectedResponse(String, String),
}

pub type Result<T> = std::result::Result<T, Error>;

/// An SMT Logic.
#[derive(Debug, Clone)]
pub enum Logic {
    All,
    QfAufbv,
    QfAbv,
}

/// The result of a `(check-sat)` command.
#[derive(Debug, Clone)]
pub enum CheckSatResponse {
    Sat,
    Unsat,
    Unknown,
}

/// Interface to a SMT Solver with everything executing as blocking I/O.
pub trait Solver {
    fn set_logic(&mut self, option: Logic) -> Result<()>;
    fn assert(&mut self, ctx: &Context, e: ExprRef) -> Result<()>;
    fn declare_const(&mut self, ctx: &Context, symbol: ExprRef) -> Result<()>;
    fn define_const(&mut self, ctx: &Context, symbol: ExprRef, expr: ExprRef) -> Result<()>;
    fn check_sat_assuming(
        &mut self,
        props: impl IntoIterator<Item = ExprRef>,
    ) -> Result<CheckSatResponse>;
    fn check_sat(&mut self) -> Result<CheckSatResponse> {
        self.check_sat_assuming([])
    }
    fn push(&mut self) -> Result<()>;
    fn pop(&mut self) -> Result<()>;
}

/// Launches an SMT solver and communicates through `stdin` using SMTLib commands.
pub struct SmtLibSolver {
    name: String,
    proc: std::process::Child,
    stdin: BufWriter<std::process::ChildStdin>,
    stdout: BufReader<std::process::ChildStdout>,
    stack_depth: usize,
    response: String,
}

impl SmtLibSolver {
    pub fn bitwuzla() -> Result<impl Solver> {
        Self::create(&BITWUZLA_CMD)
    }

    fn create(cmd: &SmtSolverCmd) -> Result<impl Solver> {
        let mut proc = Command::new(cmd.name)
            .args(cmd.args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()?;
        let stdin = BufWriter::new(proc.stdin.take().unwrap());
        let stdout = BufReader::new(proc.stdout.take().unwrap());
        let name = cmd.name.to_string();
        let mut solver = Self {
            name,
            proc,
            stdin,
            stdout,
            stack_depth: 0,
            response: String::new(),
        };
        for option in cmd.options.iter() {
            solver.write_cmd(|o| writeln!(o, "(set-option :{} true)", option))?;
        }
        Ok(solver)
    }

    #[inline]
    fn write_cmd_str(&mut self, cmd: &str) -> Result<()> {
        self.write_cmd(|stdin| writeln!(stdin, "{}", cmd))
    }

    #[inline]
    fn write_cmd(
        &mut self,
        cmd: impl Fn(&mut BufWriter<ChildStdin>) -> std::result::Result<(), std::io::Error>,
    ) -> Result<()> {
        cmd(&mut self.stdin)?;
        self.stdin.flush()?;
        Ok(())
    }

    /// after this function executes, the result will be available in `self.result`.
    fn read_response(&mut self) -> Result<()> {
        self.stdin.flush()?; // make sure that the commands reached the solver
        self.response.clear();
        // our basic assumptions are:
        // 1. the solver will terminate its answer with '\n'
        // 2. the answer will contain a balanced number of parenthesis
        self.stdout.read_line(&mut self.response)?;
        while count_parens(&self.response) > 0 {
            self.response.push(' ');
            self.stdout.read_line(&mut self.response)?;
        }
        // check to see if there was an error
        if self.response.trim_start().starts_with("(error") {
            let trimmed = self.response.trim();
            let start = "(error ".len();
            let msg = &trimmed[start..(trimmed.len() - start - 1)];
            Err(Error::FromSolver(self.name.clone(), msg.to_string()))
        } else {
            Ok(())
        }
    }
}

fn count_parens(s: &str) -> i64 {
    s.chars().fold(0, |count, cc| match cc {
        '(' => count + 1,
        ')' => count - 1,
        _ => count,
    })
}

impl Drop for SmtLibSolver {
    fn drop(&mut self) {
        // try to close the child process as not to leak resources
        self.write_cmd_str("(exit)")
            .expect("failed to send exit command");
        let status = self
            .proc
            .wait()
            .expect("failed to wait for SMT solver to exit");
        assert!(
            status.success(),
            "There was an error with the solver exiting: {:?}",
            status
        );
    }
}

impl Solver for SmtLibSolver {
    fn set_logic(&mut self, logic: Logic) -> Result<()> {
        let logic = match logic {
            Logic::All => "ALL",
            Logic::QfAufbv => "QF_AUFBV",
            Logic::QfAbv => "QF_ABV",
        };
        self.write_cmd(|o| writeln!(o, "(set-logic {})", logic))
    }

    fn assert(&mut self, ctx: &Context, e: ExprRef) -> Result<()> {
        todo!()
    }

    fn declare_const(&mut self, ctx: &Context, symbol: ExprRef) -> Result<()> {
        todo!()
    }

    fn define_const(&mut self, ctx: &Context, symbol: ExprRef, expr: ExprRef) -> Result<()> {
        todo!()
    }

    fn check_sat_assuming(
        &mut self,
        props: impl IntoIterator<Item = ExprRef>,
    ) -> Result<CheckSatResponse> {
        todo!()
    }

    fn check_sat(&mut self) -> Result<CheckSatResponse> {
        self.write_cmd_str("(check-sat)")?;
        self.read_response()?;
        match self.response.trim() {
            "sat" => Ok(CheckSatResponse::Sat),
            "unsat" => Ok(CheckSatResponse::Unsat),
            other => Err(Error::UnexpectedResponse(
                self.name.clone(),
                other.to_string(),
            )),
        }
    }

    fn push(&mut self) -> Result<()> {
        self.write_cmd_str("(push 1)")?;
        self.stack_depth += 1;
        Ok(())
    }

    fn pop(&mut self) -> Result<()> {
        if self.stack_depth > 0 {
            self.write_cmd_str("(pop 1)")?;
            self.stack_depth -= 1;
            Ok(())
        } else {
            Err(Error::StackUnderflow)
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct SmtSolverCmd {
    name: &'static str,
    args: &'static [&'static str],
    options: &'static [&'static str],
    supports_uf: bool,
    supports_check_assuming: bool,
}

const BITWUZLA_CMD: SmtSolverCmd = SmtSolverCmd {
    name: "bitwuzla",
    args: &[],
    options: &["incremental"],
    supports_uf: false,
    supports_check_assuming: true,
};

const YICES2_CMD: SmtSolverCmd = SmtSolverCmd {
    name: "yices-smt2",
    args: &["--incremental"],
    options: &[],
    supports_uf: false, // actually true, but ignoring for now
    supports_check_assuming: false,
};
