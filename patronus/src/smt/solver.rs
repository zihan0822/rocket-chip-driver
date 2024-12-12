// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::expr::{Context, ExprRef};
use crate::smt::serialize::serialize_expr;
use std::io::{BufRead, BufReader, BufWriter};
use std::io::{Read, Write};
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
#[derive(Debug, Clone, Eq, PartialEq)]
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
        ctx: &Context,
        props: impl IntoIterator<Item = ExprRef>,
    ) -> Result<CheckSatResponse>;
    fn check_sat(&mut self) -> Result<CheckSatResponse>;
    fn push(&mut self) -> Result<()>;
    fn pop(&mut self) -> Result<()>;
}

/// Launches an SMT solver and communicates through `stdin` using SMTLib commands.
pub struct SmtLibSolver<R: Write + Send> {
    name: String,
    proc: std::process::Child,
    stdin: BufWriter<std::process::ChildStdin>,
    stdout: BufReader<std::process::ChildStdout>,
    stderr: std::process::ChildStderr,
    stack_depth: usize,
    response: String,
    replay_file: Option<R>,
    /// keeps track of whether there was an error from the solver which might make regular shutdown
    /// impossible
    has_error: bool,
}

impl<R: Write + Send> SmtLibSolver<R> {
    pub fn bitwuzla(replay_file: Option<R>) -> Result<impl Solver> {
        Self::create(&BITWUZLA_CMD, replay_file)
    }

    fn create(cmd: &SmtSolverCmd, replay_file: Option<R>) -> Result<impl Solver> {
        let mut proc = Command::new(cmd.name)
            .args(cmd.args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()?;
        let stdin = BufWriter::new(proc.stdin.take().unwrap());
        let stdout = BufReader::new(proc.stdout.take().unwrap());
        let stderr = proc.stderr.take().unwrap();
        let name = cmd.name.to_string();
        let mut solver = Self {
            name,
            proc,
            stdin,
            stdout,
            stderr,
            stack_depth: 0,
            response: String::new(),
            replay_file,
            has_error: false,
        };
        for option in cmd.options.iter() {
            solver.write_cmd_replay(|o| writeln!(o, "(set-option :{} true)", option))?;
            solver.write_cmd(|o| writeln!(o, "(set-option :{} true)", option))?;
        }
        Ok(solver)
    }

    #[inline]
    fn write_cmd_str(&mut self, cmd: &str) -> Result<()> {
        self.write_cmd_replay(|stdin| writeln!(stdin, "{}", cmd))?;
        self.write_cmd(|stdin| writeln!(stdin, "{}", cmd))
    }

    #[inline]
    fn write_cmd(
        &mut self,
        cmd: impl FnOnce(&mut BufWriter<ChildStdin>) -> std::result::Result<(), std::io::Error>,
    ) -> Result<()> {
        cmd(&mut self.stdin)?;
        self.stdin.flush()?;
        Ok(())
    }

    #[inline]
    fn write_cmd_replay(
        &mut self,
        cmd: impl FnOnce(&mut R) -> std::result::Result<(), std::io::Error>,
    ) -> Result<()> {
        if let Some(rf) = self.replay_file.as_mut() {
            cmd(rf)?;
            rf.flush()?;
        }
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
        // check stderr
        let mut err = vec![];
        self.stderr.read_to_end(&mut err)?;
        if !err.is_empty() {
            self.has_error = true;
            return Err(Error::FromSolver(
                self.name.clone(),
                String::from_utf8_lossy(&err).to_string(),
            ));
        }

        // check to see if there was an error reported on stdout
        if self.response.trim_start().starts_with("(error") {
            let trimmed = self.response.trim();
            let start = "(error ".len();
            let msg = &trimmed[start..(trimmed.len() - start - 1)];
            self.has_error = true;
            Err(Error::FromSolver(self.name.clone(), msg.to_string()))
        } else {
            Ok(())
        }
    }

    fn read_sat_response(&mut self) -> Result<CheckSatResponse> {
        self.read_response()?;
        let response = self.response.trim();
        match response {
            "sat" => Ok(CheckSatResponse::Sat),
            "unsat" => Ok(CheckSatResponse::Unsat),
            other => Err(Error::UnexpectedResponse(
                self.name.clone(),
                other.to_string(),
            )),
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

impl<R: Write + Send> Drop for SmtLibSolver<R> {
    fn drop(&mut self) {
        // try to close the child process as not to leak resources
        if self.write_cmd_str("(exit)").is_err() {
            if self.has_error {
                return;
            } else {
                panic!("failed to send exit command");
            }
        }
        let status = self
            .proc
            .wait()
            .expect("failed to wait for SMT solver to exit");
        if !self.has_error {
            // if everything has gone smoothly so far, we expect a successful exit
            assert!(
                status.success(),
                "There was an error with the solver exiting: {:?}",
                status
            );
        }
    }
}

impl<R: Write + Send> Solver for SmtLibSolver<R> {
    fn set_logic(&mut self, logic: Logic) -> Result<()> {
        let logic = match logic {
            Logic::All => "ALL",
            Logic::QfAufbv => "QF_AUFBV",
            Logic::QfAbv => "QF_ABV",
        };
        self.write_cmd_replay(|o| writeln!(o, "(set-logic {})", logic))?;
        self.write_cmd(|o| writeln!(o, "(set-logic {})", logic))
    }

    fn assert(&mut self, ctx: &Context, e: ExprRef) -> Result<()> {
        self.write_cmd_replay(|out| {
            write!(out, "(assert ")?;
            serialize_expr(out, ctx, e)?;
            writeln!(out, ")")
        })?;
        self.write_cmd(|out| {
            write!(out, "(assert ")?;
            serialize_expr(out, ctx, e)?;
            writeln!(out, ")")
        })
    }

    fn declare_const(&mut self, ctx: &Context, symbol: ExprRef) -> Result<()> {
        todo!(
            "we should change hoow write_cmd works to take &str and a list of expressions or types"
        )
    }

    fn define_const(&mut self, ctx: &Context, symbol: ExprRef, expr: ExprRef) -> Result<()> {
        todo!()
    }

    fn check_sat_assuming(
        &mut self,
        ctx: &Context,
        props: impl IntoIterator<Item = ExprRef>,
    ) -> Result<CheckSatResponse> {
        let props: Vec<ExprRef> = props.into_iter().collect();
        self.write_cmd_replay(|out| {
            write!(out, "(check-sat-assuming")?;
            let mut is_first = true;
            for &prop in props.iter() {
                write!(out, " ")?;
                serialize_expr(out, ctx, prop)?;
            }
            writeln!(out, ")")
        })?;
        self.write_cmd(|out| {
            write!(out, "(check-sat-assuming")?;
            let mut is_first = true;
            for &prop in props.iter() {
                write!(out, " ")?;
                serialize_expr(out, ctx, prop)?;
            }
            writeln!(out, ")")
        })?;
        self.read_sat_response()
    }

    fn check_sat(&mut self) -> Result<CheckSatResponse> {
        self.write_cmd_str("(check-sat)")?;
        self.read_sat_response()
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bitwuzla() {
        let mut ctx = Context::default();
        let replay = Some(std::fs::File::create("replay.smt").unwrap());
        let mut solver = SmtLibSolver::bitwuzla(replay).unwrap();
        let a = ctx.bv_symbol("a", 3);
        let e = ctx.build(|c| c.equal(a, c.bit_vec_val(3, 3)));
        solver.assert(&ctx, e).unwrap();
        let res = solver.check_sat();
        assert!(res.is_err(), "a was not declared!");
        solver.declare_const(&ctx, a).unwrap();
        let res = solver.check_sat();
        assert_eq!(res.unwrap(), CheckSatResponse::Sat);
    }
}
