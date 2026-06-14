// SPDX-License-Identifier: MIT OR Apache-2.0

use std::fmt::Write;
use std::result;

use crate::util::smtmodel::SmtModel;
use crate::writers::smt::exprs::SmtExpr;

use super::{Error, Result, SmtSolver, SmtSolverBackend, SmtSolverResponse};

use crate::util::process;
use clap::ValueEnum;

pub struct Communicator(process::Communicator);

#[derive(ValueEnum, Clone, Debug, Copy)]
pub enum SolverVariant {
    Cvc4,
    Cvc5,
    Z3,
}

pub struct ProcessSmtSolverBackend {
    backend: SolverVariant,
}

impl ProcessSmtSolverBackend {
    pub fn new(backend: SolverVariant) -> Self {
        Self { backend }
    }
}

impl SmtSolverBackend for ProcessSmtSolverBackend {
    type Solver = Communicator;

    fn new_smtsolver(&self) -> Result<Self::Solver> {
        Communicator::new(self.backend)
    }

    fn new_smtsolver_with_transcript<W: std::io::Write + Send + Sync + 'static>(
        &self,
        writer: W,
    ) -> Result<Self::Solver> {
        Communicator::new_with_transcript(self.backend, writer)
    }
}

impl Communicator {
    pub fn new(backend: SolverVariant) -> Result<Self> {
        match backend {
            SolverVariant::Cvc4 => Communicator::new_cvc4(),
            SolverVariant::Cvc5 => Communicator::new_cvc5(),
            SolverVariant::Z3 => Communicator::new_z3(),
        }
    }

    pub fn new_with_transcript<W: std::io::Write + Send + Sync + 'static>(
        backend: SolverVariant,
        transcript: W,
    ) -> Result<Self> {
        match backend {
            SolverVariant::Cvc4 => Communicator::new_cvc4_with_transcript(transcript),
            SolverVariant::Cvc5 => Communicator::new_cvc5_with_transcript(transcript),
            SolverVariant::Z3 => Communicator::new_z3_with_transcript(transcript),
        }
    }

    pub fn new_z3() -> Result<Self> {
        let mut cmd = std::process::Command::new("z3");
        cmd.args(["-in", "-smt2"])
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::inherit());

        Ok(Self(
            process::Communicator::new_from_cmd_without_transcript(cmd)?,
        ))
    }

    pub fn new_z3_with_transcript<W: std::io::Write + Send + Sync + 'static>(
        transcript: W,
    ) -> Result<Self> {
        let mut cmd = std::process::Command::new("z3");
        cmd.args(["-in", "-smt2"])
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::inherit());

        Ok(Self(process::Communicator::new_from_cmd(
            cmd,
            Some(transcript),
        )?))
    }

    pub fn new_cvc4() -> Result<Self> {
        let mut cmd = std::process::Command::new("cvc4");
        cmd.args(["--lang=smt2", "--produce-models"])
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::inherit());

        Ok(Self(
            process::Communicator::new_from_cmd_without_transcript(cmd)?,
        ))
    }

    pub fn new_cvc4_with_transcript<W: std::io::Write + Send + Sync + 'static>(
        transcript: W,
    ) -> Result<Self> {
        let mut cmd = std::process::Command::new("cvc4");
        cmd.args(["--lang=smt2", "--produce-models"])
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::inherit());

        Ok(Self(process::Communicator::new_from_cmd(
            cmd,
            Some(transcript),
        )?))
    }

    pub fn new_cvc5() -> Result<Self> {
        let mut cmd = std::process::Command::new("cvc5");
        cmd.args(["--lang=smt2", "--produce-models", "--arrays-exp"])
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::inherit());

        Ok(Self(
            process::Communicator::new_from_cmd_without_transcript(cmd)?,
        ))
    }

    pub fn new_cvc5_with_transcript<W: std::io::Write + Send + Sync + 'static>(
        transcript: W,
    ) -> Result<Self> {
        //let mut cmd = std::process::Command::new("cat");
        //cmd.stdin(std::process::Stdio::piped())

        let mut cmd = std::process::Command::new("cvc5");
        cmd.args(["--lang=smt2", "--produce-models", "--arrays-exp"])
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::inherit());

        Ok(Self(process::Communicator::new_from_cmd(
            cmd,
            Some(transcript),
        )?))
    }

    pub fn read_until_end(&mut self) -> Result<String> {
        Ok(self.0.read_until_end()?)
    }

    pub fn join(&mut self) -> Result<()> {
        Ok(self.0.join()?)
    }
}

impl SmtSolver for Communicator {
    fn get_model(&mut self) -> Result<(String, SmtModel)> {
        writeln!(self, "\n(get-model)")?;
        let (_cnt, modelstring, model) = self.0.read_model()?;
        Ok((modelstring, model))
    }

    #[cfg(not(target_os = "windows"))]
    fn check_sat(&mut self) -> Result<SmtSolverResponse> {
        writeln!(self, "\n(check-sat)")?;

        let pred =
            |_: usize, data: &str| -> (usize, Option<result::Result<SmtSolverResponse, Error>>) {
                let is_err_start = data.starts_with(r#"(error ""#);
                let is_err_end = data.ends_with(")\n");
                if data.starts_with("sat\n") {
                    (4, Some(Ok(SmtSolverResponse::Sat)))
                } else if data.starts_with("unsat\n") {
                    (6, Some(Ok(SmtSolverResponse::Unsat)))
                } else if data.starts_with("unknown\n") {
                    (8, Some(Ok(SmtSolverResponse::Unknown)))
                } else if is_err_start && is_err_end {
                    (data.len(), Some(Err(Error::SolverError(data.to_string()))))
                } else {
                    (0, None)
                }
            };

        let resp = self.0.read_until_pred(pred)??;
        Ok(resp)
    }

    #[cfg(target_os = "windows")]
    fn check_sat(&mut self) -> Result<SmtSolverResponse> {
        writeln!(self, "\n(check-sat)")?;

        let pred =
            |_: usize, data: &str| -> (usize, Option<result::Result<SmtSolverResponse, Error>>) {
                let is_err_start = data.starts_with(r#"(error ""#);
                let is_err_end = data.ends_with(")\r\n");
                if data.starts_with("sat\r\n") {
                    return (5, Some(Ok(SmtSolverResponse::Sat)));
                } else if data.starts_with("unsat\r\n") {
                    return (7, Some(Ok(SmtSolverResponse::Unsat)));
                } else if data.starts_with("unknown\r\n") {
                    return (9, Some(Ok(SmtSolverResponse::Unknown)));
                } else if is_err_start && is_err_end {
                    return (data.len(), Some(Err(Error::SolverError(data.to_string()))));
                } else {
                    return (0, None);
                }
            };

        let resp = self.0.read_until_pred(pred)??;
        Ok(resp)
    }

    fn write_smt<I: Into<SmtExpr>>(&mut self, expr: I) -> Result<()> {
        // avoid making a lot of tiny writes. instead, write everything into a buffer and write
        // that buffer. In the future, we could optimize this further by reusing the buffer instead
        // of allocating a new one every time.
        let mut buffer = String::new();
        write!(buffer, "{}", expr.into())?;

        write!(self, "{buffer}")?;
        Ok(())
    }

    fn close(&mut self) {
        self.0.close();
    }
}

impl std::fmt::Write for Communicator {
    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        let result = self.0.write_str(s);

        std::thread::sleep(std::time::Duration::from_micros(100));

        result
    }
}
