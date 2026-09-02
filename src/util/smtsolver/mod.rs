use crate::util::smtmodel::SmtModel;
use crate::writers::smt::exprs::SmtExpr;

use std::fmt;

pub mod error;

#[cfg(feature = "process-solver")]
pub mod process;

#[cfg(feature = "cvc5-lib")]
pub mod cvc5lib;

pub use error::{Error, Result};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SmtSolverResponse {
    Sat,
    Unsat,
    Unknown,
}

pub trait SmtSolverBackend {
    type Solver: SmtSolver;

    fn new_smtsolver(&self) -> Result<Self::Solver>;
    fn new_smtsolver_with_transcript<W: std::io::Write + Send + Sync + 'static>(
        &self,
        write: W,
    ) -> Result<Self::Solver>;
}

pub trait SmtSolver: fmt::Write {
    fn write_smt<I: Into<SmtExpr>>(&mut self, expr: I) -> Result<()>;
    fn check_sat(&mut self) -> Result<SmtSolverResponse>;
    fn get_model(&mut self) -> Result<(String, SmtModel)>;

    /// Push one assertion level (`(push 1)`).
    fn push(&mut self) -> Result<()>;
    /// Pop one assertion level (`(pop 1)`).
    fn pop(&mut self) -> Result<()>;
    /// `(set-option :<key> <value>)`.
    fn set_option(&mut self, key: &str, value: &str) -> Result<()>;

    fn close(&mut self);
}

impl SmtSolverResponse {
    /// Returns `true` if the smt solver response is [`Sat`].
    ///
    /// [`Sat`]: SmtSolverResponse::Sat
    #[must_use]
    pub fn is_sat(&self) -> bool {
        matches!(self, Self::Sat)
    }

    /// Returns `true` if the smt solver response is [`Unsat`].
    ///
    /// [`Unsat`]: SmtSolverResponse::Unsat
    #[must_use]
    pub fn is_unsat(&self) -> bool {
        matches!(self, Self::Unsat)
    }

    /// Returns `true` if the smt solver response is [`Unknown`].
    ///
    /// [`Unknown`]: SmtSolverResponse::Unknown
    #[must_use]
    pub fn is_unknown(&self) -> bool {
        matches!(self, Self::Unknown)
    }
}

impl fmt::Display for SmtSolverResponse {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SmtSolverResponse::Sat => write!(f, "sat"),
            SmtSolverResponse::Unsat => write!(f, "unsat"),
            SmtSolverResponse::Unknown => write!(f, "unknown"),
        }
    }
}
