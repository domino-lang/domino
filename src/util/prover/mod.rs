use crate::util::smtmodel::SmtModel;
use crate::writers::smt::exprs::SmtExpr;

use std::fmt;

pub mod error;

#[cfg(feature = "process-solver")]
pub mod process;

pub use error::{Error, Result};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProverResponse {
    Sat,
    Unsat,
    Unknown,
}

pub trait ProverFactory {
    fn new_prover(&self) -> Result<impl Prover>;
    fn new_prover_with_transcript<W: std::io::Write + Send + Sync + 'static>(
        &self,
        write: W,
    ) -> Result<impl Prover>;
    fn transcript_enabled(&self) -> bool;
}

pub trait Prover: fmt::Write {
    fn write_smt<I: Into<SmtExpr>>(&mut self, expr: I) -> Result<()>;
    fn check_sat(&mut self) -> Result<ProverResponse>;
    fn get_model(&mut self) -> Result<(String, SmtModel)>;

    fn close(&mut self);
}

impl ProverResponse {
    /// Returns `true` if the prover response is [`Sat`].
    ///
    /// [`Sat`]: ProverResponse::Sat
    #[must_use]
    pub fn is_sat(&self) -> bool {
        matches!(self, Self::Sat)
    }

    /// Returns `true` if the prover response is [`Unsat`].
    ///
    /// [`Unsat`]: ProverResponse::Unsat
    #[must_use]
    pub fn is_unsat(&self) -> bool {
        matches!(self, Self::Unsat)
    }

    /// Returns `true` if the prover response is [`Unknown`].
    ///
    /// [`Unknown`]: ProverResponse::Unknown
    #[must_use]
    pub fn is_unknown(&self) -> bool {
        matches!(self, Self::Unknown)
    }
}

impl fmt::Display for ProverResponse {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ProverResponse::Sat => write!(f, "sat"),
            ProverResponse::Unsat => write!(f, "unsat"),
            ProverResponse::Unknown => write!(f, "unknown"),
        }
    }
}
