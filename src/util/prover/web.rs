use thiserror::Error;

use crate::util::prover::ProverResponse;
use crate::writers::smt::exprs::SmtExpr;

#[derive(Clone, Debug, Copy)]
pub enum ProverBackend {
    Cvc5,
}

pub struct Communicator {
    //    cvc: &CVC
}

#[derive(Debug, Error)]
pub enum Error {
    #[error("prover error: {0}")]
    ProverError(String),
}

pub type Result<T> = std::result::Result<T, Error>;

impl Communicator {
    pub fn new(backend: ProverBackend) -> Result<Self> {
        Ok(Communicator {})
    }

    pub fn new_with_transcript<W: std::io::Write + Send + Sync + 'static>(
        backend: ProverBackend,
        transcript: W,
    ) -> Result<Self> {
        Ok(Communicator {})
    }

    pub fn write_smt<I: Into<SmtExpr>>(&mut self, expr: I) -> Result<()> {
        Ok(())
    }

    pub fn get_model(&mut self) -> Result<String> {
        Ok("".to_string())
    }

    pub fn check_sat(&mut self) -> Result<ProverResponse> {
        Ok(ProverResponse::Sat)
    }
}

impl std::fmt::Write for Communicator {
    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        Ok(())
    }
}
