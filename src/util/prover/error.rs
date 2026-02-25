use thiserror::Error;

#[derive(Debug, Error)]
pub enum Error {
    #[error("error writing to prover process: {0}")]
    WriteError(#[from] std::fmt::Error),
    #[error("io error: {0}")]
    IOError(#[from] std::io::Error),
    #[cfg(feature = "process-solver")]
    #[error("error interacting with prover process: {0}")]
    ProcessError(#[from] crate::util::process::Error),
    #[error("prover error: {0}")]
    ProverError(String),
}

pub type Result<T> = std::result::Result<T, Error>;
