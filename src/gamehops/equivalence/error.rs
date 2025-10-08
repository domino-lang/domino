use crate::{
    gamehops::equivalence::Equivalence,
    util::prover_process::{ProverResponse, Result as ProverResponseResult},
};
use std::path::PathBuf;

#[derive(Debug)]
pub enum Error {
    UnsatAfterInvariantRead {
        equivalence: Equivalence,
        oracle_name: String,
    },
    ProverProcessError(crate::util::prover_process::Error),
    InvariantFileReadError {
        oracle_name: String,
        invariant_file_name: String,
        err: std::io::Error,
    },
    CompositionParamMismatch {
        left_game_inst_name: String,
        right_game_inst_name: String,
        mismatching_param_name: String,
    },
    ClaimTheoremFailed {
        claim_name: String,
        oracle_name: String,
        response: ProverResponse,
        modelfile: ProverResponseResult<PathBuf>,
    },
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Error::ProverProcessError(err) => Some(err),
            Error::InvariantFileReadError { err, .. } => Some(err),
            _ => None,
        }
    }
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::UnsatAfterInvariantRead {
                equivalence,
                oracle_name,
            } => {
                let left_game_inst_name = equivalence.left_name();
                let right_game_inst_name = equivalence.right_name();
                write!(
                    f,
                    "It seems the provided invariant file for the equivalence of \
                       game instances {left_game_inst_name} and {right_game_inst_name} \
                       contains unsatisfiable assert statements at oracle {oracle_name}. \
                       This is most likely an issue with the invariant file. \
                       Hint: Most invariant file should not contains assert statements at all."
                )
            }
            Error::ProverProcessError(err) => write!(f, "error communicating with prover: {err}"),
            Error::InvariantFileReadError {
                oracle_name,
                invariant_file_name,
                err,
            } => write!(f, "error reading invariant file {invariant_file_name} for oracle {oracle_name}: {err}"),
            Error::CompositionParamMismatch {
                left_game_inst_name,
                right_game_inst_name,
                mismatching_param_name,
            } => write!(f, "parameter {mismatching_param_name} does not match in equivalence theorem of game instances {left_game_inst_name} and {right_game_inst_name}"),
            Error::ClaimTheoremFailed {
                claim_name,
                oracle_name,
                response,
                modelfile,
            } => {
                match modelfile {
                    Ok(model) => {
                        let model = model.as_path().display();
                        write!(f, "error proving claim {claim_name} oracle {oracle_name}. status: {response}. model file: {model}.")
                    }
                    Err(model_err) => write!(f, "error proving claim {claim_name} oracle {oracle_name}. status: {response}. \
                                             Also, encountered the following error when trying to get the model: {model_err}"),
                }
            },
        }
    }
}

pub type Result<T> = std::result::Result<T, Error>;

impl From<crate::util::prover_process::Error> for Error {
    fn from(err: crate::util::prover_process::Error) -> Self {
        new_prover_process_error(err)
    }
}

pub(crate) fn new_prover_process_error(err: crate::util::prover_process::Error) -> Error {
    Error::ProverProcessError(err)
}

pub(crate) fn new_invariant_file_read_error(
    oracle_name: String,
    invariant_file_name: String,
    err: std::io::Error,
) -> Error {
    Error::InvariantFileReadError {
        oracle_name,
        invariant_file_name,
        err,
    }
}
