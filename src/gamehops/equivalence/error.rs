// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::{
    gamehops::equivalence::Equivalence,
    util::smtsolver::{Result as SmtSolverResponseResult, SmtSolverResponse},
};

use miette::Diagnostic;
use std::path::PathBuf;
use thiserror::Error;

#[derive(Debug, Error, Diagnostic)]
pub enum Error {
    // #[error(
    //     "It seems the provided invariant file for the equivalence of \
    //      game instances {left_game_inst_name} and {right_game_inst_name} \
    //      contains unsatisfiable assert statements at oracle {oracle_name}. \
    //      This is most likely an issue with the invariant file. \
    //      Hint: Most invariant file should not contains assert statements at all."
    // )]
    #[error("It seems the provided invariant file for the equivalence {} = {} contains unsatisfiable assert statements at oracle {oracle_name}.", equivalence.left_name(), equivalence.right_name())]
    UnsatAfterInvariantRead {
        equivalence: Equivalence,
        oracle_name: String,
    },
    #[error("error reading invariant file {invariant_file_name} for oracle {oracle_name}: {err}")]
    InvariantFileReadError {
        oracle_name: String,
        invariant_file_name: String,
        err: std::io::Error,
    },
    #[error("parameter {mismatching_param_name} does not match in equivalence theorem of game instances {left_game_inst_name} and {right_game_inst_name}")]
    CompositionParamMismatch {
        left_game_inst_name: String,
        right_game_inst_name: String,
        mismatching_param_name: String,
    },
    #[error("export(s) {mismatching_export_name} does not match in equivalence theorem of game instances {left_game_inst_name} and {right_game_inst_name}")]
    CompositionExportsMismatch {
        left_game_inst_name: String,
        right_game_inst_name: String,
        mismatching_export_name: String,
    },
    #[error(transparent)]
    ClaimTheoremFailed(#[from] ClaimTheoremFailedError),
    #[error("Failed invariant {left_game_inst_name} = {right_game_inst_name}")]
    ParallelEquivalenceError {
        left_game_inst_name: String,
        right_game_inst_name: String,

        #[related]
        failed_oracles: Vec<Error>,
    },
    #[error("found lemma named \"{lemma_name}\". Expected name ending in the name of the oracle. followed by a closing angle bracket")]
    IllegalLemmaName { lemma_name: String },
    #[error("found lemma named \"{lemma_name}\" for oracle \"{oracle_name}\" but couldn't find matching oracle")]
    UnknownLemmaName {
        lemma_name: String,
        oracle_name: String,
    },
    #[error("Expected 2-tuple (name type) for argument but got {argument}")]
    IncorrectArgument { argument: String },
    #[error("expected {expected} arguments but found {argument}")]
    IncorrectNumberOfArguments { argument: String, expected: String },
    #[error("define-game-invariant only valid in game contexts: {defn}")]
    RewriteNeedsGameContext { defn: String },
    #[error("define-package-invariant only valid in package contexts: {defn}")]
    RewriteNeedsPackageContext { defn: String },
    #[error(transparent)]
    ParserError(#[from] crate::util::smtparser::Error),
    #[error(transparent)]
    ProverProcessError(#[from] crate::util::smtsolver::Error),
}

#[derive(Debug, Error, Diagnostic)]
#[error("{oracle_name}: error proving claim {claim_name}. status: {response}. modelfile {}",
        if let Ok(modfile) = modelfile {modfile.to_str().unwrap()} else {""})]
pub struct ClaimTheoremFailedError {
    pub claim_name: String,
    pub oracle_name: String,
    pub response: SmtSolverResponse,
    pub modelfile: SmtSolverResponseResult<PathBuf>,
}

pub type Result<T> = std::result::Result<T, Error>;

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
