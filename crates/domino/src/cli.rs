// SPDX-License-Identifier: MIT OR Apache-2.0

use clap::Subcommand;
use wildcard::Wildcard;

use sspverif::{project::configuration::*, util::smtsolver::process::SolverVariant};

#[derive(Subcommand, Debug)]
pub(crate) enum Commands {
    /// Export to LaTeX
    Latex(Latex),

    /// Prove the whole project.
    Prove(Prove),

    /// Reformat file or directory
    Format(Format),

    Gamehops(Gamehops),
}

#[derive(clap::Args, Debug)]
#[clap(author, version, about, long_about = None)]
pub(crate) struct Format {
    /// Input to reformat
    pub(crate) input: Option<std::path::PathBuf>,
}

#[derive(clap::Args, Debug)]
#[clap(author, version, about, long_about = None)]
pub(crate) struct Latex {
    /// Solver for graph layouting
    /// TODO: given we have a default here, it seems impossible to choose none
    #[clap(short, long, default_value = "z3")]
    pub(crate) smtsolver: Option<SolverVariant>,
    /// Path to the Domino project. Defaults to searching the current
    /// directory and its ancestors for an `ssp.toml`.
    #[clap(long)]
    pub(crate) path: Option<std::path::PathBuf>,
}

#[derive(clap::Args, Debug)]
#[clap(author, version, about, long_about = None)]
pub(crate) struct Prove {
    /// Path to the Domino project. Defaults to searching the current
    /// directory and its ancestors for an `ssp.toml`.
    #[clap(long)]
    pub(crate) path: Option<std::path::PathBuf>,
    #[clap(short, long, default_value = "cvc5")]
    pub(crate) smtsolver: SolverVariant,
    #[clap(short, long)]
    pub(crate) transcript: bool,
    // only check randomness mapping is injective
    #[clap(long)]
    pub(crate) injective_randmap: bool,
    #[clap(long)]
    pub(crate) invariant_start: bool,
    #[clap(long)]
    pub(crate) gamehop: Option<usize>,
    #[clap(long)]
    pub(crate) theorem: Option<String>,
    #[clap(long)]
    pub(crate) oracle: Option<String>,
    #[clap(long)]
    pub(crate) claim: Option<String>,
    #[clap(long, default_value_t = 1)]
    pub(crate) parallel: usize,
}

#[derive(clap::Args, Debug)]
#[clap(author, version, about, long_about = None)]
pub(crate) struct Gamehops {
    /// Path to the Domino project. Defaults to searching the current
    /// directory and its ancestors for an `ssp.toml`.
    #[clap(long)]
    pub(crate) path: Option<std::path::PathBuf>,
}

impl ProveConfiguration for Prove {
    type SolverBackend = sspverif::util::smtsolver::process::ProcessSmtSolverBackend;

    fn solver_backend(&self) -> Self::SolverBackend {
        sspverif::util::smtsolver::process::ProcessSmtSolverBackend::new(self.smtsolver)
    }

    fn transcript(&self) -> bool {
        self.transcript
    }

    fn parallel(&self) -> usize {
        self.parallel
    }

    fn theorem_requested(&self, theorem: &str) -> bool {
        self.theorem
            .as_ref()
            .map(|name| theorem == name)
            .unwrap_or(true)
    }

    fn gamehop_requested(&self, gamehop: usize) -> bool {
        self.gamehop
            .as_ref()
            .map(|hop| *hop == gamehop)
            .unwrap_or(true)
    }

    fn claim_requested(&self, claim: &str) -> bool {
        let req_claim = self
            .claim
            .as_ref()
            .map(|req| Wildcard::new(req.as_bytes()).unwrap());
        match req_claim {
            Some(req_claim) => req_claim.is_match(claim.as_bytes()),
            None => true,
        }
    }

    fn oracle_requested(&self, export: &str) -> bool {
        if let Some(name) = &self.oracle {
            export == name
        } else {
            true
        }
    }

    fn restricted_requests(&self) -> bool {
        self.injective_randmap
            || self.invariant_start
            || self.claim.is_some()
            || self.oracle.is_some()
    }

    fn invariant_start_requested(&self) -> bool {
        self.invariant_start
    }
    fn injectivity_requested(&self) -> bool {
        self.injective_randmap
    }
}
