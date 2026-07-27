// SPDX-License-Identifier: MIT OR Apache-2.0

use clap::Subcommand;
use sspverif::util::smtsolver::process::SolverVariant;

#[derive(Subcommand, Debug)]
pub(crate) enum Commands {
    /// Export to LaTeX
    Latex(Latex),

    /// Prove the whole project.
    Prove(Prove),

    /// Reformat file or directory
    Format(Format),

    /// Parse a cvc5 model (e.g. one produced by a failed `prove`) and explain it in terms of
    /// this Domino project's theorems, oracles and package states.
    Model(Model),

    Proofsteps(Proofsteps),
}

#[derive(clap::Args, Debug)]
#[clap(author, version, about, long_about = None)]
pub(crate) struct Model {
    /// Path to the cvc5 model file (e.g. as produced by `domino prove --transcript`, or the
    /// model file referenced in a failed proof's error message).
    pub(crate) model_file: std::path::PathBuf,
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
    #[clap(short, long, default_value = "z3")]
    pub(crate) smtsolver: Option<SolverVariant>,
    // TODO: given we have a default here, it seems impossible to choose none
}

#[derive(clap::Args, Debug)]
#[clap(author, version, about, long_about = None)]
pub(crate) struct Prove {
    #[clap(short, long, default_value = "cvc5")]
    pub(crate) smtsolver: SolverVariant,
    #[clap(short, long)]
    pub(crate) transcript: bool,
    /// Name of the proof step, e.g. "Left = Right" for an equivalence or
    /// "Left ~= Right" for a reduction. See `domino proofsteps` for the exact names.
    #[clap(long)]
    pub(crate) proofstep: Option<String>,
    #[clap(long)]
    pub(crate) proof: Option<String>,
    #[clap(long)]
    pub(crate) oracle: Option<String>,
    #[clap(long)]
    pub(crate) claim: Option<String>,
    #[clap(long, default_value_t = 1)]
    pub(crate) parallel: usize,
}

#[derive(clap::Args, Debug)]
#[clap(author, version, about, long_about = None)]
pub(crate) struct Proofsteps {
    /// Restrict to a single theorem
    #[clap(long)]
    pub(crate) proof: Option<String>,
    /// Restrict to a single game hop (proof step) within the theorem
    #[clap(long)]
    pub(crate) proofstep: Option<usize>,
    /// Restrict the lemma dependency graph to a single oracle instead of
    /// merging all of a game hop's oracles into one file
    #[clap(long)]
    pub(crate) oracle: Option<String>,
    /// Restrict the lemma dependency graph to a single claim's transitive
    /// dependencies (down to admitted/built-in leaves) instead of the whole
    /// oracle. Requires --oracle.
    #[clap(long)]
    pub(crate) claim: Option<String>,
}
