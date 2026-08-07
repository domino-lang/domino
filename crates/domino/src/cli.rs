// SPDX-License-Identifier: MIT OR Apache-2.0

use clap::Subcommand;
use sspverif::project::ProofStepSelector;
use sspverif::util::smtsolver::process::SolverVariant;

#[derive(Subcommand, Debug)]
pub(crate) enum Commands {
    /// Export to LaTeX
    Latex(Latex),

    /// Prove the whole project.
    Prove(Prove),

    /// Inline the code of an oracle for both sides of an equivalence proofstep, side by side.
    Inline(Inline),

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
    /// Path to the Domino project (or a subdirectory of it), used to resolve model values back
    /// to project semantics. Defaults to searching the current directory and its ancestors for
    /// an `ssp.toml`.
    #[clap(long, short = 'p')]
    pub(crate) project: Option<std::path::PathBuf>,
}

#[derive(clap::Args, Debug)]
#[clap(author, version, about, long_about = None)]
pub(crate) struct Format {
    /// Input to reformat
    pub(crate) input: Option<std::path::PathBuf>,
    /// Path to the Domino project (or a subdirectory of it) to reformat when no input is given.
    /// Defaults to searching the current directory and its ancestors for an `ssp.toml`.
    #[clap(long, short = 'p')]
    pub(crate) project: Option<std::path::PathBuf>,
}

#[derive(clap::Args, Debug)]
#[clap(author, version, about, long_about = None)]
pub(crate) struct Latex {
    /// Solver for graph layouting
    #[clap(short, long, default_value = "z3")]
    pub(crate) smtsolver: Option<SolverVariant>,
    // TODO: given we have a default here, it seems impossible to choose none
    /// Path to the Domino project (or a subdirectory of it). Defaults to searching the current
    /// directory and its ancestors for an `ssp.toml`.
    #[clap(long, short = 'p')]
    pub(crate) project: Option<std::path::PathBuf>,
}

#[derive(clap::Args, Debug)]
#[clap(author, version, about, long_about = None)]
pub(crate) struct Prove {
    /// Path to the Domino project (or a subdirectory of it). Defaults to searching the current
    /// directory and its ancestors for an `ssp.toml`.
    #[clap(long, short = 'p')]
    pub(crate) project: Option<std::path::PathBuf>,
    #[clap(short, long, default_value = "cvc5")]
    pub(crate) smtsolver: SolverVariant,
    #[clap(short, long)]
    pub(crate) transcript: bool,
    /// The proof step to restrict to, either by its 0-based index within the
    /// theorem (as printed by `domino proofsteps`) or by its name, e.g.
    /// "Left == Right" for an equivalence or "Left ~= Right" for a reduction.
    #[clap(long)]
    pub(crate) proofstep: Option<ProofStepSelector>,
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
    /// Path to the Domino project (or a subdirectory of it). Defaults to searching the current
    /// directory and its ancestors for an `ssp.toml`.
    #[clap(long, short = 'p')]
    pub(crate) project: Option<std::path::PathBuf>,
    /// Restrict to a single theorem
    #[clap(long)]
    pub(crate) proof: Option<String>,
    /// Restrict to a single game hop (proof step) within the theorem,
    /// either by its 0-based index or by its name (e.g. "Left == Right").
    #[clap(long)]
    pub(crate) proofstep: Option<ProofStepSelector>,
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

#[derive(clap::Args, Debug)]
#[clap(author, version, about, long_about = None)]
pub(crate) struct Inline {
    /// Path to the Domino project (or a subdirectory of it). Defaults to searching the current
    /// directory and its ancestors for an `ssp.toml`.
    #[clap(long, short = 'p')]
    pub(crate) project: Option<std::path::PathBuf>,
    /// Name of the theorem the equivalence proofstep belongs to.
    #[clap(long)]
    pub(crate) proof: String,
    /// Index (starting at 0) of the equivalence proofstep within the theorem.
    #[clap(long)]
    pub(crate) proofstep: usize,
    /// Name of the oracle to inline, as exported by the games in the proofstep.
    #[clap(long)]
    pub(crate) oracle: String,
}
