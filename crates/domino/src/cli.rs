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

    Proofsteps(Proofsteps),

    /// Symbolically execute both sides of an equivalence proofstep and debug one claim.
    Debug(Debug),

    /// Inline the code of an oracle for both sides of an equivalence proofstep, side by side.
    Inline(Inline),
}

#[derive(clap::Args, Debug)]
#[clap(author, version, about, long_about = None)]
pub(crate) struct Inline {
    /// Path to the Domino project. Defaults to searching the current
    /// directory and its ancestors for an `ssp.toml`.
    #[clap(long)]
    pub(crate) path: Option<std::path::PathBuf>,
    /// Name of the theorem the equivalence proofstep belongs to.
    #[clap(long)]
    pub(crate) proof: String,
    /// Index (starting at 0) of the equivalence proofstep within the theorem,
    /// as printed by `domino proofsteps`.
    #[clap(long)]
    pub(crate) proofstep: usize,
    /// Name of the oracle to inline, as exported by the games in the proofstep.
    #[clap(long)]
    pub(crate) oracle: String,
    /// Print without line numbers (useful for diffing two runs).
    #[clap(long)]
    pub(crate) no_line_numbers: bool,
}

#[derive(clap::Args, Debug)]
#[clap(author, version, about, long_about = None)]
pub(crate) struct Debug {
    /// Path to the Domino project. Defaults to searching the current
    /// directory and its ancestors for an `ssp.toml`.
    #[clap(long)]
    pub(crate) path: Option<std::path::PathBuf>,
    /// Name of the theorem.
    #[clap(long)]
    pub(crate) proof: String,
    /// Index (starting at 0) of the equivalence proofstep, as printed by `domino proofsteps`.
    #[clap(long)]
    pub(crate) proofstep: usize,
    /// Exported oracle name.
    #[clap(long)]
    pub(crate) oracle: String,
    /// Claim to debug. Required — one claim per run.
    #[clap(long)]
    pub(crate) claim: String,
    /// Ask the solver which branches of the LEFT oracle are reachable (default: explore all).
    #[clap(long)]
    pub(crate) check_left: bool,
    /// Do NOT ask the solver about the RIGHT oracle's branches (default: it does ask).
    /// Skips the vacuity check, so unreachable pairs fall through to "verified" — a
    /// diagnostic escape hatch, not the recommended mode.
    #[clap(long)]
    pub(crate) no_check_right: bool,
    /// Per-query solver timeout in milliseconds (cvc5 `tlimit-per`). A timeout counts
    /// as `unknown` (explored, never pruned, never "verified").
    #[clap(long)]
    pub(crate) timeout: Option<u64>,
    /// Give up after this many explored paths (left paths + right paths per left path).
    #[clap(long, default_value_t = 1000)]
    pub(crate) max_paths: usize,
    /// Output directory. Defaults to
    /// `_build/debug/<theorem>/<left>-<right>/<oracle>/<claim>/`.
    #[clap(long)]
    pub(crate) out: Option<std::path::PathBuf>,
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
    pub(crate) proofstep: Option<usize>,
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
    /// Path to the Domino project. Defaults to searching the current
    /// directory and its ancestors for an `ssp.toml`.
    #[clap(long)]
    pub(crate) path: Option<std::path::PathBuf>,
}
