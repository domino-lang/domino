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

    Proofsteps,
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
    #[clap(long)]
    pub(crate) proofstep: Option<usize>,
    #[clap(long)]
    pub(crate) proof: Option<String>,
    #[clap(long)]
    pub(crate) oracle: Option<String>,
    #[clap(long, default_value_t = 1)]
    pub(crate) parallel: usize,
}
