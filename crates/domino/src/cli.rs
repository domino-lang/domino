// SPDX-License-Identifier: MIT OR Apache-2.0

use clap::{Parser, Subcommand};
use sspverif::util::prover_process::ProverBackend;

#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
#[clap(propagate_version = true)]
pub(crate) struct Cli {
    #[clap(subcommand)]
    pub(crate) command: Commands,
}

#[derive(Subcommand, Debug)]
pub(crate) enum Commands {
    /// Export to LaTeX
    Latex(Latex),

    /// Give information about the provided code
    Explain(Explain),

    /// Prove the whole project.
    Prove(Prove),

    /// Print Wire Check SMTLIB code
    WireCheck(WireCheck),

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
    #[clap(short, long, default_value = "cvc5")]
    pub(crate) prover: Option<ProverBackend>,
    // TODO: given we have a default here, it seems impossible to choose none
}

#[derive(clap::Args, Debug)]
#[clap(author, version, about, long_about = None)]
pub(crate) struct Explain {
    pub(crate) game_name: String,
    #[clap(short, long)]
    pub(crate) output: Option<String>,
}

#[derive(clap::Args, Debug)]
#[clap(author, version, about, long_about = None)]
pub(crate) struct Prove {
    #[clap(short, long, default_value = "cvc5")]
    pub(crate) prover: ProverBackend,
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

#[derive(clap::Args, Debug)]
#[clap(author, version, about, long_about = None)]
pub(crate) struct WireCheck {
    #[clap(short, long)]
    pub(crate) game_name: String,
    #[clap(short, long)]
    pub(crate) dst_idx: usize,
}
