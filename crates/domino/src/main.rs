// SPDX-License-Identifier: MIT OR Apache-2.0

// We have a lot of large errors.
// This is fine for now. We will want to address that at some point in the future.
#![allow(clippy::result_large_err)]

use clap::Parser;
use shadow_rs::shadow;
shadow!(build);

use sspverif::project;

mod cli;
use crate::cli::*;

#[derive(Parser, Debug)]
#[clap(author, version, long_version = build::CLAP_LONG_VERSION, about, long_about = None)]
#[clap(propagate_version = true)]
pub(crate) struct Cli {
    #[clap(subcommand)]
    pub(crate) command: Commands,
}

fn proofsteps() -> Result<(), project::error::Error> {
    let project_root = project::find_project_root()?;
    let files = project::Files::load(&project_root)?;
    let project = project::Project::load(&files)?;

    project.proofsteps()
}

fn prove(p: &Prove) -> Result<(), project::error::Error> {
    let project_root = project::find_project_root()?;
    let files = project::Files::load(&project_root)?;
    let project = project::Project::load(&files)?;

    assert!(p.proofstep.is_none() || p.proof.is_some());

    let smtsolver = sspverif::util::smtsolver::process::ProcessSmtSolverBackend::new(p.smtsolver);
    project.prove(
        &smtsolver,
        p.transcript,
        p.parallel,
        &p.proof,
        p.proofstep,
        &p.oracle,
    )
}

fn latex(l: &Latex) -> Result<(), project::error::Error> {
    let project_root = project::find_project_root()?;
    let files = project::Files::load(&project_root)?;
    let project = project::Project::load(&files)?;

    let smtsolver = l
        .smtsolver
        .map(sspverif::util::smtsolver::process::ProcessSmtSolverBackend::new);
    project.latex(&smtsolver)
}

fn format(f: &Format) -> Result<(), project::error::Error> {
    if let Some(input) = &f.input {
        sspverif::format::format_file(input)?;
    } else {
        let root = crate::project::find_project_root();
        sspverif::format::format_file(&root?)?;
    }
    Ok(())
}

fn main() -> miette::Result<()> {
    let cli = Cli::parse();

    let result = match &cli.command {
        Commands::Prove(p) => prove(p),
        Commands::Proofsteps => proofsteps(),
        Commands::Latex(l) => latex(l),
        Commands::Format(f) => format(f),
    };

    result.map_err(miette::Report::new)
}
