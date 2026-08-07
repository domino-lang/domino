// SPDX-License-Identifier: MIT OR Apache-2.0

// We have a lot of large errors.
// This is fine for now. We will want to address that at some point in the future.
#![allow(clippy::result_large_err)]

use clap::Parser;
use miette::Diagnostic;
use shadow_rs::shadow;
use thiserror::Error;
shadow!(build);

use sspverif::project;
use sspverif::project::Project;

mod cli;
use crate::cli::*;

#[derive(Parser, Debug)]
#[clap(author, version, long_version = build::CLAP_LONG_VERSION, about, long_about = None)]
#[clap(propagate_version = true)]
pub(crate) struct Cli {
    #[clap(subcommand)]
    pub(crate) command: Commands,
}

#[derive(Error, Diagnostic, Debug)]
#[error("Need to specify a proof when specifying a proofstep")]
#[diagnostic(code(cli::incompatible_arguments))]
pub struct IncompatibleArgumentsError;

#[allow(clippy::large_enum_variant)]
#[derive(Debug, Error, Diagnostic)]
enum Error {
    #[error(transparent)]
    #[diagnostic(transparent)]
    ProjectError(#[from] project::error::Error),
    #[error(transparent)]
    #[diagnostic(transparent)]
    IncompatibleArgumentsErrorError(#[from] IncompatibleArgumentsError),
}

fn proofsteps(p: &Proofsteps) -> Result<(), Error> {
    let project_root = project::directory::find_project_root(p.project.as_deref())?;
    let files = project::DirectoryFiles::load(&project_root)?;
    let project = project::DirectoryProject::load(project_root, &files)?;

    project.proofsteps()?;
    Ok(())
}

fn prove(p: &Prove) -> Result<(), Error> {
    let project_root = project::directory::find_project_root(p.project.as_deref())?;
    let files = project::DirectoryFiles::load(&project_root)?;
    let project = project::DirectoryProject::load(project_root, &files)?;

    if p.proofstep.is_none() || p.proof.is_some() {
        let smtsolver =
            sspverif::util::smtsolver::process::ProcessSmtSolverBackend::new(p.smtsolver);
        project.prove(
            &smtsolver,
            p.transcript,
            p.parallel,
            &p.proof,
            p.proofstep,
            &p.oracle,
        )?;
    } else {
        return Err(IncompatibleArgumentsError.into());
    }
    Ok(())
}

fn latex(l: &Latex) -> Result<(), Error> {
    let project_root = project::directory::find_project_root(l.project.as_deref())?;
    let files = project::DirectoryFiles::load(&project_root)?;
    let project = project::DirectoryProject::load(project_root, &files)?;

    let smtsolver = l
        .smtsolver
        .map(sspverif::util::smtsolver::process::ProcessSmtSolverBackend::new);
    project.latex(&smtsolver)?;
    Ok(())
}

fn format(f: &Format) -> Result<(), Error> {
    if let Some(input) = &f.input {
        sspverif::format::format_file(input)?;
    } else {
        let root = crate::project::directory::find_project_root(f.project.as_deref());
        sspverif::format::format_file(&root?)?;
    }
    Ok(())
}

fn main() -> miette::Result<()> {
    miette::set_hook(Box::new(|_| {
        Box::new(
            miette::MietteHandlerOpts::new()
                .show_related_errors_as_nested()
                .build(),
        )
    }))
    .unwrap();

    let cli = Cli::parse();

    let result = match &cli.command {
        Commands::Prove(p) => prove(p),
        Commands::Proofsteps(p) => proofsteps(p),
        Commands::Latex(l) => latex(l),
        Commands::Format(f) => format(f),
    };

    result.map_err(miette::Report::new)
}
