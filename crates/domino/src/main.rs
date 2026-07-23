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
#[error("{0}")]
#[diagnostic(code(cli::incompatible_arguments))]
pub struct IncompatibleArgumentsError(pub &'static str);

#[allow(clippy::large_enum_variant)]
#[derive(Debug, Error, Diagnostic)]
enum Error {
    #[error(transparent)]
    #[diagnostic(transparent)]
    ProjectError(#[from] project::error::Error),
    #[error(transparent)]
    #[diagnostic(transparent)]
    IncompatibleArgumentsErrorError(#[from] IncompatibleArgumentsError),
    #[error("could not read model file")]
    ModelFileReadError(#[from] std::io::Error),
    #[error(transparent)]
    #[diagnostic(transparent)]
    ModelViewError(#[from] sspverif::modelview::Error),
}

fn proofsteps(p: &Proofsteps) -> Result<(), Error> {
    let project_root = project::directory::find_project_root()?;
    let files = project::DirectoryFiles::load(&project_root)?;
    let project = project::DirectoryProject::load(&files)?;

    if p.proofstep.is_some() && p.proof.is_none() {
        return Err(IncompatibleArgumentsError(
            "Need to specify a proof when specifying a proofstep",
        )
        .into());
    }
    if p.claim.is_some() && p.oracle.is_none() {
        return Err(IncompatibleArgumentsError(
            "Need to specify an oracle when specifying a claim",
        )
        .into());
    }

    project.proofsteps(&p.proof, &p.proofstep, &p.oracle, &p.claim)?;
    Ok(())
}

fn prove(p: &Prove) -> Result<(), Error> {
    let project_root = project::directory::find_project_root()?;
    let files = project::DirectoryFiles::load(&project_root)?;
    let project = project::DirectoryProject::load(&files)?;

    if p.proofstep.is_none() || p.proof.is_some() {
        let smtsolver =
            sspverif::util::smtsolver::process::ProcessSmtSolverBackend::new(p.smtsolver);
        project.prove(
            &smtsolver,
            p.transcript,
            p.parallel,
            &p.proof,
            &p.proofstep,
            &p.oracle,
            &p.claim,
        )?;
    } else {
        return Err(IncompatibleArgumentsError(
            "Need to specify a proof when specifying a proofstep",
        )
        .into());
    }
    Ok(())
}

fn model(m: &Model) -> Result<(), Error> {
    // Loading the project is best-effort here: the model parser/viewer is still useful without
    // one (it just can't resolve names back to package/oracle semantics), so a missing or
    // unparseable project is a warning, not a hard error.
    let files = project::directory::find_project_root()
        .and_then(|root| project::DirectoryFiles::load(&root))
        .inspect_err(|err| {
            eprintln!(
                "warning: could not load a Domino project ({err}); showing raw model values only"
            );
        })
        .ok();

    let project = files.as_ref().and_then(|files| {
        project::DirectoryProject::load(files)
            .inspect_err(|err| {
                eprintln!(
                    "warning: could not load a Domino project ({err}); showing raw model values only"
                );
            })
            .ok()
    });

    let content = std::fs::read_to_string(&m.model_file)?;
    let report = sspverif::modelview::analyze(project.as_ref(), &content)?;
    println!("{report}");

    Ok(())
}

fn inline(i: &Inline) -> Result<(), Error> {
    let project_root = project::directory::find_project_root()?;
    let files = project::DirectoryFiles::load(&project_root)?;
    let project = project::DirectoryProject::load(&files)?;

    let rendered = project.inline(&i.proof, i.proofstep, &i.oracle)?;
    println!("{rendered}");
    Ok(())
}

fn latex(l: &Latex) -> Result<(), Error> {
    let project_root = project::directory::find_project_root()?;
    let files = project::DirectoryFiles::load(&project_root)?;
    let project = project::DirectoryProject::load(&files)?;

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
        let root = crate::project::directory::find_project_root();
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
        Commands::Inline(i) => inline(i),
        Commands::Latex(l) => latex(l),
        Commands::Format(f) => format(f),
        Commands::Model(m) => model(m),
    };

    result.map_err(miette::Report::new)
}
