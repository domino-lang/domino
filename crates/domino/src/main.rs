// SPDX-License-Identifier: MIT OR Apache-2.0

// We have a lot of large errors.
// This is fine for now. We will want to address that at some point in the future.
#![allow(clippy::result_large_err)]

/*

What is the functionality of the tool:
- game hops
  - count epsilons
- assumption
- game description (= composition)
- package
- proof types:
  - code equality
  - assumption application
  - hybrid argument (n-wise parallel composition)
- compute and verify proofs
- generate latex + proof viewer

What do we need for this:
- internal representation of multi-step/multi-game-hop proofs
  - type-checking + rewriting rather than smt
    - rewriting based on assumption or code equivalence
    - user says what rewrite rule to use
- would be nice to pin down directory structure a bit
  - this sort of reflects the data structure for the entire proof, though

----

UI consists of two elements:
- CLI
- Directory Structure

----

$ ssp prove [-u] [real [ideal]]	# prove that games real and ideal are indistinguishable and show epsilons
                                 # also generates proofviewer html
                                # what happens with bugs in the proof?
                                #   each gamehop is a lemma/claim, and when we can't prove it, it can be flagged
                                # when -u is given, automatically re-prove and re-generate proof viewer, when a file is updated. also host a web-server to host proof viewer and give info on syntax errors (-u is for update. maybe w for watch?)
$ ssp check-syntax [pkg]	    # syntax check individual packages
$ ssp gen-latex                 # check syntax and generate latex cryptocode for packages
$ ssp explain [path]

----

project/
    ssp.toml  -- this is at least needed to indicate that this is the project root
    _build/ 	-- only generated, only read by the user
        code_eq/
            mapping_ideal
        proof_viewer/
            index.html
            ...
        latex/
            packages/
                ...
            graphs/
                ...
    packages/
        key.pkg.ssp
        prf.pkg.ssp
    assumptions/
        prf/
            real.comp.ssp
            ideal.comp.ssp
            // hard-code these names? allow overrides?
            //     maybe for now allow all names
            // type checker needs to validate that interfaces match up
            // - oracles
            // - parameters
            // - how to deal with security parameter?
            // - more?
    games/
        real.comp.ssp
        g1.comp.ssp
        g2.comp.ssp
        ...
        mapping.comp.ssp
        ideal.comp.ssp
    game_hops.toml
        // rough description:
        // real->g1: assumption
        // g1->g2: assumption
        // ...
        // mapping->ideal: code equivalence with code_eq/mapping-ideal_invariant.smt
    code_eq/
        mapping-ideal_invariant.smt

----

game_hops.toml:

This would be the contents is JSONy notation. We'll see how that looks like in toml.
[
    {
        Reduction: {
            left: PackageName
            right: PackageName
            assumption: AssumptionName
            optional:
                name: String
        }
    },
    {
        Equivalence: {
            left: PackageName
            right: PackageName
            invariant: InvariantPath
            optional:
                name: String
        }
    },
    ..
]

*/

use clap::Parser;
use sspverif::project;

mod cli;
use crate::cli::*;

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

    project.prove(
        p.prover,
        p.transcript,
        p.parallel,
        &p.proof,
        p.proofstep,
        &p.oracle,
    )
}

fn explain(_game_name: &str, _dst: &Option<String>) -> Result<(), project::error::Error> {
    todo!("not implemented");
    /*
        let data = project::Project::load()?.explain_game(game_name)?;

        match dst {
            Some(dst) => std::fs::write(dst, data)?,
            None => println!("{data}"),
        }
    */
    // Ok(())
}

fn latex(l: &Latex) -> Result<(), project::error::Error> {
    let project_root = project::find_project_root()?;
    let files = project::Files::load(&project_root)?;
    let project = project::Project::load(&files)?;

    project.latex(l.prover)
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

fn wire_check(game_name: &str, dst_idx: usize) -> Result<(), project::error::Error> {
    /*
    let project_root = project::find_project_root()?;
    let files = project::Files::load(&project_root)?;
    let project = project::Project::load(&files)?;

    project.print_wire_check_smt(game_name, dst_idx);
    */
    Ok(())
}

fn main() -> miette::Result<()> {
    let cli = Cli::parse();

    let result = match &cli.command {
        Commands::Prove(p) => prove(p),
        Commands::Proofsteps => proofsteps(),
        Commands::Latex(l) => latex(l),
        Commands::Explain(Explain { game_name, output }) => explain(game_name, output),
        Commands::WireCheck(args) => wire_check(&args.game_name, args.dst_idx),
        Commands::Format(f) => format(f),
    };

    result.map_err(miette::Report::new)
}
