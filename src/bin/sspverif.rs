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
use clap::{Parser, Subcommand};
use sspverif::project::{self, error::Result};
use sspverif::util::prover_process::ProverBackend;

#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
#[clap(propagate_version = true)]
struct Cli {
    #[clap(subcommand)]
    command: Commands,
}

#[derive(Subcommand, Debug)]
enum Commands {
    /// Export to LaTeX
    Latex,

    /// Give information about the provided code
    Explain(Explain),

    // Prove the whole project.
    Prove(Prove),
}

#[derive(clap::Args, Debug)]
#[clap(author, version, about, long_about = None)]
struct Explain {
    game_name: String,
    #[clap(short, long)]
    output: Option<String>,
}

#[derive(clap::Args, Debug)]
#[clap(author, version, about, long_about = None)]
struct Prove {
    #[clap(short, long, default_value = "cvc5")]
    prover: ProverBackend,
    #[clap(short, long)]
    transcript: bool,
}

fn prove(p: &Prove) -> Result<()> {
    project::Project::load()?.prove(p.prover, p.transcript)
}

fn explain(_game_name: &str, _dst: &Option<String>) -> Result<()> {
    todo!();
    /*
        let data = project::Project::load()?.explain_game(game_name)?;

        match dst {
            Some(dst) => std::fs::write(dst, data)?,
            None => println!("{data}"),
        }
    */
    // Ok(())
}

fn latex() -> Result<()> {
    project::Project::load()?.latex()
}

fn main() {
    let cli = Cli::parse();

    let result = match &cli.command {
        Commands::Prove(p) => prove(p),
        Commands::Latex => latex(),
        Commands::Explain(Explain { game_name, output }) => explain(game_name, output),
    };

    match result {
        Ok(_) => println!("success!"),
        Err(err) => println!("error: {err}"),
    }
}
