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
use sspverif::writers::easycrypt::export::{ExportedTheorem, SkipNote};

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
pub struct IncompatibleArguments;

#[derive(Error, Diagnostic, Debug)]
#[error(
    "`domino debug` needs the native cvc5 backend, which is behind the `cvc5-lib` cargo feature"
)]
#[diagnostic(help(
    "rebuild with `cargo build --features cvc5-lib` (see the cvc5-lib section of Readme.md \
     and scripts/setup-cvc5-lib.sh for the one-time prerequisites)"
))]
pub struct Cvc5LibNotEnabled;

#[derive(Error, Diagnostic, Debug)]
#[error("`domino debug` found unresolved pairs (GOAL FAILS / inconclusive) or stopped early")]
#[diagnostic(code(debug::claim_not_verified))]
pub struct DebugNotVerified;

#[derive(Error, Diagnostic, Debug)]
#[error("`domino easycrypt --check-alignment` found {0} mismatches (see the report above)")]
#[diagnostic(code(easycrypt::alignment_mismatch))]
pub struct AlignmentMismatch(pub usize);

#[derive(Error, Diagnostic, Debug)]
#[error(
    "`domino easycrypt --tactics` runs lockstep execution, which needs the native cvc5 backend \
     behind the `cvc5-lib` cargo feature"
)]
#[diagnostic(help(
    "rebuild with `cargo build --features cvc5-lib` (see the cvc5-lib section of Readme.md \
     and scripts/setup-cvc5-lib.sh for the one-time prerequisites)"
))]
pub struct TacticsNeedCvc5Lib;

#[derive(Error, Diagnostic, Debug)]
#[error("theorem `{0}` not found")]
#[diagnostic(code(cli::theorem_not_found))]
pub struct TheoremNotFound(pub String);

#[derive(Error, Diagnostic, Debug)]
#[error("--oracle and --invariant-start cannot be used together")]
#[diagnostic(help(
    "--invariant-start restricts verification to the invariant start, which \
        doesn't involve any oracle, so --oracle has no effect there. \
        Pass only one of the two options."
))]
pub struct ReqOracleWithInvariantStart;

#[allow(clippy::large_enum_variant)]
#[allow(clippy::enum_variant_names)]
#[derive(Debug, Error, Diagnostic)]
enum Error {
    #[error(transparent)]
    #[diagnostic(transparent)]
    Project(#[from] project::error::Error),
    #[error(transparent)]
    #[diagnostic(transparent)]
    IncompatibleArguments(#[from] IncompatibleArguments),
    #[error(transparent)]
    #[diagnostic(transparent)]
    ReqOracleWithInvariantStart(#[from] ReqOracleWithInvariantStart),
    #[error(transparent)]
    #[diagnostic(transparent)]
    Cvc5LibNotEnabled(#[from] Cvc5LibNotEnabled),
    #[error(transparent)]
    #[diagnostic(transparent)]
    DebugNotVerified(#[from] DebugNotVerified),
    #[error(transparent)]
    #[diagnostic(transparent)]
    TheoremNotFound(#[from] TheoremNotFound),
    #[error(transparent)]
    #[diagnostic(transparent)]
    InlineRender(#[from] sspverif::debug::render::RenderError),
    #[error(transparent)]
    #[diagnostic(transparent)]
    AlignmentMismatch(#[from] AlignmentMismatch),
    #[error(transparent)]
    #[diagnostic(transparent)]
    TacticsNeedCvc5Lib(#[from] TacticsNeedCvc5Lib),
    #[error(transparent)]
    EcCheck(#[from] sspverif::easycrypt::check::CheckError),
    #[error(transparent)]
    EcTactics(#[from] sspverif::easycrypt::tactics::TacticsError),
    #[error(transparent)]
    EcSession(#[from] sspverif::easycrypt::session::SessionError),
    #[error(transparent)]
    #[diagnostic(transparent)]
    EcExport(#[from] sspverif::writers::easycrypt::EcExportError),
    #[error(transparent)]
    #[diagnostic(transparent)]
    ExportTree(#[from] sspverif::writers::easycrypt::overwrite::ExportTreeError),
    // Same shape as `project::error::Error::IOError` (no diagnostic span —
    // there is none to give a bare I/O failure). The only `std::io::Error`
    // site in this binary is `write_files` in `easycrypt()` below, so the
    // blanket `#[from]` can't yet mislabel an unrelated failure.
    #[error("io error writing the EasyCrypt export")]
    EcExportIo(#[from] std::io::Error),
    #[cfg(feature = "cvc5-lib")]
    #[error(transparent)]
    #[diagnostic(transparent)]
    Debug(#[from] sspverif::debug::driver::DebugError),
}

fn proofsteps(p: &Proofsteps) -> Result<(), Error> {
    let project_root = p
        .path
        .to_owned()
        .unwrap_or(project::directory::find_project_root()?);
    let files = project::DirectoryFiles::load(&project_root)?;
    let project = project::DirectoryProject::load(project_root, &files)?;

    project.proofsteps()?;
    Ok(())
}

fn prove(p: &Prove) -> Result<(), Error> {
    let project_root = p
        .path
        .to_owned()
        .unwrap_or(project::directory::find_project_root()?);
    let files = project::DirectoryFiles::load(&project_root)?;
    let project = project::DirectoryProject::load(project_root, &files)?;

    if p.proofstep.is_some() && p.proof.is_none() {
        return Err(IncompatibleArguments.into());
    }

    if p.invariant_start && p.oracle.is_some() {
        return Err(ReqOracleWithInvariantStart.into());
    }

    let smtsolver = sspverif::util::smtsolver::process::ProcessSmtSolverBackend::new(p.smtsolver);
    project.prove(
        &smtsolver,
        p.transcript,
        p.parallel,
        &p.proof,
        p.proofstep,
        &p.oracle,
        &p.claim,
        p.invariant_start,
        p.injective_randmap,
    )?;
    Ok(())
}

/// Best-effort Ctrl-C handling, from here on: the first press sets the returned flag and prints
/// `first`, a second press exits immediately with 130. If a handler is already installed the
/// run just is not interruptible — not fatal.
#[cfg(feature = "cvc5-lib")]
fn stop_on_ctrl_c(first: &'static str) -> std::sync::Arc<std::sync::atomic::AtomicBool> {
    use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
    use std::sync::Arc;

    let stop = Arc::new(AtomicBool::new(false));
    let flag = stop.clone();
    let hits = AtomicUsize::new(0);
    let _ = ctrlc::try_set_handler(move || {
        if hits.fetch_add(1, Ordering::Relaxed) == 0 {
            flag.store(true, Ordering::Relaxed);
            eprintln!("\n{first}");
        } else {
            std::process::exit(130);
        }
    });
    stop
}

#[cfg(feature = "cvc5-lib")]
fn debug(d: &Debug) -> Result<(), Error> {
    use std::io::IsTerminal;

    use sspverif::debug::driver::{run_debug_command, DebugOptions};
    use sspverif::debug::progress::{BarObserver, DebugObserver, NopObserver, PlainObserver};
    use sspverif::debug::smtout::SmtOut;

    // NB: `unwrap_or` would evaluate `find_project_root()?` eagerly even when
    // `--path` is given (and propagate its error). Match instead.
    let project_root = match &d.path {
        Some(path) => path.clone(),
        None => project::directory::find_project_root()?,
    };
    let files = project::DirectoryFiles::load(&project_root)?;
    let project = project::DirectoryProject::load(project_root, &files)?;

    let opts = DebugOptions {
        check_left: !d.no_check_left,
        check_right: !d.no_check_right,
        timeout_ms: d.timeout,
        max_paths: d.max_paths,
        smt_out: match d.smt {
            SmtOutArg::None => SmtOut::None,
            SmtOutArg::Failures => SmtOut::Failures,
            SmtOutArg::All => SmtOut::All,
            SmtOutArg::Deltas => SmtOut::Deltas,
        },
        transcript: d.transcript,
    };

    let backend = sspverif::util::smtsolver::cvc5lib::Cvc5LibBackend::new(true, d.timeout);

    let mut observer: Box<dyn DebugObserver> = match d.progress {
        ProgressMode::None => Box::new(NopObserver),
        ProgressMode::Plain => Box::new(PlainObserver::new()),
        ProgressMode::Bar => Box::new(BarObserver::new()),
        ProgressMode::Auto => {
            if std::io::stderr().is_terminal() {
                Box::new(BarObserver::new())
            } else {
                Box::new(PlainObserver::new())
            }
        }
    };

    // Best-effort Ctrl-C handling. The first press sets a flag the driver checks
    // at every fork (inside branch-pruning sweeps too) and at every pair
    // boundary; it then finishes the in-flight cvc5 query — which is a blocking
    // FFI call and cannot itself be cancelled, so `--timeout` bounds how long
    // that takes — and writes partial `trace.json` / `index.html`. A second
    // press exits immediately with 130. If a handler is already installed the
    // run just is not interruptible — not fatal.
    let stop = stop_on_ctrl_c(
        "debug: interrupt — finishing the current solver query, then writing partial results \
         (Ctrl-C again to abort now)",
    );

    if d.easycrypt {
        use sspverif::debug::lockstep_report::render_summary;
        use sspverif::debug::lockstep_run::{run_lockstep_command, LockstepDebugOptions};

        let run = run_lockstep_command(
            &project,
            &d.proof,
            d.proofstep,
            &d.oracle,
            &LockstepDebugOptions {
                timeout_ms: opts.timeout_ms,
                max_paths: opts.max_paths,
                smt_out: opts.smt_out,
                transcript: opts.transcript,
            },
            &backend,
            d.out.clone(),
            observer.as_mut(),
            Some(&stop),
        )?;
        print!("{}", render_summary(&run));
        if !run.is_ok() {
            return Err(DebugNotVerified.into());
        }
        return Ok(());
    }

    // clap guarantees `--claim` unless `--easycrypt`
    let claim = d.claim.as_deref().expect("`--claim` is required without `--easycrypt`");
    let run = run_debug_command(
        &project,
        &d.proof,
        d.proofstep,
        &d.oracle,
        claim,
        &opts,
        &backend,
        d.out.clone(),
        observer.as_mut(),
        Some(&stop),
    )?;

    // Story 17: the concise report goes to stdout; the full per-left-path tree is
    // in `summary.txt` (its `artifacts` block points at that and every other
    // file). The `Finished` event already cleared the progress bar inside
    // `run_debug_command`, so this never lands in a redrawn line.
    print!("{}", sspverif::debug::report::render_summary(&run));

    if !run.is_ok() {
        return Err(DebugNotVerified.into());
    }
    Ok(())
}

#[cfg(not(feature = "cvc5-lib"))]
fn debug(_d: &Debug) -> Result<(), Error> {
    Err(Cvc5LibNotEnabled.into())
}

fn inline(i: &Inline) -> Result<(), Error> {
    // NB: match rather than `unwrap_or` so `find_project_root()?` is not
    // evaluated (and its error propagated) when `--path` is given.
    let project_root = match &i.path {
        Some(path) => path.clone(),
        None => project::directory::find_project_root()?,
    };
    let files = project::DirectoryFiles::load(&project_root)?;
    let project = project::DirectoryProject::load(project_root, &files)?;

    let theorem = project
        .get_theorem(&i.proof)
        .ok_or_else(|| TheoremNotFound(i.proof.clone()))?;

    let render = if i.easycrypt {
        sspverif::debug::render::render_side_by_side_easycrypt
    } else {
        sspverif::debug::render::render_side_by_side
    };
    let listing = render(theorem, i.proofstep, &i.oracle, !i.no_line_numbers)?;
    print!("{listing}");
    Ok(())
}

/// `domino easycrypt`'s stdout report (§3.3 of the story): one block per
/// exported theorem, fixed-width labels so the fields line up.
fn print_easycrypt_report(theorem_name: &str, exported: &ExportedTheorem, wrote_path: &str) {
    fn types_line(exported: &ExportedTheorem) -> String {
        let bits = exported.bits_type_names.join(", ");
        let funcs = exported.fn_const_names.join(", ");
        match (bits.is_empty(), funcs.is_empty()) {
            (true, true) => "(none)".to_string(),
            (false, true) => bits,
            (true, false) => funcs,
            (false, false) => format!("{bits}; {funcs}"),
        }
    }

    fn packages_line(exported: &ExportedTheorem) -> String {
        if exported.package_variant_names.is_empty() {
            return "(none)".to_string();
        }
        let noun = if exported.package_variant_names.len() == 1 {
            "variant"
        } else {
            "variants"
        };
        format!(
            "{} {noun} ({})",
            exported.package_variant_names.len(),
            exported.package_variant_names.join(", ")
        )
    }

    fn games_line(exported: &ExportedTheorem) -> String {
        if exported.game_names.is_empty() {
            "(none)".to_string()
        } else {
            exported.game_names.join(", ")
        }
    }

    // One line per skipped-hop kind (reduction/hybrid/conjecture), grouped
    // in first-seen order, naming every pair that kind covers — "every
    // skipped hop is named with its kind and the reason" (§3.3). At most
    // three kinds ever exist, so a linear scan beats standing up a map just
    // to fake insertion order.
    fn skipped_lines(skipped: &[SkipNote]) -> Vec<String> {
        let mut groups: Vec<(&str, &str, Vec<String>)> = Vec::new();
        for note in skipped {
            let pair = format!("{} ~ {}", note.left, note.right);
            match groups.iter_mut().find(|(kind, ..)| *kind == note.kind) {
                Some((_, _, pairs)) => pairs.push(pair),
                None => groups.push((note.kind, note.reason, vec![pair])),
            }
        }
        groups
            .into_iter()
            .map(|(kind, reason, pairs)| {
                let noun = if pairs.len() == 1 { "hop" } else { "hops" };
                format!(
                    "{} {kind} {noun} ({}): {reason}",
                    pairs.len(),
                    pairs.join(", ")
                )
            })
            .collect()
    }

    fn randomness_line(exported: &ExportedTheorem) -> Option<String> {
        if exported.randomness_mapping_oracles == 0 {
            return None;
        }
        let (noun, verb) = if exported.randomness_mapping_oracles == 1 {
            ("oracle", "declares")
        } else {
            ("oracles", "declare")
        };
        Some(format!(
            "{} {noun} {verb} an explicit randomness mapping (not translated by this exporter)",
            exported.randomness_mapping_oracles
        ))
    }

    // One line per translated equivalence hop (story 07 §3.2): the proof
    // file written, the oracle count, and the admit count (= oracle count
    // in v1) — plus a warning line when the proof trees name a different
    // oracle set than the game interface actually exports (§3: "warn if
    // that set differs ... do not silently drop an oracle").
    fn equivalence_lines(exported: &ExportedTheorem) -> Vec<String> {
        exported
            .equivalences
            .iter()
            .map(|eq| {
                let noun = if eq.oracle_count == 1 {
                    "oracle"
                } else {
                    "oracles"
                };
                format!(
                    "{} ({} {noun}, {} admits)",
                    eq.proof_file, eq.oracle_count, eq.admit_count
                )
            })
            .collect()
    }

    println!("theorem {theorem_name}");
    println!("  {:<12}{}", "types", types_line(exported));
    println!("  {:<12}{}", "packages", packages_line(exported));
    println!("  {:<12}{}", "games", games_line(exported));
    for line in skipped_lines(&exported.skipped) {
        println!("  {:<12}{}", "skipped", line);
    }
    if let Some(line) = randomness_line(exported) {
        println!("  {:<12}{}", "randomness", line);
    }
    for line in equivalence_lines(exported) {
        println!("  {:<12}{}", "equivalence", line);
    }
    for eq in &exported.equivalences {
        if let Some(warning) = &eq.oracle_set_mismatch {
            println!("  {:<12}{}", "warning", warning);
        }
    }
    println!(
        "  {:<12}{} ({} files)",
        "wrote",
        wrote_path,
        exported.files.len()
    );
}

fn easycrypt(e: &Easycrypt) -> Result<(), Error> {
    let project_root = match &e.project {
        Some(path) => path.clone(),
        None => project::directory::find_project_root()?,
    };
    let files = project::DirectoryFiles::load(&project_root)?;
    let project = project::DirectoryProject::load(project_root.clone(), &files)?;

    let theorem_names: Vec<String> = match &e.theorem {
        Some(name) => {
            if project.get_theorem(name).is_none() {
                return Err(TheoremNotFound(name.clone()).into());
            }
            vec![name.clone()]
        }
        None => {
            let mut names: Vec<String> = project.theorems().map(String::from).collect();
            names.sort();
            names
        }
    };

    let out_base = e
        .out
        .clone()
        .unwrap_or_else(|| project_root.join("_build/easycrypt"));

    // Story 32 (ADR 0004): refuse to overwrite anything but run artifacts. First, so that
    // it fires before the EasyCrypt probe and before any export work.
    if !e.force {
        let names: Vec<&str> = theorem_names.iter().map(String::as_str).collect();
        sspverif::writers::easycrypt::overwrite::check_export_tree(&out_base, &names)?;
    }

    if e.tactics {
        // fail early and clearly: a solver and a `-json`-capable EasyCrypt are prerequisites
        #[cfg(not(feature = "cvc5-lib"))]
        return Err(TacticsNeedCvc5Lib.into());
        #[cfg(feature = "cvc5-lib")]
        drop(sspverif::easycrypt::session::Session::start(&std::env::temp_dir())?);
    }

    // Build every requested theorem fully in memory first, and only start
    // writing once *all* of them succeeded. §3.2 states this per theorem
    // ("a failed export must not leave a half-written tree"); extending it
    // across the whole invocation is a deliberate choice, not an accident —
    // without it, plain `domino easycrypt` (no `--theorem`) on a project
    // where only *some* theorems fail (e.g. `example-projects/yao`, where
    // `HybridSecurity`/`LayerSecurity` export cleanly but `Yao`/`Yao3Layer`
    // don't) would leave the successful theorems' directories on disk next
    // to a top-level error, contradicting §4's "writes no files" bullet for
    // that exact project.
    use sspverif::writers::easycrypt::progress::{
        BarExportObserver, ExportEvent, ExportObserver, LoggingExportObserver, NopExportObserver,
        PlainExportObserver,
    };
    // Story 21: progress goes to stderr only; stdout and the written files do not depend on it.
    let make_observer = || -> Box<dyn ExportObserver> {
        match e.progress {
            ProgressMode::None => Box::new(NopExportObserver),
            ProgressMode::Plain => Box::new(PlainExportObserver::new()),
            ProgressMode::Bar => Box::new(BarExportObserver::new()),
            ProgressMode::Auto => {
                use std::io::IsTerminal;
                if std::io::stderr().is_terminal() {
                    Box::new(BarExportObserver::new())
                } else {
                    Box::new(PlainExportObserver::new())
                }
            }
        }
    };
    let mut observer = make_observer();
    // the export phases, for the live page of `--tactics` (story 28)
    let mut logging = LoggingExportObserver::new(observer.as_mut());

    let mut exports = Vec::with_capacity(theorem_names.len());
    for (i, name) in theorem_names.iter().enumerate() {
        let theorem = project.get_theorem(name).unwrap();
        logging.on_event(&ExportEvent::TheoremStarted {
            name,
            index: i + 1,
            total: theorem_names.len(),
        });
        let exported = sspverif::writers::easycrypt::export::export_theorem_observed(
            theorem,
            &project,
            &mut logging,
        )?;
        logging.on_event(&ExportEvent::TheoremFinished { name });
        exports.push((name.clone(), exported));
    }

    let theorem_outs: Vec<std::path::PathBuf> =
        exports.iter().map(|(name, _)| out_base.join(name)).collect();
    let outputs: Vec<_> = exports
        .iter()
        .zip(&theorem_outs)
        .map(|((name, exported), out)| (name.as_str(), out.as_path(), &exported.files))
        .collect();
    sspverif::writers::easycrypt::export::write_all_observed(&outputs, &mut logging)?;
    #[cfg_attr(not(feature = "cvc5-lib"), allow(unused_variables))]
    let phase_log = logging.into_log();
    drop(observer);

    for (i, (name, exported)) in exports.iter().enumerate() {
        if i > 0 {
            println!();
        }
        let theorem_out = out_base.join(name);

        let display_path = theorem_out
            .strip_prefix(&project_root)
            .map(|p| p.display().to_string())
            .unwrap_or_else(|_| theorem_out.display().to_string());
        print_easycrypt_report(name, exported, &display_path);
    }

    #[cfg(feature = "cvc5-lib")]
    if e.tactics {
        use sspverif::easycrypt::tactics::{
            read_smt_hints, run_tactics_observed, EcTranscriptMode, TacticsOptions,
            WriteGranularity,
        };

        let backend = sspverif::util::smtsolver::cvc5lib::Cvc5LibBackend::new(true, None);
        let options = TacticsOptions {
            proofstep: e.proofstep,
            oracle: e.oracle.clone(),
            ec_timeout: std::time::Duration::from_secs(e.ec_timeout),
            smt_hints: read_smt_hints(&project_root)?,
            lockstep_timeout_ms: None,
            rung0: !e.no_rung0,
            leaf_budget: std::time::Duration::from_secs(e.leaf_budget),
            ec_transcript: match e.ec_transcript {
                EcTranscriptArg::Capped => EcTranscriptMode::Capped,
                EcTranscriptArg::Full => EcTranscriptMode::Full,
            },
            write_granularity: match e.write_granularity {
                WriteGranularityArg::Oracle => WriteGranularity::Oracle,
                WriteGranularityArg::Node => WriteGranularity::Node,
            },
            stop: Some(stop_on_ctrl_c(
                "easycrypt: interrupt — stopping the current EasyCrypt sentence, then writing the \
                 partial proof (Ctrl-C again to abort now)",
            )),
        };
        for (name, exported) in &exports {
            let theorem = project.get_theorem(name).unwrap();
            let theorem_out = out_base.join(name);
            let result = run_tactics_observed(
                theorem,
                &project,
                exported,
                &theorem_out,
                &backend,
                &options,
                make_observer(),
                &phase_log.phases_of(name),
            )?;
            let report = result.render();
            println!();
            print!("{report}");
            if result.interrupted().is_some() {
                // a partial proof is not a success; 130 is what a second Ctrl-C exits with too
                use std::io::Write as _;
                let _ = std::io::stdout().flush();
                std::process::exit(130);
            }
        }
    }

    if e.check_alignment {
        let mut mismatches = 0;
        for (name, exported) in &exports {
            let theorem = project.get_theorem(name).unwrap();
            let theorem_out = out_base.join(name);
            let options = sspverif::easycrypt::check::CheckOptions {
                proofstep: e.proofstep,
                oracle: e.oracle.clone(),
            };
            let alignment = sspverif::easycrypt::check::check_alignment(
                theorem,
                exported,
                &theorem_out,
                &options,
            )?;
            let report = alignment.render();
            println!();
            print!("{report}");
            std::fs::write(theorem_out.join("alignment.txt"), &report)?;
            mismatches += alignment.mismatch_count();
        }
        if mismatches > 0 {
            return Err(AlignmentMismatch(mismatches).into());
        }
    }

    Ok(())
}

fn latex(l: &Latex) -> Result<(), Error> {
    let project_root = l
        .path
        .to_owned()
        .unwrap_or(project::directory::find_project_root()?);
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
        Commands::Latex(l) => latex(l),
        Commands::Format(f) => format(f),
        Commands::Debug(d) => debug(d),
        Commands::Inline(i) => inline(i),
        Commands::Easycrypt(e) => easycrypt(e),
    };

    result.map_err(miette::Report::new)
}
