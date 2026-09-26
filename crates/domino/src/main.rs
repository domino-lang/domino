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
#[error("`domino easycrypt check-alignment` found {0} mismatches (see the report above)")]
#[diagnostic(code(easycrypt::alignment_mismatch))]
pub struct AlignmentMismatch(pub usize);

#[derive(Error, Diagnostic, Debug)]
#[error(
    "`domino easycrypt prove` runs lockstep execution, which needs the native cvc5 backend \
     behind the `cvc5-lib` cargo feature"
)]
#[diagnostic(help(
    "rebuild with `cargo build --features cvc5-lib` (see the cvc5-lib section of Readme.md \
     and scripts/setup-cvc5-lib.sh for the one-time prerequisites)"
))]
pub struct TacticsNeedCvc5Lib;

#[derive(Error, Diagnostic, Debug)]
#[error(
    "`domino easycrypt debug` runs lockstep execution, which needs the native cvc5 backend \
     behind the `cvc5-lib` cargo feature"
)]
#[diagnostic(help(
    "rebuild with `cargo build --features cvc5-lib` (see the cvc5-lib section of Readme.md \
     and scripts/setup-cvc5-lib.sh for the one-time prerequisites)"
))]
pub struct EcDebugNeedCvc5Lib;

#[derive(Error, Diagnostic, Debug)]
#[error("`--out` names one output directory, but this run covers {0} oracles")]
#[diagnostic(help(
    "name one oracle with `--proof`, `--proofstep` and `--oracle`, or drop `--out` to write \
     each run under `_build/debug/domino/`"
))]
pub struct OutNeedsOneOracle(pub usize);

#[derive(Error, Diagnostic, Debug)]
#[error("io error writing the debug artifacts")]
pub struct DebugIo(#[source] pub std::io::Error);

#[derive(Error, Diagnostic, Debug)]
#[error("`domino easycrypt debug` found joint paths that fail equal-output or the invariant, or stopped early")]
#[diagnostic(code(easycrypt::debug_not_verified))]
pub struct EcDebugNotVerified;

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
    #[diagnostic(transparent)]
    EcDebugNeedCvc5Lib(#[from] EcDebugNeedCvc5Lib),
    #[error(transparent)]
    #[diagnostic(transparent)]
    OutNeedsOneOracle(#[from] OutNeedsOneOracle),
    #[error(transparent)]
    #[diagnostic(transparent)]
    DebugIo(#[from] DebugIo),
    #[error(transparent)]
    #[diagnostic(transparent)]
    EcDebugNotVerified(#[from] EcDebugNotVerified),
    #[error(transparent)]
    EcDebug(#[from] sspverif::easycrypt::debug::EcDebugError),
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

    use sspverif::debug::driver::{run_debug_command, DebugError, DebugOptions};
    use sspverif::debug::layout::DOMINO_DEBUG_DIR;
    use sspverif::debug::lockstep_report::render_summary as render_lockstep_summary;
    use sspverif::debug::lockstep_run::{run_lockstep_domino, LockstepDebugOptions};
    use sspverif::debug::progress::{BarObserver, DebugObserver, NopObserver, PlainObserver};
    use sspverif::debug::smtout::SmtOut;
    use sspverif::debug::sweep::{self, SweepEntry};

    if d.proofstep.is_some() && d.proof.is_none() {
        return Err(IncompatibleArguments.into());
    }

    // NB: `unwrap_or` would evaluate `find_project_root()?` eagerly even when
    // `--path` is given (and propagate its error). Match instead.
    let project_root = match &d.path {
        Some(path) => path.clone(),
        None => project::directory::find_project_root()?,
    };
    let files = project::DirectoryFiles::load(&project_root)?;
    let project = project::DirectoryProject::load(project_root.clone(), &files)?;

    // Every filter is optional: omitted means all, given means only that (as in `prove`).
    let plan = sweep::plan(
        &project,
        d.proof.as_deref(),
        d.proofstep,
        d.oracle.as_deref(),
    )?;
    for skipped in &plan.skipped {
        eprintln!("{}", skipped.note());
    }
    if plan.targets.is_empty() {
        eprintln!("debug: the project has no equivalence proofstep to debug");
        return Ok(());
    }
    if plan.targets.len() > 1 && d.out.is_some() {
        return Err(OutNeedsOneOracle(plan.targets.len()).into());
    }
    // One oracle: today's concise report on stdout. Several: one line per oracle as it
    // finishes, then the failures of the whole project.
    let single = plan.targets.len() == 1;

    let smt_out = match d.smt {
        SmtOutArg::None => SmtOut::None,
        SmtOutArg::Failures => SmtOut::Failures,
        SmtOutArg::All => SmtOut::All,
        SmtOutArg::Deltas => SmtOut::Deltas,
    };
    let opts = DebugOptions {
        check_left: !d.no_check_left,
        check_right: !d.no_check_right,
        timeout_ms: d.timeout,
        max_paths: d.max_paths,
        smt_out,
        transcript: d.transcript,
        first_failure_per_claim: d.first_failure_per_claim,
    };
    let lockstep_opts = LockstepDebugOptions {
        timeout_ms: d.timeout,
        max_paths: d.max_paths,
        smt_out,
        transcript: d.transcript,
    };

    let backend = sspverif::util::smtsolver::cvc5lib::Cvc5LibBackend::new(true, d.timeout);

    let make_observer = || -> Box<dyn DebugObserver> {
        match d.progress {
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

    let mut entries: Vec<SweepEntry> = Vec::new();
    let mut claim_not_found: Option<DebugError> = None;
    for target in &plan.targets {
        let mut observer = make_observer();
        let entry = if d.lockstep {
            match run_lockstep_domino(
                &project,
                &target.theorem,
                target.proofstep,
                &target.oracle,
                d.claim.as_deref(),
                &lockstep_opts,
                &backend,
                d.out.clone(),
                observer.as_mut(),
                Some(&stop),
            ) {
                Ok(run) => {
                    if single {
                        print!("{}", render_lockstep_summary(&run));
                    }
                    SweepEntry::from_lockstep(target.clone(), &run)
                }
                Err(e @ DebugError::ClaimNotFound { .. }) if !single => {
                    claim_not_found = Some(e);
                    continue;
                }
                Err(e) => return Err(e.into()),
            }
        } else {
            match run_debug_command(
                &project,
                &target.theorem,
                target.proofstep,
                &target.oracle,
                d.claim.as_deref(),
                &opts,
                &backend,
                d.out.clone(),
                observer.as_mut(),
                Some(&stop),
            ) {
                Ok(run) => {
                    // Story 17: the concise report goes to stdout; the full per-left-path
                    // tree is in the summary file (its `artifacts` block points at that and
                    // every other file). The `Finished` event already cleared the progress
                    // bar inside `run_debug_command`, so this never lands in a redrawn line.
                    if single {
                        print!("{}", sspverif::debug::report::render_summary(&run));
                    }
                    SweepEntry::from_sequential(target.clone(), &run)
                }
                Err(e @ DebugError::ClaimNotFound { .. }) if !single => {
                    claim_not_found = Some(e);
                    continue;
                }
                Err(e) => return Err(e.into()),
            }
        };
        drop(observer);
        if !single {
            println!("{}", entry.one_line());
        }
        let interrupted = sweep::is_interrupted(&entry);
        entries.push(entry);
        if interrupted {
            break;
        }
    }

    // `--claim` names a claim only some oracles have: those that lack it are skipped, unless
    // none has it.
    if entries.is_empty() {
        if let Some(e) = claim_not_found {
            return Err(e.into());
        }
    }

    if !single && !entries.is_empty() {
        let table = sweep::failure_table(&entries);
        if !table.is_empty() {
            println!("\n{table}");
        }
        let root = project_root.join(DOMINO_DEBUG_DIR);
        let (index, summary) = sweep::write_index(&root, &entries).map_err(DebugIo)?;
        println!(
            "\nindex    {}\nsummary  {}",
            index.display(),
            summary.display()
        );
    }

    if entries.iter().any(|entry| !entry.ok) {
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

/// The export's progress observer (story 21): stderr only; stdout and the written files do not
/// depend on it.
fn export_observer(
    mode: ProgressMode,
) -> Box<dyn sspverif::writers::easycrypt::progress::ExportObserver> {
    use sspverif::writers::easycrypt::progress::{
        BarExportObserver, NopExportObserver, PlainExportObserver,
    };
    match mode {
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
}

/// Builds every theorem of `theorem_names` fully in memory. Callers write only once *all* of
/// them succeeded: a failed export must not leave a half-written tree, and extending that across
/// the whole invocation is deliberate. Without it, plain `domino easycrypt` (no `--theorem`) on
/// a project where only *some* theorems fail (e.g. `example-projects/yao`, where
/// `HybridSecurity`/`LayerSecurity` export cleanly but `Yao`/`Yao3Layer` don't) would leave the
/// successful theorems' directories on disk next to a top-level error.
fn export_in_memory<P: project::Project>(
    project: &P,
    theorem_names: &[String],
    logging: &mut sspverif::writers::easycrypt::progress::LoggingExportObserver<'_>,
) -> Result<Vec<(String, sspverif::writers::easycrypt::export::ExportedTheorem)>, Error> {
    use sspverif::writers::easycrypt::progress::{ExportEvent, ExportObserver};
    let mut exports = Vec::with_capacity(theorem_names.len());
    for (i, name) in theorem_names.iter().enumerate() {
        let theorem = project.get_theorem(name).unwrap();
        logging.on_event(&ExportEvent::TheoremStarted {
            name,
            index: i + 1,
            total: theorem_names.len(),
        });
        let exported =
            sspverif::writers::easycrypt::export::export_theorem_observed(theorem, project, logging)?;
        logging.on_event(&ExportEvent::TheoremFinished { name });
        exports.push((name.clone(), exported));
    }
    Ok(exports)
}

fn easycrypt(e: &Easycrypt) -> Result<(), Error> {
    let project_root = match &e.project {
        Some(path) => path.clone(),
        None => project::directory::find_project_root()?,
    };
    let files = project::DirectoryFiles::load(&project_root)?;
    let project = project::DirectoryProject::load(project_root.clone(), &files)?;
    let out_base = e
        .out
        .clone()
        .unwrap_or_else(|| project_root.join("_build/easycrypt"));

    match &e.command {
        None => {
            let theorem_names: Vec<String> = match &e.theorem {
                Some(name) => vec![name.clone()],
                None => {
                    let mut names: Vec<String> = project.theorems().map(String::from).collect();
                    names.sort();
                    names
                }
            };
            easycrypt_translate(e, &project, &project_root, &out_base, &theorem_names)
        }
        Some(EasycryptCommand::Prove(p)) => {
            easycrypt_prove(p, &project, &project_root, &out_base)
        }
        Some(EasycryptCommand::CheckAlignment(c)) => {
            easycrypt_check_alignment(c, &project, &out_base)
        }
        Some(EasycryptCommand::Debug(d)) => easycrypt_debug(d, &project, &out_base),
    }
}

/// `domino easycrypt`: translation only. Runs no EasyCrypt (story 35).
fn easycrypt_translate<P: project::Project>(
    e: &Easycrypt,
    project: &P,
    project_root: &std::path::Path,
    out_base: &std::path::Path,
    theorem_names: &[String],
) -> Result<(), Error> {
    use sspverif::writers::easycrypt::progress::LoggingExportObserver;
    for name in theorem_names {
        if project.get_theorem(name).is_none() {
            return Err(TheoremNotFound(name.clone()).into());
        }
    }

    // Story 32 (ADR 0004): refuse to overwrite anything but run artifacts. First, so that
    // it fires before any export work. A session record counts as translation output.
    if !e.force {
        let names: Vec<&str> = theorem_names.iter().map(String::as_str).collect();
        sspverif::writers::easycrypt::overwrite::check_export_tree(out_base, &names)?;
    }

    let mut observer = export_observer(e.progress);
    let mut logging = LoggingExportObserver::new(observer.as_mut());
    let exports = export_in_memory(project, theorem_names, &mut logging)?;

    let theorem_outs: Vec<std::path::PathBuf> =
        exports.iter().map(|(name, _)| out_base.join(name)).collect();
    if e.force {
        // the proofs the records describe are about to be overwritten by skeletons (story 35 §3.5)
        for out in &theorem_outs {
            sspverif::easycrypt::job::remove_session_records(out)?;
        }
    }
    let outputs: Vec<_> = exports
        .iter()
        .zip(&theorem_outs)
        .map(|((name, exported), out)| (name.as_str(), out.as_path(), &exported.files))
        .collect();
    sspverif::writers::easycrypt::export::write_all_observed(&outputs, &mut logging)?;
    drop(logging);
    drop(observer);

    for (i, (name, exported)) in exports.iter().enumerate() {
        if i > 0 {
            println!();
        }
        let theorem_out = out_base.join(name);

        let display_path = theorem_out
            .strip_prefix(project_root)
            .map(|p| p.display().to_string())
            .unwrap_or_else(|_| theorem_out.display().to_string());
        print_easycrypt_report(name, exported, &display_path);
    }
    Ok(())
}

/// The proof jobs' theorem: it must exist.
fn proof_job_theorem<P: project::Project>(project: &P, name: &str) -> Result<Vec<String>, Error> {
    if project.get_theorem(name).is_none() {
        return Err(TheoremNotFound(name.to_string()).into());
    }
    Ok(vec![name.to_string()])
}

/// `domino easycrypt prove` (story 35): one proof job per selected equivalence, one after the
/// other. Translation's files are created if missing and otherwise not touched (ADR 0006).
fn easycrypt_prove<P: project::Project>(
    p: &EcProve,
    project: &P,
    project_root: &std::path::Path,
    out_base: &std::path::Path,
) -> Result<(), Error> {
    #[cfg(not(feature = "cvc5-lib"))]
    {
        let _ = (p, project, project_root, out_base);
        Err(TacticsNeedCvc5Lib.into())
    }
    #[cfg(feature = "cvc5-lib")]
    {
        use sspverif::easycrypt::tactics::{
            read_smt_hints, run_tactics_observed, EcTranscriptMode, TacticsOptions,
            WriteGranularity,
        };
        use sspverif::writers::easycrypt::progress::LoggingExportObserver;

        let theorem_names = proof_job_theorem(project, &p.theorem)?;
        // fail early and clearly: a `-json`-capable EasyCrypt is a prerequisite
        drop(sspverif::easycrypt::session::Session::start(&std::env::temp_dir())?);

        let mut observer = export_observer(p.progress);
        let mut logging = LoggingExportObserver::new(observer.as_mut());
        // The proof job needs translation's result in memory (the equivalence setup and the
        // skeleton) and writes none of it over what is there.
        let exports = export_in_memory(project, &theorem_names, &mut logging)?;
        let phase_log = logging.into_log();
        drop(observer);

        let backend = sspverif::util::smtsolver::cvc5lib::Cvc5LibBackend::new(true, None);
        let options = TacticsOptions {
            proofstep: p.proofstep,
            oracle: p.oracle.clone(),
            ec_timeout: std::time::Duration::from_secs(p.ec_timeout),
            smt_hints: read_smt_hints(project_root)?,
            lockstep_timeout_ms: None,
            rung0: !p.no_rung0,
            leaf_budget: std::time::Duration::from_secs(p.leaf_budget),
            ec_transcript: match p.ec_transcript {
                EcTranscriptArg::Capped => EcTranscriptMode::Capped,
                EcTranscriptArg::Full => EcTranscriptMode::Full,
            },
            write_granularity: match p.write_granularity {
                WriteGranularityArg::Oracle => WriteGranularity::Oracle,
                WriteGranularityArg::Node => WriteGranularity::Node,
            },
            stop: Some(stop_on_ctrl_c(
                "easycrypt: interrupt — stopping the current EasyCrypt sentence, then writing the \
                 partial proof (Ctrl-C again to abort now)",
            )),
            force: p.force,
        };
        for (name, exported) in &exports {
            let theorem = project.get_theorem(name).unwrap();
            let theorem_out = out_base.join(name);
            let result = run_tactics_observed(
                theorem,
                project,
                exported,
                &theorem_out,
                &backend,
                &options,
                export_observer(p.progress),
                &phase_log.phases_of(name),
            )?;
            if result.equivalences.is_empty() {
                // every selected equivalence was skipped (their lines are on stderr)
                continue;
            }
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
        Ok(())
    }
}

/// `domino easycrypt debug` (story 19, 35): lockstep execution on the EasyCrypt listing. It
/// starts no EasyCrypt and reads no file of the tree, so it writes only `!debug!/`.
fn easycrypt_debug<P: project::Project>(
    d: &EcDebug,
    project: &P,
    out_base: &std::path::Path,
) -> Result<(), Error> {
    #[cfg(not(feature = "cvc5-lib"))]
    {
        let _ = (d, project, out_base);
        Err(EcDebugNeedCvc5Lib.into())
    }
    #[cfg(feature = "cvc5-lib")]
    {
        use sspverif::easycrypt::debug::{debug_theorem, EcDebugOptions};
        use sspverif::writers::easycrypt::progress::{LoggingExportObserver, NopExportObserver};

        let theorem_names = proof_job_theorem(project, &d.theorem)?;
        let mut observer = NopExportObserver;
        let mut logging = LoggingExportObserver::new(&mut observer);
        let exports = export_in_memory(project, &theorem_names, &mut logging)?;

        let backend =
            sspverif::util::smtsolver::cvc5lib::Cvc5LibBackend::new(true, d.debug_timeout);
        let options = EcDebugOptions {
            proofstep: d.proofstep,
            oracle: d.oracle.clone(),
            timeout_ms: d.debug_timeout,
        };
        let stop = stop_on_ctrl_c(
            "easycrypt: interrupt — finishing the current solver query, then writing partial \
             results (Ctrl-C again to abort now)",
        );
        let mut all_ok = true;
        for (name, exported) in &exports {
            let theorem = project.get_theorem(name).unwrap();
            let theorem_out = out_base.join(name);
            println!();
            let entries = debug_theorem(
                theorem,
                project,
                exported,
                &theorem_out,
                &backend,
                &options,
                Some(&stop),
                &mut |entry| println!("{}", entry.one_line()),
            )?;
            let table = sspverif::debug::sweep::failure_table(&entries);
            if !table.is_empty() {
                println!("\n{table}");
            }
            all_ok &= entries.iter().all(|entry| entry.ok);
        }
        if !all_ok {
            return Err(EcDebugNotVerified.into());
        }
        Ok(())
    }
}

/// `domino easycrypt check-alignment` (story 26, 35): a proof job, so the translation files it
/// runs EasyCrypt against are created if missing and otherwise not touched.
fn easycrypt_check_alignment<P: project::Project>(
    c: &EcCheckAlignment,
    project: &P,
    out_base: &std::path::Path,
) -> Result<(), Error> {
    use sspverif::writers::easycrypt::progress::{LoggingExportObserver, NopExportObserver};

    let theorem_names = proof_job_theorem(project, &c.theorem)?;
    let mut observer = NopExportObserver;
    let mut logging = LoggingExportObserver::new(&mut observer);
    let exports = export_in_memory(project, &theorem_names, &mut logging)?;

    let mut mismatches = 0;
    for (name, exported) in &exports {
        let theorem = project.get_theorem(name).unwrap();
        let theorem_out = out_base.join(name);
        std::fs::create_dir_all(&theorem_out)?;
        sspverif::easycrypt::job::ensure_translation_files(exported, &theorem_out)?;
        let options = sspverif::easycrypt::check::CheckOptions {
            proofstep: c.proofstep,
            oracle: c.oracle.clone(),
        };
        let alignment =
            sspverif::easycrypt::check::check_alignment(theorem, exported, &theorem_out, &options)?;
        let report = alignment.render();
        println!();
        print!("{report}");
        std::fs::write(theorem_out.join("alignment.txt"), &report)?;
        mismatches += alignment.mismatch_count();
    }
    if mismatches > 0 {
        return Err(AlignmentMismatch(mismatches).into());
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
