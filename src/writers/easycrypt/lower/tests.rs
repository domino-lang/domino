//! Story 08: the EasyCrypt listing and its IR.

use std::collections::{BTreeMap, HashSet};
use std::path::{Path, PathBuf};

use super::*;
use crate::debug::exec::{execute, Side, Terminal};
use crate::debug::ir::{count_terminals, inline_oracle, Place, Plumbing};
use crate::debug::render::render_side_by_side_easycrypt;
use crate::project::{DirectoryFiles, DirectoryProject, Project};
use crate::theorem::Theorem;
use crate::transforms::theorem_transforms::{DebugTransform, EasyCryptTransform, GameInstAux};
use crate::transforms::TheoremTransform;
use crate::types::Type;
use crate::writers::easycrypt::game::compute_game_files;
use crate::writers::easycrypt::interfaces::build_interfaces_file;
use crate::writers::easycrypt::package::compute_package_variants;
use crate::writers::easycrypt::render::render_file;
use crate::writers::easycrypt::typesfile::build_types_file;

const HELLO: &str = "example-projects/hello-world";
const KEM_DEM: &str = "example-projects/kem-dem/kem-dem-cca-ssp";

/// The raw (untransformed) theorem. Leaked, like `game.rs`'s tests, so the
/// borrowed `Theorem<'_>` can be returned.
fn raw_theorem(dir: &str, name: &str) -> &'static Theorem<'static> {
    let files: &'static DirectoryFiles =
        Box::leak(Box::new(DirectoryFiles::load(Path::new(dir)).unwrap()));
    let project: &'static DirectoryProject = Box::leak(Box::new(
        DirectoryProject::load(PathBuf::from(dir), files).unwrap(),
    ));
    project.get_theorem(name).unwrap()
}

fn ec_theorem(dir: &str, name: &str) -> (Theorem<'static>, Vec<(String, GameInstAux)>) {
    EasyCryptTransform
        .transform_theorem(raw_theorem(dir, name))
        .unwrap()
}

fn debug_theorem(dir: &str, name: &str) -> Theorem<'static> {
    DebugTransform
        .transform_theorem(raw_theorem(dir, name))
        .unwrap()
        .0
}

/// `(project, theorem, game instance, oracle)` for both sides of proofstep 0
/// of the two story-08 projects.
const CASES: &[(&str, &str, &str, &str)] = &[
    (HELLO, "Proof", "medium_composition", "UsefulOracle"),
    (HELLO, "Proof", "small_composition", "UsefulOracle"),
    (KEM_DEM, "kem_dem_cca_ssp", "Game_MON_CCA_PKE", "PKENC"),
    (
        KEM_DEM,
        "kem_dem_cca_ssp",
        "Game_MOD_CCA_PKE_Real_KEM",
        "PKENC",
    ),
];

fn lowered(dir: &str, theorem: &str, game_inst: &str, oracle: &str) -> InlinedOracle {
    let (th, _) = ec_theorem(dir, theorem);
    inline_oracle_ec(th.find_game_instance(game_inst).unwrap(), oracle).unwrap()
}

fn line(inl: &InlinedOracle, label: Label) -> &str {
    inl.listing.text.lines().nth(label - 1).unwrap()
}

/// Every statement, pre-order, with whether it sits in the entry frame.
fn walk<'a>(block: &'a InlBlock, entry: bool, out: &mut Vec<(&'a InlStmt, bool)>) {
    for stmt in &block.0 {
        out.push((stmt, entry));
        match stmt {
            InlStmt::Branch { then, els, .. } => {
                walk(then, entry, out);
                walk(els, entry, out);
            }
            InlStmt::Call { body, .. } => walk(body, false, out),
            _ => {}
        }
    }
}

fn stmts(inl: &InlinedOracle) -> Vec<(&InlStmt, bool)> {
    let mut out = Vec::new();
    walk(&inl.body, true, &mut out);
    out
}

fn label_of(stmt: &InlStmt) -> Label {
    match stmt {
        InlStmt::Assign { label, .. }
        | InlStmt::Sample { label, .. }
        | InlStmt::Unwrap { label, .. }
        | InlStmt::Branch { label, .. }
        | InlStmt::Call { label, .. }
        | InlStmt::Return { label, .. }
        | InlStmt::Abort { label } => *label,
    }
}

// --- golden files ------------------------------------------------------------

fn assert_golden(dir: &str, theorem: &str, oracle: &str, golden: &str) {
    // Regenerate with `domino inline --easycrypt --proof <T> --proofstep 0
    // --oracle <O> > testdata/easycrypt/story08/<golden>` (run in the
    // project directory): the command prints exactly this string.
    let out = render_side_by_side_easycrypt(raw_theorem(dir, theorem), 0, oracle, true).unwrap();
    let path = format!(
        "{}/testdata/easycrypt/story08/{golden}",
        env!("CARGO_MANIFEST_DIR")
    );
    let expected = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("failed to read golden file {path}: {e}"));
    assert_eq!(
        out, expected,
        "`domino inline --easycrypt` output != {path}"
    );
}

#[test]
fn golden_hello_world_useful_oracle() {
    assert_golden(HELLO, "Proof", "UsefulOracle", "inline-hello-world.txt");
}

#[test]
fn golden_kem_dem_pkenc() {
    assert_golden(
        KEM_DEM,
        "kem_dem_cca_ssp",
        "PKENC",
        "inline-kem-dem-pkenc.txt",
    );
}

#[test]
fn listing_is_deterministic() {
    for &(dir, th, gi, o) in CASES {
        assert_eq!(
            lowered(dir, th, gi, o).listing.text,
            lowered(dir, th, gi, o).listing.text
        );
    }
}

// --- labels, sites and line ranges ---------------------------------------------

#[test]
fn labels_are_distinct_lines_and_sites_are_1to1() {
    for &(dir, th, gi, o) in CASES {
        let inl = lowered(dir, th, gi, o);
        let n_lines = inl.listing.text.lines().count();
        let mut labels: Vec<Label> = stmts(&inl).iter().map(|(s, _)| label_of(s)).collect();
        let total = labels.len();
        labels.sort_unstable();
        labels.dedup();
        assert_eq!(labels.len(), total, "{gi}: labels are not distinct");
        assert!(
            labels.iter().all(|l| (1..=n_lines).contains(l)),
            "{gi}: label out of range"
        );
        let site_keys: Vec<Label> = inl.listing.sites.keys().copied().collect();
        assert_eq!(
            site_keys, labels,
            "{gi}: sites and labelled statements disagree"
        );
        for (label, site) in &inl.listing.sites {
            assert_eq!(site.line, line(&inl, *label).trim(), "{gi}: site {label}");
        }
    }
}

#[test]
fn block_and_frame_line_ranges_are_populated() {
    for &(dir, th, gi, o) in CASES {
        let inl = lowered(dir, th, gi, o);
        let mut calls = 0;
        for (stmt, _) in stmts(&inl) {
            match stmt {
                InlStmt::Branch {
                    label,
                    is_assert,
                    then_lines,
                    else_lines,
                    ..
                } => {
                    assert!(!is_assert, "EasyCrypt has no `assert`");
                    let (first, last) = then_lines.expect("every EasyCrypt `if` has a block");
                    assert_eq!(first, label + 1);
                    let close = line(&inl, last).trim();
                    match else_lines {
                        Some((efirst, elast)) => {
                            assert_eq!(close, "} else {");
                            assert_eq!(*efirst, last + 1);
                            assert_eq!(line(&inl, *elast).trim(), "}");
                        }
                        None => assert_eq!(close, "}"),
                    }
                }
                InlStmt::Call {
                    label,
                    frame,
                    frame_lines,
                    arg_lines,
                    ..
                } => {
                    calls += 1;
                    assert_eq!(frame_lines.0, *label, "the call line opens the frame");
                    assert!(line(&inl, *label).trim().starts_with("(* "));
                    // The frame closes on the callee's result binding.
                    assert!(line(&inl, frame_lines.1).contains(" <- ec_result"));
                    match arg_lines {
                        None => assert!(frame.arg_bindings.is_empty()),
                        Some((first, last)) => {
                            assert_eq!(*first, label + 1);
                            assert_eq!(last - first + 1, frame.arg_bindings.len());
                            assert!(*last < frame_lines.1);
                        }
                    }
                }
                _ => {}
            }
        }
        if gi != "small_composition" {
            assert!(calls > 0, "{gi} inlines at least one call");
        }
    }
}

// --- provenance (§3.2) ----------------------------------------------------------

fn state_places<'a>(place: &'a Place, out: &mut Vec<(&'a str, &'a str)>) {
    match place {
        Place::State {
            pkg_inst, field, ..
        } => out.push((pkg_inst, field)),
        Place::Index { base, .. } => state_places(base, out),
        Place::Tuple(ps) => ps.iter().for_each(|p| state_places(p, out)),
        Place::Local { .. } | Place::Discard => {}
    }
}

fn local_keys(place: &Place, out: &mut Vec<String>) {
    match place {
        Place::Local { key, .. } => out.push(key.clone()),
        Place::Index { base, .. } => local_keys(base, out),
        Place::Tuple(ps) => ps.iter().for_each(|p| local_keys(p, out)),
        Place::State { .. } | Place::Discard => {}
    }
}

/// Every place any statement of `inl` writes or binds.
fn places(inl: &InlinedOracle) -> Vec<Place> {
    let mut out = Vec::new();
    for (stmt, _) in stmts(inl) {
        match stmt {
            InlStmt::Assign { target, .. }
            | InlStmt::Sample { target, .. }
            | InlStmt::Unwrap { target, .. } => out.push(target.clone()),
            InlStmt::Call { bind, .. } => out.extend(bind.clone()),
            _ => {}
        }
    }
    out
}

fn entry_returns(inl: &InlinedOracle) -> Vec<Option<Expression>> {
    stmts(inl)
        .into_iter()
        .filter_map(|(s, entry)| match s {
            InlStmt::Return { value, .. } if entry => Some(value.clone()),
            _ => None,
        })
        .collect()
}

#[test]
fn kem_dem_pkenc_state_places_and_return_values_are_domino() {
    let domino = debug_theorem(KEM_DEM, "kem_dem_cca_ssp");
    for gi in ["Game_MON_CCA_PKE", "Game_MOD_CCA_PKE_Real_KEM"] {
        let inl = lowered(KEM_DEM, "kem_dem_cca_ssp", gi, "PKENC");
        let game = domino.find_game_instance(gi).unwrap().game();

        let written = places(&inl);
        let mut state = Vec::new();
        for place in &written {
            state_places(place, &mut state);
        }
        assert!(!state.is_empty(), "{gi}: PKENC writes package state");
        for (pkg_inst, field) in state {
            let inst = game
                .pkgs
                .iter()
                .find(|p| p.name == pkg_inst)
                .unwrap_or_else(|| panic!("{gi}: no Domino package instance `{pkg_inst}`"));
            assert!(
                inst.pkg.state.iter().any(|(name, _, _)| name == field),
                "{gi}: `{pkg_inst}` has no Domino state field `{field}`"
            );
        }

        // Every value the oracle returns is the Domino expression the Domino
        // listing returns — the same node, alpha-renamed the same way.
        let dom = inline_oracle(domino.find_game_instance(gi).unwrap(), "PKENC").unwrap();
        let ec_returns = entry_returns(&inl);
        assert!(!ec_returns.is_empty());
        assert_eq!(ec_returns, entry_returns(&dom), "{gi}");
        assert_eq!(inl.return_type, dom.return_type, "{gi}");
        assert_eq!(inl.args, dom.args, "{gi}");
        assert_eq!(inl.entry_pkg_inst, dom.entry_pkg_inst, "{gi}");
    }
}

#[test]
fn plumbing_variables_never_reach_the_ir() {
    for &(dir, th, gi, o) in CASES {
        let inl = lowered(dir, th, gi, o);
        let mut keys = Vec::new();
        for place in places(&inl) {
            local_keys(&place, &mut keys);
        }
        for key in &keys {
            assert!(
                !key.ends_with("::ec_result") && !key.ends_with("::ec_done"),
                "{gi}: `{key}` is exporter plumbing, not a place"
            );
        }
        for (label, site) in &inl.listing.sites {
            let written = site.kind == SiteKind::Assign || site.kind == SiteKind::Sample;
            assert!(
                !(written && (site.line.contains("abort_flag") || site.line.contains("ec_done"))),
                "{gi}: line {label} assigns a flag: {}",
                site.line
            );
        }
    }
}

// --- aborts -------------------------------------------------------------------

#[test]
fn falling_through_the_entry_procedure_aborts_at_the_router_flag() {
    for &(dir, th, gi, o) in CASES {
        let inl = lowered(dir, th, gi, o);
        let Some(InlStmt::Abort { label }) = inl.body.0.last() else {
            panic!("{gi}: the entry body must end in the router's abort");
        };
        assert!(
            line(&inl, *label).trim().ends_with(".abort_flag <- true;"),
            "{gi}"
        );
        assert_eq!(inl.listing.sites[label].kind, SiteKind::Abort);
        assert!(line(&inl, label - 1)
            .trim()
            .starts_with("if (ec_result = None)"));
    }
}

#[test]
fn every_ec_done_true_that_is_not_after_a_return_is_an_abort() {
    let inl = lowered(KEM_DEM, "kem_dem_cca_ssp", "Game_MON_CCA_PKE", "PKENC");
    let aborts: Vec<Label> = stmts(&inl)
        .into_iter()
        .filter(|(s, _)| matches!(s, InlStmt::Abort { .. }))
        .map(|(s, _)| label_of(s))
        .collect();
    for (i, text) in inl.listing.text.lines().enumerate() {
        let label = i + 1;
        if text.trim() == "ec_done <- true;" {
            let after_return = line(&inl, label - 1)
                .trim()
                .starts_with("ec_result <- Some");
            assert_eq!(aborts.contains(&label), !after_return, "line {label}");
        }
    }
}

// --- plumbing branches (story 22) ----------------------------------------------

/// Every guard row of the listing is a labelled `Branch` marked with the kind
/// of plumbing it is, and nothing else is marked. A done guard's condition is
/// the literal `true` and it has no else side.
#[test]
fn plumbing_branches_are_labelled_decision_points() {
    let (mut done_guards, mut call_results) = (0, 0);
    for &(dir, th, gi, o) in CASES {
        let inl = lowered(dir, th, gi, o);
        for (stmt, _) in stmts(&inl) {
            let InlStmt::Branch {
                label,
                cond,
                els,
                plumbing,
                ..
            } = stmt
            else {
                continue;
            };
            let text = line(&inl, *label).trim();
            if text == "if (!ec_done) {" {
                done_guards += 1;
                assert_eq!(*plumbing, Some(Plumbing::DoneGuard), "{gi}: line {label}");
                assert_eq!(*cond, Expression::boolean(true), "{gi}: line {label}");
                assert!(els.0.is_empty(), "{gi}: line {label}");
            } else if text.starts_with("if (!(ec_r") && !text.starts_with("if (!(ec_result") {
                call_results += 1;
                assert_eq!(*plumbing, Some(Plumbing::CallResult), "{gi}: line {label}");
            } else {
                assert_eq!(*plumbing, None, "{gi}: line {label}: {text}");
            }
        }
        // no `if (!ec_done)` row is left without a Branch
        let labelled: HashSet<Label> = stmts(&inl).iter().map(|(s, _)| label_of(s)).collect();
        for (i, text) in inl.listing.text.lines().enumerate() {
            if text.trim() == "if (!ec_done) {" {
                assert!(
                    labelled.contains(&(i + 1)),
                    "{gi}: line {} unlabelled",
                    i + 1
                );
            }
        }
    }
    assert!(done_guards > 0, "no done guard exercised");
    assert!(call_results > 0, "no call-result guard exercised");
}

// --- the executor runs it -----------------------------------------------------

#[test]
fn executor_walks_every_structural_path() {
    for &(dir, th, gi, o) in CASES {
        let (theorem, auxs) = ec_theorem(dir, th);
        let game_inst = theorem.find_game_instance(gi).unwrap();
        let inl = inline_oracle_ec(game_inst, o).unwrap();
        let si = &auxs.iter().find(|(n, _)| n == gi).unwrap().1.sample_info;
        let paths = execute(&inl, game_inst, si, Side::Left, None).unwrap();
        assert_eq!(paths.len() as u64, count_terminals(&inl), "{gi}");
        assert!(paths
            .iter()
            .any(|p| matches!(p.terminal, Terminal::Return { .. })));
        // Falling through to the router is an abort wherever a path can get
        // there without having returned or aborted first: where the entry
        // procedure has a guard with no else side, or a pruned
        // `ec_done <- true` (story 18: a write no done guard can read is
        // deleted, so that path now aborts at the router instead of at the
        // write). `small_composition` never aborts. `Game_MON_CCA_PKE` still
        // has a live flag, but its outer guards' `else { ec_done <- true }`
        // arms are dead and were pruned, so it reaches the router abort too.
        let router_abort = label_of(inl.body.0.last().unwrap());
        let reaches_router_abort = paths
            .iter()
            .any(|p| matches!(p.terminal, Terminal::Abort { label } if label == router_abort));
        let expected = matches!(
            gi,
            "medium_composition" | "Game_MON_CCA_PKE" | "Game_MOD_CCA_PKE_Real_KEM"
        );
        assert_eq!(reaches_router_abort, expected, "{gi}");
        if dir == KEM_DEM {
            assert!(paths.iter().any(|p| p.terminal.is_abort()), "{gi}");
        }
    }
}

/// Structural path counts (`count_terminals`): the EasyCrypt listing against
/// the Domino listing of the same oracle. Recorded in the story 08 report.
#[test]
fn kem_dem_pkenc_path_counts() {
    let domino = debug_theorem(KEM_DEM, "kem_dem_cca_ssp");
    let mut counts = BTreeMap::new();
    for gi in ["Game_MON_CCA_PKE", "Game_MOD_CCA_PKE_Real_KEM"] {
        let ec = count_terminals(&lowered(KEM_DEM, "kem_dem_cca_ssp", gi, "PKENC"));
        let dom = count_terminals(
            &inline_oracle(domino.find_game_instance(gi).unwrap(), "PKENC").unwrap(),
        );
        counts.insert(gi, (ec, dom));
    }
    // The surplus is one child per inlined call that can return: the
    // caller's `if (!(ec_rN = None))` guard has an else side (an explicit
    // `ec_done <- true`, or falling through to the router's abort) that is
    // only reachable if the callee returned `None` without aborting — which
    // the inlined callee body rules out. Structurally present, infeasible.
    // Story 18 part B removed the `pk = None` guard that repeated the user's
    // own `assert`, so each inlined copy has one fewer infeasible branch
    // (12 and 31 before). Part A alone leaves these counts as they were. The
    // Domino counts, and every feasible path, are unchanged.
    //
    // Story 22 keeps each `if (!ec_done)` guard as a labelled branch whose
    // condition is the literal `true`, so each contributes an infeasible else
    // child: 10 -> 12 and 28 -> 32.
    assert_eq!(counts["Game_MON_CCA_PKE"], (12, 6));
    assert_eq!(counts["Game_MOD_CCA_PKE_Real_KEM"], (32, 16));
}

// --- the listing is real EasyCrypt ----------------------------------------------

/// Writes `Types.ec`, `Interfaces.ec`, every `Pkg_*.ec` and `Comp_*.ec` of
/// `theorem` (already through `EasyCryptTransform`) into `dir` — everything
/// but the invariant and proof files, which hello-world cannot export.
fn write_modules(theorem: &Theorem<'_>, auxs: &[(String, GameInstAux)], dir: &Path) {
    let types: HashSet<Type> = auxs
        .iter()
        .flat_map(|(_, aux)| aux.types.iter().cloned())
        .collect();
    let mut files = vec![
        (
            "Types.ec".to_string(),
            render_file(&build_types_file(theorem, &types).unwrap()),
        ),
        (
            "Interfaces.ec".to_string(),
            render_file(&build_interfaces_file(theorem).unwrap().file),
        ),
    ];
    for v in compute_package_variants(theorem).unwrap() {
        files.push((format!("Pkg_{}.ec", v.name), render_file(&v.file)));
    }
    for g in compute_game_files(theorem).unwrap() {
        files.push((format!("Comp_{}.ec", g.name), render_file(&g.file)));
    }
    std::fs::create_dir_all(dir).unwrap();
    for (name, text) in files {
        std::fs::write(dir.join(name), text).unwrap();
    }
}

#[test]
fn listing_compiles_as_an_easycrypt_procedure() {
    for (dir, th) in [(HELLO, "Proof"), (KEM_DEM, "kem_dem_cca_ssp")] {
        let (theorem, auxs) = ec_theorem(dir, th);
        let out =
            std::env::temp_dir().join(format!("domino-story08-{}-{}", th, std::process::id()));
        write_modules(&theorem, &auxs, &out);
        for &(cdir, _, gi, o) in CASES {
            if cdir != dir {
                continue;
            }
            let game_inst = theorem.find_game_instance(gi).unwrap();
            let inl = inline_oracle_ec(game_inst, o).unwrap();
            let comp = Names::new()
                .mangle(NameKind::Module, &game_inst.game().name)
                .unwrap();
            let file = out.join(format!("Inlined_{comp}.ec"));
            std::fs::write(
                &file,
                format!(
                    "require import AllCore Distr FMap Int IntDiv Types.\n\
                     require import Comp_{comp}.\n\n\
                     module Inlined = {{\n{}}}.\n",
                    inl.listing.text
                ),
            )
            .unwrap();
            crate::writers::easycrypt::test_support::assert_compiles(
                out.to_str().unwrap(),
                file.to_str().unwrap(),
            );
        }
        let _ = std::fs::remove_dir_all(&out);
    }
}

/// Story 16 §8 warned that on easycryptified code the executor can read a
/// local on an infeasible path before any assignment — the body of an
/// `if (!ec_done)` after a failed guard — and then emits the raw frame key
/// (`<pkg#N::x>`), which is not legal SMT-LIB. In this IR every point that
/// sets `ec_done` is already a terminal, so a guard's body is only ever
/// reached on paths that assigned everything it reads: no path mentions an
/// unbound frame-local.
///
/// It also runs the IR against the **Domino** game instance
/// (`DebugTransform`), which is what the claims are built from: the state
/// places, sample positions and entry-frame return values are the Domino
/// ones (§3.2), so it pairs with it directly.
#[test]
fn no_path_reads_an_unbound_local_and_the_domino_game_instance_pairs_with_it() {
    for &(dir, th, gi, o) in CASES {
        let (ec, _) = ec_theorem(dir, th);
        let inl = inline_oracle_ec(ec.find_game_instance(gi).unwrap(), o).unwrap();
        let (dbg, auxs) = DebugTransform
            .transform_theorem(raw_theorem(dir, th))
            .unwrap();
        let game_inst = dbg.find_game_instance(gi).unwrap();
        let si = &auxs.iter().find(|(n, _)| n == gi).unwrap().1.sample_info;
        let paths = execute(&inl, game_inst, si, Side::Left, None).unwrap();
        assert_eq!(paths.len() as u64, count_terminals(&inl), "{gi}");
        for path in &paths {
            let smt = path
                .decls
                .iter()
                .chain(&path.constraints)
                .chain(std::iter::once(&path.return_constraint))
                .map(|e| e.to_string())
                .collect::<Vec<_>>()
                .join("\n");
            assert!(
                !smt.contains("::"),
                "{gi}: a path reads an unbound local:\n{smt}"
            );
        }
    }
}
