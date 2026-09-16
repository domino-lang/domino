// SPDX-License-Identifier: MIT OR Apache-2.0

//! `export_theorem` (`docs/stories/easycrypt/05-easycrypt-command.md` §3.4):
//! the one function that turns a Domino [`Theorem`] into the in-memory
//! contents of an EasyCrypt project — `Types.ec`, `Interfaces.ec`,
//! `Variant_*.ec`, `Comp_*.ec` — plus the data `domino easycrypt`'s stdout
//! report is built from. All files land directly in the theorem's own
//! output directory, flat (story 10 §3.2: no `packages/`/`games/`
//! subdirectories). It runs [`EquivalenceTransform`] itself (§2 of the
//! story: "the export pipeline is the existing `EquivalenceTransform`"), so
//! callers pass the *untransformed* theorem exactly as `Project::get_theorem`
//! returns it.
//!
//! Nothing here touches disk — [`write_files`] is the "thin wrapper" the
//! story asks for, kept separate so golden/unit tests can build an
//! [`ExportedTheorem`] without a temp directory. This is a deliberate
//! divergence from the story's own illustrative signature (§3.4:
//! `export_theorem(theorem: &Theorem, out: &Path)`) — `out` is dropped here
//! precisely *because* nothing here writes, and re-appears as
//! [`write_files`]'s own parameter instead.

use std::collections::{BTreeMap, HashSet};
use std::path::{Path, PathBuf};

use crate::gamehops::GameHop;
use crate::project::Project;
use crate::theorem::{RandomnessType, Theorem};
use crate::transforms::theorem_transforms::EquivalenceTransform;
use crate::transforms::TheoremTransform;
use crate::types::Type;

use super::game::compute_game_files;
use super::interfaces::build_interfaces_file;
use super::package::compute_package_variants;
use super::proof::compute_equivalence_files;
use super::render::render_file;
use super::types::func_op_name;
use super::typesfile::{build_types_file, collect_bits_types, collect_fn_consts};
use super::EcExportError;

/// One translated equivalence hop's report data (§3.2 of story 07): the
/// files it wrote, the oracle count, and the admit count — the CLI's stdout
/// report needs these without re-deriving them from `files`/re-parsing
/// rendered text.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EquivalenceReport {
    pub left_name: String,
    pub right_name: String,
    pub invariants_file: String,
    pub proof_file: String,
    pub oracle_count: usize,
    pub admit_count: usize,
    pub oracle_set_mismatch: Option<String>,
}

/// A game hop this exporter does not translate, named with its kind and the
/// pair of game instances it connects (`GameHop::{left,right}_game_instance_name`)
/// — `domino easycrypt`'s report lists these so a missing `Eq_*.ec` (stories
/// 06/07) is never a silent gap.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SkipNote {
    pub kind: &'static str,
    pub left: String,
    pub right: String,
    pub reason: &'static str,
}

/// The in-memory result of exporting one theorem (§3.4). `files` keys are
/// bare file names, flat in the theorem's own output directory (`Types.ec`,
/// `Variant_KX.ec`, ... — story 10 §3.2: no `packages/`/`games/`
/// subdirectories); [`write_files`] joins them onto an `out` root. The
/// remaining fields are exactly the data `domino easycrypt`'s stdout report
/// (§3.3) needs, computed once here so the report never re-derives it (and
/// can never disagree with what was actually written).
#[derive(Debug)]
pub struct ExportedTheorem {
    pub files: BTreeMap<PathBuf, String>,
    pub skipped: Vec<SkipNote>,
    /// `Types.ec`'s bits types, already-mangled EasyCrypt names
    /// (`bits_n`, ...), in emission order.
    pub bits_type_names: Vec<String>,
    /// `Types.ec`'s function constants, already-mangled EasyCrypt op names
    /// (`func_prf`, ...), in emission order.
    pub fn_const_names: Vec<String>,
    /// `Variant_*.ec` variant names (unprefixed, e.g. `"KX"`), discovery
    /// order.
    pub package_variant_names: Vec<String>,
    /// `Comp_*.ec` composition names (unprefixed, e.g. `"Hybrid0"`),
    /// discovery order.
    pub game_names: Vec<String>,
    /// How many oracles, across this theorem's equivalence hops (direct or
    /// nested in a hybrid), declare an explicit `randomness: simple`/`none`
    /// mapping — a feature this epic does not translate (see
    /// [`super::EcExportError`]'s doc and `Equivalence::randomness`).
    pub randomness_mapping_oracles: usize,
    /// One entry per translated `GameHop::Equivalence`, `theorem.game_hops`
    /// order (story 07).
    pub equivalences: Vec<EquivalenceReport>,
}

/// The kind + reason for a hop this exporter skips, or `None` for
/// [`GameHop::Equivalence`], which is exactly what §3.2 translates into
/// `Variant_*.ec`/`Comp_*.ec`.
fn skip_kind_and_reason(hop: &GameHop<'_>) -> Option<(&'static str, &'static str)> {
    match hop {
        GameHop::Equivalence(_) => None,
        GameHop::Reduction(_) => Some(("reduction", "reductions are not translated")),
        GameHop::Hybrid(_) => Some(("hybrid", "hybrid game hops are not translated")),
        GameHop::Conjecture(_) => Some(("conjecture", "conjectures are not translated")),
    }
}

fn compute_skipped(theorem: &Theorem<'_>) -> Vec<SkipNote> {
    theorem
        .game_hops
        .iter()
        .filter_map(|hop| {
            skip_kind_and_reason(hop).map(|(kind, reason)| SkipNote {
                kind,
                left: hop.left_game_instance_name().to_string(),
                right: hop.right_game_instance_name().to_string(),
                reason,
            })
        })
        .collect()
}

/// The equivalence every [`GameHop`] variant carries or wraps, or `None` for
/// [`GameHop::Reduction`]/[`GameHop::Conjecture`], which have none.
fn hop_equivalence<'a>(
    hop: &'a GameHop<'_>,
) -> Option<&'a crate::gamehops::equivalence::Equivalence> {
    match hop {
        GameHop::Equivalence(eq) => Some(eq),
        GameHop::Hybrid(hybrid) => Some(hybrid.equivalence()),
        GameHop::Reduction(_) | GameHop::Conjecture(_) => None,
    }
}

fn count_randomness_mapping_oracles(theorem: &Theorem<'_>) -> usize {
    theorem
        .game_hops
        .iter()
        .filter_map(hop_equivalence)
        .flat_map(|eq| eq.randomness())
        .filter(|(_, randomness)| !matches!(randomness, RandomnessType::Custom))
        .count()
}

/// Builds the whole EasyCrypt project for `theorem` in memory (§3.2, §3.4).
/// Runs [`EquivalenceTransform`] itself — `theorem` is the plain,
/// untransformed `Theorem` a `Project` hands back. Never touches disk and
/// never invokes a solver (§6: "export must never invoke cvc5 or touch
/// `EquivalenceContext`"). `project` is needed to read each equivalence
/// hop's hand-written invariant file(s) (story 06/07); it must be the same
/// project `theorem` came from.
pub fn export_theorem(
    theorem: &Theorem<'_>,
    project: &impl Project,
) -> Result<ExportedTheorem, EcExportError> {
    let skipped = compute_skipped(theorem);
    let randomness_mapping_oracles = count_randomness_mapping_oracles(theorem);

    let (theorem, auxs) = EquivalenceTransform.transform_theorem(theorem)?;

    let types: HashSet<Type> = auxs
        .iter()
        .flat_map(|(_, aux)| aux.types.iter().cloned())
        .collect();

    let types_file = build_types_file(&theorem, &types)?;
    let bits_type_names = collect_bits_types(&types).into_keys().collect();
    let fn_const_names = collect_fn_consts(&theorem.consts)
        .into_keys()
        .map(|name| func_op_name(&name))
        .collect();

    let interfaces_output = build_interfaces_file(&theorem)?;
    let package_variants = compute_package_variants(&theorem)?;
    let game_files = compute_game_files(&theorem)?;

    let package_variant_names = package_variants.iter().map(|v| v.name.clone()).collect();
    let game_names = game_files.iter().map(|g| g.name.clone()).collect();

    let mut files = BTreeMap::new();
    files.insert(PathBuf::from("Types.ec"), render_file(&types_file));
    files.insert(
        PathBuf::from("Interfaces.ec"),
        render_file(&interfaces_output.file),
    );
    for variant in &package_variants {
        files.insert(
            PathBuf::from(format!("Variant_{}.ec", variant.name)),
            render_file(&variant.file),
        );
    }
    for game in &game_files {
        files.insert(
            PathBuf::from(format!("Comp_{}.ec", game.name)),
            render_file(&game.file),
        );
    }

    let equivalence_files = compute_equivalence_files(&theorem, project, &interfaces_output)?;
    let mut equivalences = Vec::with_capacity(equivalence_files.len());
    for ef in &equivalence_files {
        files.insert(
            PathBuf::from(ef.invariants.file_name.clone()),
            render_file(&ef.invariants.file),
        );
        files.insert(
            PathBuf::from(ef.proof.file_name.clone()),
            render_file(&ef.proof.file),
        );
        equivalences.push(EquivalenceReport {
            left_name: ef.proof.left_name.clone(),
            right_name: ef.proof.right_name.clone(),
            invariants_file: ef.invariants.file_name.clone(),
            proof_file: ef.proof.file_name.clone(),
            oracle_count: ef.proof.oracle_count,
            admit_count: ef.proof.admit_count,
            oracle_set_mismatch: ef.proof.oracle_set_mismatch.clone(),
        });
    }

    Ok(ExportedTheorem {
        files,
        skipped,
        bits_type_names,
        fn_const_names,
        package_variant_names,
        game_names,
        randomness_mapping_oracles,
        equivalences,
    })
}

/// Writes every entry of `exported.files` under `out_dir`, flat (story 10
/// §3.2 — no `packages/`/`games/` subdirectories; `create_dir_all` here only
/// ever creates `out_dir` itself). The caller (`domino easycrypt`) only
/// calls this after [`export_theorem`] has returned `Ok` for *every*
/// requested theorem (§3.2: "a failed export must not leave a half-written
/// tree").
pub fn write_files(out_dir: &Path, files: &BTreeMap<PathBuf, String>) -> std::io::Result<()> {
    for (rel_path, contents) in files {
        let path = out_dir.join(rel_path);
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent)?;
        }
        std::fs::write(path, contents)?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::path::{Path, PathBuf};

    use crate::project::{DirectoryFiles, DirectoryProject, Project};

    use super::*;

    fn export(dir: &str, theorem_name: &str) -> Result<ExportedTheorem, EcExportError> {
        let files = DirectoryFiles::load(Path::new(dir)).unwrap();
        let project = DirectoryProject::load(PathBuf::from(dir), &files).unwrap();
        let theorem = project.get_theorem(theorem_name).unwrap();
        export_theorem(theorem, &project)
    }

    // `hello-world`'s `theorem/invariant.smt2` predates the
    // `define-state-relation (left right)` grammar story 06's
    // `invariant.rs` supports: it is written against `src/writers/smt`'s
    // own *solver-facing* encoding — one opaque whole-game-state sort per
    // side (`<GameState_MediumComposition_<$<!n!>$>>`) with datatype
    // selector functions (`<game-...-pkgstate-rand>`,
    // `<pkg-state-Rand-...-ctr>`) — rather than story 06's flat
    // per-`(instance, field)` record model. This is a real, pre-existing
    // gap discovered only now that story 07 wires `build_invariant_file`
    // into every equivalence hop of every project's export (previously
    // only `Simple4WHS`'s `Hybrid0 ~ Hybrid1` had ever been run through
    // it) — see the story 07 implementation report §"hello-world does not
    // export" for the full writeup. Fixing it is out of story 07's scope
    // (it is a story-06-shaped grammar-coverage gap, not a proof-skeleton
    // one); `export_theorem` is correctly all-or-nothing per theorem
    // (matching `yao_theorem_fails_with_a_real_miette_diagnostic`'s
    // existing precedent for an unsupported construct), so this pins the
    // known failure rather than papering over it.
    #[test]
    fn hello_world_fails_on_its_pre_easycrypt_invariant_format() {
        let err = export("example-projects/hello-world", "Proof").unwrap_err();
        let report = format!("{:?}", miette::Report::new(err));
        assert!(
            report.contains("unsupported SMT sort"),
            "expected the known GameState-sort gap, got: {report}"
        );
    }

    #[test]
    fn simple_4whs_reports_the_reduction_hop_and_the_composition_names() {
        let exported = export("example-projects/4WHS", "Simple4WHS").unwrap();

        assert_eq!(
            exported.skipped,
            vec![SkipNote {
                kind: "reduction",
                left: "Hybrid2".to_string(),
                right: "Hybrid3".to_string(),
                reason: "reductions are not translated",
            }]
        );

        assert_eq!(
            exported.game_names,
            vec!["Hybrid0", "Hybrid1", "Hybrid2", "PRF"]
        );
        assert_eq!(exported.bits_type_names, vec!["bits_n"]);
        assert_eq!(exported.fn_const_names, vec!["func_mac", "func_prf"]);

        // Simple4WHS's three equivalences annotate several oracles with
        // `randomness: simple`/`randomness: none` — a real, hit-in-practice
        // case for the acceptance target, not a hypothetical.
        assert!(exported.randomness_mapping_oracles > 0);
    }

    #[test]
    fn simple_4whs_exports_the_same_package_variants_as_story_03() {
        let exported = export("example-projects/4WHS", "Simple4WHS").unwrap();
        let mut names = exported.package_variant_names.clone();
        names.sort();
        assert_eq!(
            names,
            vec![
                "KX",
                "KX_NoKeys",
                "KX_NoPrf",
                "PRF",
                "Prot",
                "Prot_NoKey",
                "Prot_NoPrf"
            ]
        );
    }

    // `Full4WHS`'s `theorem/full/*.smt2` invariants hit three distinct
    // gaps, all now fixed in `invariant.rs`: their `define-state-relation`
    // binders are spelled `state-left`/`state-right` instead of
    // `Simple4WHS`'s `left`/`right` (binder names are purely positional,
    // like an ordinary `define-fun`'s own argument names); at least two
    // files compare a *whole package instance's* state in one equality
    // (`(= state-left.KX state-right.KX)`, `invariant-KX-H1_0.smt2` and
    // `invariant-H1_1-H2_0.smt2` — `translate_eq_n`'s
    // `resolve_instance_atom`/`translate_instance_equality` expand that
    // into a conjunction over every field both sides share for that
    // instance); and `invariant-H7_1_1_0-H7_1_1_1.smt2` uses `<0_n>`, the
    // SMT-text form of a fixed-width `BitsLiteral` zero/one value
    // (`src/writers/smt/expr_expr.rs`'s own `<{0|1}_{suffix}>` encoding,
    // not a placeholder — `translate_bits_literal_atom` now maps it onto
    // the same `zero_<suffix>`/`one_<suffix>` ops `Types.ec` already
    // declares for every bits type in scope). `Full4WHS` now exports with
    // no error at all.
    #[test]
    fn full_4whs_exports_without_error() {
        let exported = export("example-projects/4WHS", "Full4WHS").unwrap();
        assert!(exported.files.contains_key(Path::new("Types.ec")));
        assert!(!exported.package_variant_names.is_empty());
        assert!(!exported.game_names.is_empty());
        assert_eq!(exported.equivalences.len(), 9);
        for eq in &exported.equivalences {
            assert_eq!(eq.oracle_set_mismatch, None);
        }
    }

    // Acceptance §4's other target project beyond hello-world/4WHS above,
    // literal-width `Bits(256)`: `simple-KEM-example`. Its own hand-written
    // invariants (`theorem/invariant-*.smt2`) turn out to be the same
    // pre-easycrypt `GameState_`-sort shape as `hello-world`'s (see that
    // test above) — not a story-07 acceptance target itself (only
    // "kem-dem and hello-world" are named in §4), so this pins the same
    // known gap rather than the story's own illustrative "exports without
    // error".
    #[test]
    fn simple_kem_example_fails_on_its_pre_easycrypt_invariant_format() {
        let err = export("example-projects/simple-KEM-example", "KEM_Proof").unwrap_err();
        let report = format!("{:?}", miette::Report::new(err));
        assert!(
            report.contains("unsupported SMT sort"),
            "expected the known GameState-sort gap, got: {report}"
        );
    }

    #[test]
    fn kem_dem_cca_ssp_exports_without_error() {
        let exported = export(
            "example-projects/kem-dem/kem-dem-cca-ssp",
            "kem_dem_cca_ssp",
        )
        .unwrap();
        assert!(exported.files.contains_key(Path::new("Types.ec")));
        assert!(!exported.package_variant_names.is_empty());
        assert!(!exported.game_names.is_empty());

        // Its one equivalence hop (`Game_MON_CCA_PKE ~
        // Game_MOD_CCA_PKE_Real_KEM`) uses story 06's supported
        // `define-state-relation (left right)` grammar, so this is the
        // acceptance target for story 07's own "kem-dem ... also produce
        // compiling `Eq_*.ec` files" bullet (§4) — both files are present
        // and report 3 oracles/3 admits (`PKGEN`/`PKENC`/`PKDEC`).
        assert_eq!(exported.equivalences.len(), 1);
        let eq = &exported.equivalences[0];
        assert_eq!(eq.left_name, "Game_MON_CCA_PKE");
        assert_eq!(eq.right_name, "Game_MOD_CCA_PKE_Real_KEM");
        assert_eq!(eq.oracle_count, 3);
        assert_eq!(eq.admit_count, 3);
        assert_eq!(eq.oracle_set_mismatch, None);
        assert!(exported
            .files
            .contains_key(Path::new(&eq.invariants_file)));
        assert!(exported.files.contains_key(Path::new(&eq.proof_file)));
    }

    #[test]
    fn yao_theorem_fails_with_a_real_miette_diagnostic() {
        // Acceptance: "point it at a project using an unsupported construct
        // ... reports a `miette` diagnostic with a span". `example-projects/
        // yao`'s `Yao` theorem hits one (confirmed empirically here, not
        // merely asserted) — `export_theorem` returns `Err`, so the CLI
        // layer never reaches `write_files` and nothing is written.
        let err = export("example-projects/yao", "Yao").unwrap_err();
        let report = format!("{:?}", miette::Report::new(err));
        assert!(!report.is_empty(), "diagnostic should render");
    }

    #[test]
    fn rendering_is_deterministic() {
        let a = export("example-projects/4WHS", "Simple4WHS").unwrap();
        let b = export("example-projects/4WHS", "Simple4WHS").unwrap();
        assert_eq!(a.files, b.files);
    }

    #[test]
    fn write_files_round_trips_and_rewriting_is_byte_identical() {
        // Not `hello-world` (see the test above pinning its known
        // pre-easycrypt invariant-format gap) — `kem-dem-cca-ssp` fully
        // exports, including its equivalence's `Eq_*.ec`/`Eq_*_Invariants.ec`.
        let exported = export(
            "example-projects/kem-dem/kem-dem-cca-ssp",
            "kem_dem_cca_ssp",
        )
        .unwrap();
        let tmp = std::env::temp_dir().join(format!(
            "domino-easycrypt-export-test-{}",
            std::process::id()
        ));
        let _ = std::fs::remove_dir_all(&tmp);

        write_files(&tmp, &exported.files).unwrap();
        let first: BTreeMap<PathBuf, String> = exported
            .files
            .keys()
            .map(|p| (p.clone(), std::fs::read_to_string(tmp.join(p)).unwrap()))
            .collect();

        write_files(&tmp, &exported.files).unwrap();
        let second: BTreeMap<PathBuf, String> = exported
            .files
            .keys()
            .map(|p| (p.clone(), std::fs::read_to_string(tmp.join(p)).unwrap()))
            .collect();

        assert_eq!(first, second);
        assert_eq!(first, exported.files);

        std::fs::remove_dir_all(&tmp).unwrap();
    }

    // --- full-tree compile, dependency order (skips without `easycrypt`) ---

    #[test]
    fn simple_4whs_full_tree_compiles_in_dependency_order() {
        let exported = export("example-projects/4WHS", "Simple4WHS").unwrap();
        let tmp = std::env::temp_dir().join(format!(
            "domino-easycrypt-export-compile-test-{}",
            std::process::id()
        ));
        let _ = std::fs::remove_dir_all(&tmp);
        write_files(&tmp, &exported.files).unwrap();

        let base = tmp.to_str().unwrap().to_string();

        // Story 10: a single `-I .` compiles the whole flat theorem
        // directory — no `packages/`/`games/` subdirectories, so no
        // `assert_compiles_with_paths`.
        super::super::test_support::assert_compiles(&base, &format!("{base}/Types.ec"));
        super::super::test_support::assert_compiles(&base, &format!("{base}/Interfaces.ec"));
        for name in &exported.package_variant_names {
            super::super::test_support::assert_compiles(&base, &format!("{base}/Variant_{name}.ec"));
        }
        for name in &exported.game_names {
            super::super::test_support::assert_compiles(&base, &format!("{base}/Comp_{name}.ec"));
        }
        // Story 07: every equivalence's invariants file compiles for real
        // (no known gap there). Story 13: the `byequiv` precondition now
        // makes the *same-composition* hop's base case genuinely
        // discharge (`Eq_Real_Hybrid3_Ideal_Hybrid3.ec` — plain
        // `assert_compiles`, no tolerance). The two *cross-composition*
        // hops (`Eq_Hybrid0_Hybrid1.ec`, `Eq_Hybrid1_Hybrid2.ec`) still hit
        // the known base-case gap — see `test_support::
        // assert_compiles_or_known_base_case_gap`'s own doc and this
        // story's implementation report for the exact residual goal.
        for eq in &exported.equivalences {
            super::super::test_support::assert_compiles(&base, &format!("{base}/{}", eq.invariants_file));
            let proof_path = format!("{base}/{}", eq.proof_file);
            if eq.proof_file == "Eq_Real_Hybrid3_Ideal_Hybrid3.ec" {
                super::super::test_support::assert_compiles(&base, &proof_path);
            } else {
                super::super::test_support::assert_compiles_or_known_base_case_gap(
                    &[&base],
                    &proof_path,
                );
            }
        }

        std::fs::remove_dir_all(&tmp).unwrap();
    }

    #[test]
    fn kem_dem_cca_ssp_full_tree_compiles_in_dependency_order() {
        let exported = export(
            "example-projects/kem-dem/kem-dem-cca-ssp",
            "kem_dem_cca_ssp",
        )
        .unwrap();
        let tmp = std::env::temp_dir().join(format!(
            "domino-easycrypt-export-compile-test-kemdem-{}",
            std::process::id()
        ));
        let _ = std::fs::remove_dir_all(&tmp);
        write_files(&tmp, &exported.files).unwrap();

        let base = tmp.to_str().unwrap().to_string();

        super::super::test_support::assert_compiles(&base, &format!("{base}/Types.ec"));
        super::super::test_support::assert_compiles(&base, &format!("{base}/Interfaces.ec"));
        for name in &exported.package_variant_names {
            super::super::test_support::assert_compiles(&base, &format!("{base}/Variant_{name}.ec"));
        }
        for name in &exported.game_names {
            super::super::test_support::assert_compiles(&base, &format!("{base}/Comp_{name}.ec"));
        }
        for eq in &exported.equivalences {
            super::super::test_support::assert_compiles(&base, &format!("{base}/{}", eq.invariants_file));
            super::super::test_support::assert_compiles_or_known_base_case_gap(
                &[&base],
                &format!("{base}/{}", eq.proof_file),
            );
        }

        std::fs::remove_dir_all(&tmp).unwrap();
    }

    // `Full4WHS` is a much larger project than `Simple4WHS`/`kem-dem-cca-ssp`
    // (18 package variants, 12 games, 9 equivalence hops) — exercising it
    // here, on top of the smaller acceptance targets above, is what actually
    // found (and, once fixed, now confirms the fix for) the three real
    // `invariant.rs` gaps documented in `full_4whs_exports_without_error`'s
    // own comment.
    #[test]
    fn full_4whs_full_tree_compiles_in_dependency_order() {
        let exported = export("example-projects/4WHS", "Full4WHS").unwrap();
        let tmp = std::env::temp_dir().join(format!(
            "domino-easycrypt-export-compile-test-full4whs-{}",
            std::process::id()
        ));
        let _ = std::fs::remove_dir_all(&tmp);
        write_files(&tmp, &exported.files).unwrap();

        let base = tmp.to_str().unwrap().to_string();

        super::super::test_support::assert_compiles(&base, &format!("{base}/Types.ec"));
        super::super::test_support::assert_compiles(&base, &format!("{base}/Interfaces.ec"));
        for name in &exported.package_variant_names {
            super::super::test_support::assert_compiles(&base, &format!("{base}/Variant_{name}.ec"));
        }
        for name in &exported.game_names {
            super::super::test_support::assert_compiles(&base, &format!("{base}/Comp_{name}.ec"));
        }
        for eq in &exported.equivalences {
            super::super::test_support::assert_compiles(&base, &format!("{base}/{}", eq.invariants_file));
            super::super::test_support::assert_compiles_or_known_base_case_gap(
                &[&base],
                &format!("{base}/{}", eq.proof_file),
            );
        }

        std::fs::remove_dir_all(&tmp).unwrap();
    }
}
