// SPDX-License-Identifier: MIT OR Apache-2.0

//! `export_theorem` (`docs/stories/easycrypt/05-easycrypt-command.md` §3.4):
//! the one function that turns a Domino [`Theorem`] into the in-memory
//! contents of an EasyCrypt project — `Types.ec`, `Interfaces.ec`,
//! `Pkg_*.ec` (story 14 §3.6 renamed this from `Variant_*.ec`), `Comp_*.ec`
//! — plus the data `domino easycrypt`'s stdout
//! report is built from. All files land directly in the theorem's own
//! output directory, flat (story 10 §3.2: no `packages/`/`games/`
//! subdirectories). It runs [`EasyCryptTransform`] itself (story 16 §3.6
//! replaced story 05's `EquivalenceTransform`: the same pipeline with
//! `easycryptify` in place of `treeify`), so callers pass the *untransformed*
//! theorem exactly as `Project::get_theorem` returns it.
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
use crate::transforms::theorem_transforms::EasyCryptTransform;
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
    /// Index of the hop in `theorem.game_hops` (`domino proofsteps`' numbering).
    pub proofstep: usize,
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
/// `Pkg_KX.ec`, ... — story 10 §3.2: no `packages/`/`games/`
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
    /// `Pkg_*.ec` variant names (unprefixed, e.g. `"KX"`), discovery
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
/// `Pkg_*.ec`/`Comp_*.ec`.
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
/// Runs [`EasyCryptTransform`] itself — `theorem` is the plain,
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

    let (theorem, auxs) = EasyCryptTransform.transform_theorem(theorem)?;

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
            PathBuf::from(format!("Pkg_{}.ec", variant.name)),
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
            proofstep: ef.proof.proofstep,
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

    /// Writes `exported` to a scratch directory and compiles every file in
    /// dependency order (skips without `easycrypt`). `tag` only names the scratch
    /// directory.
    fn assert_tree_compiles(exported: &ExportedTheorem, tag: &str) {
        let tmp = std::env::temp_dir().join(format!(
            "domino-easycrypt-export-compile-test-{tag}-{}",
            std::process::id()
        ));
        let _ = std::fs::remove_dir_all(&tmp);
        write_files(&tmp, &exported.files).unwrap();
        let base = tmp.to_str().unwrap().to_string();
        let compile = super::super::test_support::assert_compiles;
        compile(&base, &format!("{base}/Types.ec"));
        compile(&base, &format!("{base}/Interfaces.ec"));
        for name in &exported.package_variant_names {
            compile(&base, &format!("{base}/Pkg_{name}.ec"));
        }
        for name in &exported.game_names {
            compile(&base, &format!("{base}/Comp_{name}.ec"));
        }
        for eq in &exported.equivalences {
            compile(&base, &format!("{base}/{}", eq.invariants_file));
            compile(&base, &format!("{base}/{}", eq.proof_file));
        }
        std::fs::remove_dir_all(&tmp).unwrap();
    }

    // Story 20: `hello-world`'s invariant was migrated from the old
    // solver-facing `GameState_` dialect to `define-state-relation`, so the
    // project now exports (this replaces the test that pinned the failure).
    #[test]
    fn hello_world_exports_its_one_equivalence() {
        let exported = export("example-projects/hello-world", "Proof").unwrap();
        assert_eq!(exported.equivalences.len(), 1);
        let eq = &exported.equivalences[0];
        assert_eq!(eq.left_name, "medium_composition");
        assert_eq!(eq.right_name, "small_composition");
        assert_eq!(eq.oracle_count, 1);
        assert_eq!(eq.admit_count, 1);
        assert_eq!(eq.oracle_set_mismatch, None);
        let invariants = &exported.files[Path::new(&eq.invariants_file)];
        assert!(
            invariants.contains(
                "op Domino_invariant (l : medium_composition_state) (r : small_composition_state) : bool = l.`l_pkg_rand_ctr = r.`r_pkg_rand_ctr."
            ),
            "{invariants}"
        );
    }

    #[test]
    fn hello_world_full_tree_compiles() {
        let exported = export("example-projects/hello-world", "Proof").unwrap();
        assert_tree_compiles(&exported, "hello-world");
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

    // Story 20: `simple-KEM-example` (literal-width `Bits(256)`) had its two
    // invariants migrated to `define-state-relation`; both equivalences now
    // export, four oracles each, the invariant relating every state field.
    #[test]
    fn simple_kem_example_exports_its_two_equivalences() {
        let exported = export("example-projects/simple-KEM-example", "KEM_Proof").unwrap();
        assert_eq!(exported.bits_type_names, vec!["bits_256"]);
        let pairs: Vec<(&str, &str)> = exported
            .equivalences
            .iter()
            .map(|eq| (eq.left_name.as_str(), eq.right_name.as_str()))
            .collect();
        assert_eq!(
            pairs,
            vec![
                ("Prot", "H1_kem_correctness_real"),
                ("H1_kem_correctness_ideal", "H2"),
            ]
        );
        for eq in &exported.equivalences {
            assert_eq!(eq.oracle_count, 4);
            assert_eq!(eq.oracle_set_mismatch, None);
        }
        let first = &exported.files[Path::new(&exported.equivalences[0].invariants_file)];
        for field in ["d_SENTCTXT", "d_SENTKEY", "d_RECEIVEDCTXT", "d_RECEIVEDKEY", "d_TESTED"] {
            assert!(
                first.contains(&format!("l.`l_pkg_Prot_{field} = r.`r_pkg_Corr_reduction_{field}")),
                "{field}: {first}"
            );
        }
        assert!(first.contains("l.`l_pkg_Prot_sk = r.`r_pkg_Corr_KEM_sk"), "{first}");
        let second = &exported.files[Path::new(&exported.equivalences[1].invariants_file)];
        assert!(second.contains("l.`l_pkg_Corr_reduction_ctr = r.`r_pkg_CPA_ctr"), "{second}");
        assert!(second.contains("l.`l_pkg_Corr_KEM_pk = r.`r_pkg_CPA_pk"), "{second}");
    }

    #[test]
    fn simple_kem_example_full_tree_compiles() {
        let exported = export("example-projects/simple-KEM-example", "KEM_Proof").unwrap();
        assert_tree_compiles(&exported, "simple-kem");
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

        // Story 19: the base case is one line, so the `smt` can never run on
        // the first oracle's goal when `auto => />` already closed the base.
        let proof = &exported.files[Path::new(&eq.proof_file)];
        assert!(proof.lines().any(|l| l.trim() == "auto => />; smt(emptyE map_empty)."));
        assert!(!proof.lines().any(|l| l.trim() == "smt(emptyE map_empty)."));
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
        assert_tree_compiles(&exported, "simple4whs");
    }

    #[test]
    fn kem_dem_cca_ssp_full_tree_compiles_in_dependency_order() {
        let exported = export(
            "example-projects/kem-dem/kem-dem-cca-ssp",
            "kem_dem_cca_ssp",
        )
        .unwrap();
        assert_tree_compiles(&exported, "kemdem");
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
        assert_tree_compiles(&exported, "full4whs");
    }
}
