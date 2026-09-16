// SPDX-License-Identifier: MIT OR Apache-2.0

//! `export_theorem` (`docs/stories/easycrypt/05-easycrypt-command.md` §3.4):
//! the one function that turns a Domino [`Theorem`] into the in-memory
//! contents of an EasyCrypt project — `Types.ec`, `Interfaces.ec`,
//! `packages/*.ec`, `games/*.ec` — plus the data `domino easycrypt`'s stdout
//! report is built from. It runs [`EquivalenceTransform`] itself (§2 of the
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
use crate::theorem::{RandomnessType, Theorem};
use crate::transforms::theorem_transforms::EquivalenceTransform;
use crate::transforms::TheoremTransform;
use crate::types::Type;

use super::game::compute_game_files;
use super::interfaces::build_interfaces_file;
use super::package::compute_package_variants;
use super::render::render_file;
use super::types::func_op_name;
use super::typesfile::{build_types_file, collect_bits_types, collect_fn_consts};
use super::EcExportError;

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
/// paths relative to the theorem's own output directory (`Types.ec`,
/// `packages/KX.ec`, ...); [`write_files`] joins them onto an `out` root.
/// The remaining fields are exactly the data `domino easycrypt`'s stdout
/// report (§3.3) needs, computed once here so the report never re-derives it
/// (and can never disagree with what was actually written).
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
    /// `packages/*.ec` variant names, discovery order.
    pub package_variant_names: Vec<String>,
    /// `games/*.ec` composition names, discovery order.
    pub game_names: Vec<String>,
    /// How many oracles, across this theorem's equivalence hops (direct or
    /// nested in a hybrid), declare an explicit `randomness: simple`/`none`
    /// mapping — a feature this epic does not translate (see
    /// [`super::EcExportError`]'s doc and `Equivalence::randomness`).
    pub randomness_mapping_oracles: usize,
}

/// The kind + reason for a hop this exporter skips, or `None` for
/// [`GameHop::Equivalence`], which is exactly what §3.2 translates into
/// `packages/*.ec`/`games/*.ec`.
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
/// `EquivalenceContext`").
pub fn export_theorem(theorem: &Theorem<'_>) -> Result<ExportedTheorem, EcExportError> {
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
            PathBuf::from(format!("packages/{}.ec", variant.name)),
            render_file(&variant.file),
        );
    }
    for game in &game_files {
        files.insert(
            PathBuf::from(format!("games/{}.ec", game.name)),
            render_file(&game.file),
        );
    }

    Ok(ExportedTheorem {
        files,
        skipped,
        bits_type_names,
        fn_const_names,
        package_variant_names,
        game_names,
        randomness_mapping_oracles,
    })
}

/// Writes every entry of `exported.files` under `out_dir`, creating
/// `packages/`/`games/` as needed. The caller (`domino easycrypt`) only
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
        export_theorem(theorem)
    }

    #[test]
    fn hello_world_exports_expected_files() {
        let exported = export("example-projects/hello-world", "Proof").unwrap();
        let paths: Vec<&str> = exported.files.keys().map(|p| p.to_str().unwrap()).collect();
        assert!(paths.contains(&"Types.ec"));
        assert!(paths.contains(&"Interfaces.ec"));
        assert!(paths.iter().any(|p| p.starts_with("packages/")));
        assert!(paths.iter().any(|p| p.starts_with("games/")));
        // `theorem/Proof.ssp` has one reduction hop (`big_composition` ~
        // `medium_composition_more_oracles`), so it must be reported skipped.
        assert_eq!(
            exported.skipped,
            vec![SkipNote {
                kind: "reduction",
                left: "big_composition".to_string(),
                right: "medium_composition_more_oracles".to_string(),
                reason: "reductions are not translated",
            }]
        );
        // `UsefulOracle` in the one equivalence hop declares `randomness: simple`.
        assert_eq!(exported.randomness_mapping_oracles, 1);
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
            vec!["Hybrid0", "Hybrid1", "Hybrid2", "PRF_Game"]
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
                "M_PRF",
                "Prot",
                "Prot_NoKey",
                "Prot_NoPrf"
            ]
        );
    }

    #[test]
    fn full_4whs_exports_only_that_theorem() {
        let exported = export("example-projects/4WHS", "Full4WHS").unwrap();
        assert!(!exported.game_names.is_empty());
    }

    // Acceptance §4's other two target projects, beyond hello-world/4WHS
    // above: literal-width `Bits(256)` (simple-KEM-example) and real
    // branching/sampling/cross-package invokes plus a hand-written
    // invariant (kem-dem-cca-ssp) — both must export without error.

    #[test]
    fn simple_kem_example_exports_without_error() {
        let exported = export("example-projects/simple-KEM-example", "KEM_Proof").unwrap();
        assert!(exported.files.contains_key(Path::new("Types.ec")));
        assert!(!exported.package_variant_names.is_empty());
        assert!(!exported.game_names.is_empty());
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
        let exported = export("example-projects/hello-world", "Proof").unwrap();
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
        let packages = tmp.join("packages").to_str().unwrap().to_string();
        let games = tmp.join("games").to_str().unwrap().to_string();

        super::super::test_support::assert_compiles(&base, &format!("{base}/Types.ec"));
        super::super::test_support::assert_compiles(&base, &format!("{base}/Interfaces.ec"));
        for name in &exported.package_variant_names {
            super::super::test_support::assert_compiles(&base, &format!("{packages}/{name}.ec"));
        }
        for name in &exported.game_names {
            super::super::test_support::assert_compiles_with_paths(
                &[&base, &packages, &games],
                &format!("{games}/{name}.ec"),
            );
        }

        std::fs::remove_dir_all(&tmp).unwrap();
    }
}
