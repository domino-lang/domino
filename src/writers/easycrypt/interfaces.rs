// SPDX-License-Identifier: MIT OR Apache-2.0

//! Building `Interfaces.ec` (`docs/stories/easycrypt/04-games-and-router.md`
//! §3.1): one `module type <Variant>_i` per package variant (story 03),
//! listing *all* of that variant's own oracles (not just the imported ones),
//! and one `module type Iface_<X>` / `Adv_<X> (O : Iface_<X>)` pair per
//! distinct **export signature list** across the theorem's compositions —
//! two compositions whose `exports` translate to the same [`ProcSig`] list
//! share one game interface (so both sides of an equivalence can take the
//! same adversary), named after the first composition (in `theorem.instances`
//! order) that has it.
//!
//! `game.rs` depends on this module for the `Iface_<X>`/`Adv_<X>` name a
//! composition's router/experiment reference, and for the per-composition
//! mangled base name (`Game_<X>`/`Exp_<X>`/`Comp_<X>.ec` all derive from the
//! same [`InterfacesOutput::comp_mangled`] entry, so a composition's naming
//! is computed once and agrees everywhere).

use std::collections::HashMap;

use miette::SourceSpan;

use crate::package::{Composition, Package};
use crate::theorem::Theorem;

use super::ast::{EcFile, EcItem, EcType, ProcSig, Require};
use super::names::{NameKind, Names};
use super::package;
use super::types::translate_type;
use super::EcExportError;

pub struct InterfacesOutput {
    pub file: EcFile,
    /// `comp.name` -> mangled EasyCrypt base name (e.g. `"Hybrid0"` ->
    /// `"Hybrid0"`, but not the identity in general — mangling can uppercase
    /// or prefix). `game.rs`'s `Game_<X>`/`Exp_<X>` module names and
    /// `Comp_<X>.ec` file name (story 10) all derive from this same entry.
    pub comp_mangled: HashMap<String, String>,
    /// `comp.name` -> the `Iface_<X>` module type this composition's router
    /// implements (its own, or a reused one from an earlier composition with
    /// the same export signature list).
    pub iface_name: HashMap<String, String>,
    /// `comp.name` -> the `Adv_<X>` module type this composition's
    /// experiment is parameterised by.
    pub adv_name: HashMap<String, String>,
}

/// One distinct composition per `theorem.instances` entry, deduplicated by
/// `comp.name` and kept in first-discovery (`theorem.instances`) order —
/// "several game instances share one composition — emit per composition, not
/// per instance" (`docs/stories/easycrypt/04-games-and-router.md` §2.2).
/// Shared with `game.rs`, which iterates the exact same list to emit
/// `Comp_<X>.ec` (story 10).
pub(super) fn discover_compositions(theorem: &Theorem<'_>) -> Vec<Composition> {
    let mut out: Vec<Composition> = Vec::new();
    for inst in &theorem.instances {
        let comp = inst.game();
        if !out.iter().any(|c| c.name == comp.name) {
            out.push(comp.clone());
        }
    }
    out
}

/// `Composition` carries no [`SourceSpan`] of its own, like `Theorem::consts`
/// (`typesfile.rs::theorem_level_span`) and `PackageInstance::types`
/// (`package.rs`'s `PackageTypeParameters` span) before it. Point at the
/// first oracle definition reachable from the composition's own packages,
/// else a zero-length placeholder.
pub(super) fn composition_span(comp: &Composition) -> SourceSpan {
    comp.pkgs
        .iter()
        .find_map(|inst| inst.pkg.oracles.first().map(|o| o.file_pos))
        .unwrap_or_else(|| (0, 0).into())
}

/// `module type <Variant>_i` (§3.1): every oracle the variant's own package
/// *defines*, not just the ones some caller happens to import — this keeps
/// the type independent of who calls it. `init` is deliberately absent:
/// routers call `init` on the concrete clone, never through this interface.
fn build_variant_procs(pkg: &Package) -> Result<Vec<ProcSig>, EcExportError> {
    let mut names = Names::new();
    let mut procs = Vec::new();
    for oracle in &pkg.oracles {
        let span = oracle.file_pos;
        let proc_name = names.mangle(NameKind::Proc, &oracle.sig.name)?;
        let mut args = Vec::new();
        for (name, ty) in &oracle.sig.args {
            let mangled = names.mangle(NameKind::Var, name)?;
            args.push((mangled, translate_type(ty, span)?));
        }
        let ret = EcType::Option(Box::new(translate_type(&oracle.sig.ty, span)?));
        procs.push(ProcSig {
            name: proc_name,
            args,
            ret,
        });
    }
    Ok(procs)
}

/// A composition's own canonical export signature list, in `comp.exports`
/// order — "oracle order inside a game interface is the composition's
/// `exports` order" (§3.1), load-bearing for story 07's per-oracle proof
/// bullets. Used both to render a game interface's `procs` and, via
/// [`Vec<ProcSig>`]'s structural equality, as the dedup key across
/// compositions: two compositions whose exports produce the exact same
/// `Vec<ProcSig>` (proc name, argument names and types, return type) share
/// one interface. A fresh [`Names`] per composition is correct (not a
/// collision-detection gap): each composition gets its own independent
/// `Iface_<X>` namespace, mirroring how `package.rs`'s `translate_invoke`
/// reuses a fresh registry to reproduce an already-validated namespace.
fn build_export_procs(comp: &Composition) -> Result<Vec<ProcSig>, EcExportError> {
    let span = composition_span(comp);
    let mut names = Names::new();
    let mut procs = Vec::new();
    for export in &comp.exports {
        let proc_name = names.mangle(NameKind::Proc, export.name())?;
        let mut args = Vec::new();
        for (name, ty) in &export.sig().args {
            let mangled = names.mangle(NameKind::Var, name)?;
            args.push((mangled, translate_type(ty, span)?));
        }
        let ret = EcType::Option(Box::new(translate_type(&export.sig().ty, span)?));
        procs.push(ProcSig {
            name: proc_name,
            args,
            ret,
        });
    }
    Ok(procs)
}

/// Builds `Interfaces.ec` for `theorem` (§3.1).
pub fn build_interfaces_file(theorem: &Theorem<'_>) -> Result<InterfacesOutput, EcExportError> {
    let mut items = Vec::new();

    // --- one module type per package variant, grouped by signature --------
    // (story 11, §3.1-3.2): every variant still gets its own `<Variant>_i`
    // name (no call site's `Interfaces.<callee_variant>_i` reference
    // changes, `package.rs:419`), but variants whose oracle signature list
    // is structurally identical share one real declaration — the first
    // discovered in the group — and every other member becomes
    // `{ include <Canonical>_i }.`. This is a readability/file-size change
    // only: EasyCrypt module-type matching is structural and
    // width-subtyping, so the duplicated declarations were never a
    // correctness issue (`docs/stories/easycrypt/11-shared-package-module-types.md`
    // §1.1).
    let discovered = package::discover_variants(theorem);
    let mut variant_names = Names::new();
    let variant_name_map = package::assign_names(&discovered, &mut variant_names)?;

    // `(variant_name, oracle signature list)` per discovered variant, in
    // discovery order.
    let mut variant_infos: Vec<(String, Vec<ProcSig>)> = Vec::with_capacity(discovered.len());
    for (key, comp, idx) in &discovered {
        let variant_name = variant_name_map
            .get(key)
            .expect("every discovered key was named in assign_names")
            .clone();
        let pkg = &comp.pkgs[*idx].pkg;
        variant_infos.push((variant_name, build_variant_procs(pkg)?));
    }

    // Group variant indices by structurally-equal signature lists,
    // preserving first-discovery order both across groups and within one —
    // the exact same grouping shape as the game-interface grouping below,
    // reused here one level down.
    let mut variant_groups: Vec<Vec<usize>> = Vec::new();
    for i in 0..variant_infos.len() {
        match variant_groups
            .iter_mut()
            .find(|g| variant_infos[g[0]].1 == variant_infos[i].1)
        {
            Some(g) => g.push(i),
            None => variant_groups.push(vec![i]),
        }
    }

    for group in &variant_groups {
        let primary = group[0];
        let canonical_name = format!("{}_i", variant_infos[primary].0);

        // The canonical declaration always comes first in the file (§6:
        // "alias direction is load-bearing") — discovery order gives that
        // for free since `primary` is the group's first-discovered member.
        items.push(EcItem::ModuleType {
            name: canonical_name.clone(),
            params: vec![],
            includes: vec![],
            procs: variant_infos[primary].1.clone(),
        });

        if group.len() > 1 {
            let others: Vec<String> = group[1..]
                .iter()
                .map(|&i| format!("{}_i", variant_infos[i].0))
                .collect();
            items.push(EcItem::Comment(format!(
                "{} share {canonical_name}'s signature",
                others.join(", ")
            )));
            for &i in &group[1..] {
                items.push(EcItem::ModuleType {
                    name: format!("{}_i", variant_infos[i].0),
                    params: vec![],
                    includes: vec![canonical_name.clone()],
                    procs: vec![],
                });
            }
        }
    }

    // --- one game interface per distinct export signature list -------------
    let comps = discover_compositions(theorem);

    // A composition's mangled base name and a package variant's live in two
    // independent `Names` registries (story 03's and this one's own) and
    // never share a namespace: a package variant renders into
    // `Variant_<Variant>.ec` and a composition into `Comp_<Comp>.ec` (story
    // 10), so a composition and a package variant that both mangle to
    // `PRF` (as `4WHS` has it) produce `Variant_PRF.ec`/`module PRF` and
    // `Comp_PRF.ec`/`module Game_PRF`/`module Exp_PRF` — no collision, and
    // no escape hatch needed.
    let mut comp_names = Names::new();
    let mut comp_mangled = HashMap::new();
    for comp in &comps {
        let mangled = comp_names.mangle(NameKind::Module, &comp.name)?;
        comp_mangled.insert(comp.name.clone(), mangled);
    }

    let mut canonical: Vec<Vec<ProcSig>> = Vec::with_capacity(comps.len());
    for comp in &comps {
        canonical.push(build_export_procs(comp)?);
    }

    // Group composition indices by structurally-equal `canonical` entries,
    // preserving first-discovery order both across groups and within one.
    let mut groups: Vec<Vec<usize>> = Vec::new();
    for i in 0..comps.len() {
        match groups
            .iter_mut()
            .find(|g| canonical[g[0]] == canonical[i])
        {
            Some(g) => g.push(i),
            None => groups.push(vec![i]),
        }
    }

    let mut iface_name = HashMap::new();
    let mut adv_name = HashMap::new();
    for group in &groups {
        let primary = group[0];
        let mangled = comp_mangled[&comps[primary].name].clone();
        let this_iface = format!("Iface_{mangled}");
        let this_adv = format!("Adv_{mangled}");

        if group.len() > 1 {
            let others: Vec<String> = group[1..]
                .iter()
                .map(|&i| comp_mangled[&comps[i].name].clone())
                .collect();
            items.push(EcItem::Comment(format!(
                "{this_iface}/{this_adv} also cover: {}",
                others.join(", ")
            )));
        }

        items.push(EcItem::ModuleType {
            name: this_iface.clone(),
            params: vec![],
            includes: vec![],
            procs: canonical[primary].clone(),
        });
        items.push(EcItem::ModuleType {
            name: this_adv.clone(),
            params: vec![("O".to_string(), this_iface.clone())],
            includes: vec![],
            procs: vec![ProcSig {
                name: "run".to_string(),
                args: vec![],
                ret: EcType::Bool,
            }],
        });

        for &i in group {
            iface_name.insert(comps[i].name.clone(), this_iface.clone());
            adv_name.insert(comps[i].name.clone(), this_adv.clone());
        }
    }

    let file = EcFile {
        header: vec![format!(
            "Interfaces.ec for theorem `{}` — generated by `domino easycrypt`.",
            theorem.name
        )],
        requires: vec![Require {
            import: true,
            names: vec![
                "AllCore".to_string(),
                "FMap".to_string(),
                "Distr".to_string(),
                "Int".to_string(),
                "Types".to_string(),
            ],
        }],
        items,
    };

    Ok(InterfacesOutput {
        file,
        comp_mangled,
        iface_name,
        adv_name,
    })
}

#[cfg(test)]
mod tests {
    use std::path::{Path, PathBuf};

    use crate::project::{DirectoryFiles, DirectoryProject, Project};
    use crate::transforms::theorem_transforms::EquivalenceTransform;
    use crate::transforms::TheoremTransform;

    use super::super::render::render_file;
    use super::*;

    fn load(dir: &str, theorem_name: &str) -> InterfacesOutput {
        let files: &'static DirectoryFiles =
            Box::leak(Box::new(DirectoryFiles::load(Path::new(dir)).unwrap()));
        let project: &'static DirectoryProject =
            Box::leak(Box::new(DirectoryProject::load(PathBuf::from(dir), files).unwrap()));
        let theorem = project.get_theorem(theorem_name).unwrap();
        let (theorem, _auxs) = EquivalenceTransform.transform_theorem(theorem).unwrap();
        build_interfaces_file(&theorem).unwrap()
    }

    fn assert_golden(out: &InterfacesOutput, golden_path: &str) {
        let rendered = render_file(&out.file);
        let full_path = format!("{}/{golden_path}", env!("CARGO_MANIFEST_DIR"));
        let expected = std::fs::read_to_string(&full_path)
            .unwrap_or_else(|e| panic!("failed to read golden file {full_path}: {e}"));
        assert_eq!(rendered, expected, "rendered Interfaces.ec != {full_path}");
    }

    fn assert_compiles(dir: &str, file: &str) {
        let full_dir = format!("{}/{dir}", env!("CARGO_MANIFEST_DIR"));
        let full_file = format!("{full_dir}/{file}");
        crate::writers::easycrypt::test_support::assert_compiles(&full_dir, &full_file);
    }

    // --- real-project golden files ------------------------------------------

    #[test]
    fn hello_world_interfaces_match_golden() {
        let out = load("example-projects/hello-world", "Proof");
        assert_golden(
            &out,
            "testdata/easycrypt/story04/hello-world/Interfaces.ec",
        );
    }

    #[test]
    fn hello_world_interfaces_compiles() {
        assert_compiles(
            "testdata/easycrypt/story04/hello-world",
            "Interfaces.ec",
        );
    }

    #[test]
    fn simple_4whs_interfaces_match_golden() {
        let out = load("example-projects/4WHS", "Simple4WHS");
        assert_golden(&out, "testdata/easycrypt/story04/4WHS/Interfaces.ec");
    }

    #[test]
    fn simple_4whs_interfaces_compiles() {
        assert_compiles("testdata/easycrypt/story04/4WHS", "Interfaces.ec");
    }

    #[test]
    fn simple_4whs_hybrid0_and_hybrid1_reuse_one_interface() {
        // Acceptance criterion: "Interfaces.ec reuses one game interface for
        // Hybrid0 and Hybrid1 (same exports)".
        let out = load("example-projects/4WHS", "Simple4WHS");
        assert_eq!(out.iface_name["Hybrid0"], out.iface_name["Hybrid1"]);
        assert_eq!(out.adv_name["Hybrid0"], out.adv_name["Hybrid1"]);
    }

    #[test]
    fn simple_4whs_prf_has_its_own_interface() {
        // PRF's export list (NewKey/Eval/Hon) differs from Hybrid0's
        // (9 KX-shaped oracles), so it must not be folded into Iface_Hybrid0.
        let out = load("example-projects/4WHS", "Simple4WHS");
        assert_ne!(out.iface_name["PRF"], out.iface_name["Hybrid0"]);
    }

    #[test]
    fn hello_world_fwd_v1_and_fwd_v2_alias_rand() {
        // Story 11 acceptance criterion: hello-world's two-oracle signature
        // is declared once (`Rand_i`) and `Fwd_v1_i`/`Fwd_v2_i` become
        // `{ include Rand_i }.` aliases — not three verbatim copies.
        let out = load("example-projects/hello-world", "Proof");
        let rendered = render_file(&out.file);
        // Restrict the "spelled out once" check to the package-variant
        // section (before the game-interface section starts): a game
        // interface coincidentally sharing an oracle name with a package
        // variant is expected and not deduplicated across that boundary
        // (§6), so counting across the whole file would conflate the two.
        let variant_section = rendered
            .split_once("module type Iface_")
            .map(|(before, _)| before)
            .unwrap_or(&rendered);
        assert_eq!(
            variant_section.matches("proc d_UsefulOracle").count(),
            1,
            "the shared oracle signature must be spelled out exactly once in the \
             package-variant section:\n{variant_section}"
        );
        assert!(
            rendered.contains("module type Fwd_v1_i = { include Rand_i }."),
            "Fwd_v1_i must alias Rand_i:\n{rendered}"
        );
        assert!(
            rendered.contains("module type Fwd_v2_i = { include Rand_i }."),
            "Fwd_v2_i must alias Rand_i:\n{rendered}"
        );
    }

    #[test]
    fn simple_4whs_no_variant_module_type_is_an_alias() {
        // Story 11 §4 acceptance criterion: 4WHS's Interfaces.ec is a
        // deliberate no-op — none of its seven package variants
        // (Prot/Prot_NoKey/Prot_NoPrf differ in state-tuple shape,
        // KX/KX_NoKeys/KX_NoPrf in oracle count, PRF is unique) share a
        // signature, so no `{ include ... }` alias should be emitted for
        // any of them.
        let out = load("example-projects/4WHS", "Simple4WHS");
        let rendered = render_file(&out.file);
        assert!(
            !rendered.contains("{ include"),
            "4WHS has no two variants sharing a signature, so no alias should be emitted:\n{rendered}"
        );
    }

    #[test]
    fn rendering_is_deterministic() {
        let a = load("example-projects/4WHS", "Simple4WHS");
        let b = load("example-projects/4WHS", "Simple4WHS");
        assert_eq!(render_file(&a.file), render_file(&b.file));
    }
}

