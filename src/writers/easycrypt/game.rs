// SPDX-License-Identifier: MIT OR Apache-2.0

//! Building `Comp_<Comp>.ec` (`docs/stories/easycrypt/04-games-and-router.md`
//! §3.2, file name amended by story 10 §3.1): one file per distinct
//! **composition** — several game instances can share one composition
//! (`theorem.instances` in `Simple4WHS` maps `Real`, `Ideal` and `Hybrid0`
//! all onto the `Hybrid0` composition), so this emits per composition, not
//! per instance, deduplicated by [`interfaces::discover_compositions`].
//!
//! Each file gets: one `clone Variant_<Variant> as Pkg_<inst>.` per package
//! instance (story 03's variants, resolved here via the same
//! [`package::VariantKey`] machinery story 03 uses internally); a `module
//! Inst_<inst> = ...` functor-application alias for every instance that
//! imports oracles; a router module (`Game_<Comp>`) carrying the single
//! `abort_flag : bool` and one export proc per `comp.exports` entry; and an
//! experiment module (`Exp_<Comp>`) that initialises the router and runs the
//! adversary. Only the *theory* (file) names carry the `Variant_`/`Comp_`
//! prefix (story 10) — every module name, clone alias and functor
//! application keeps its pre-story-10 spelling.

use std::collections::HashMap;

use miette::SourceSpan;

use crate::expressions::{Expression, ExpressionKind};
use crate::identifier::{game_ident::GameIdentifier, Identifier};
use crate::package::{Composition, PackageInstance};
use crate::theorem::Theorem;
use crate::types::{Type, TypeKind};

use super::ast::{
    EcBinop, EcBlock, EcExpr, EcFile, EcItem, EcLvalue, EcModule, EcProc, EcStmt, EcType, EcUnop,
    Require,
};
use super::interfaces::{self, InterfacesOutput};
use super::names::{NameKind, Names};
use super::package::{self, VariantKey};
use super::types::{translate_expr, translate_type};
use super::EcExportError;

/// One deduplicated composition's rendered game file, ready for
/// `Comp_<name>.ec` (story 10) — `name` itself is unprefixed (it is also
/// `Game_<name>`/`Exp_<name>`'s own base), the `Comp_` prefix is added only
/// where the file is written (`export.rs`).
pub struct GameFile {
    pub name: String,
    pub file: EcFile,
}

/// Computes every composition's game file for `theorem` (§3.2), one per
/// distinct composition (`interfaces::discover_compositions`), deterministic
/// and in first-discovery (`theorem.instances`) order.
pub fn compute_game_files(theorem: &Theorem<'_>) -> Result<Vec<GameFile>, EcExportError> {
    let interfaces = interfaces::build_interfaces_file(theorem)?;

    let discovered = package::discover_variants(theorem);
    let mut variant_names = Names::new();
    let variant_name_map = package::assign_names(&discovered, &mut variant_names)?;

    let comps = interfaces::discover_compositions(theorem);
    let mut out = Vec::with_capacity(comps.len());
    for comp in &comps {
        let file = render_game_file(&theorem.name, comp, &interfaces, &variant_name_map)?;
        let mangled = interfaces.comp_mangled[&comp.name].clone();
        out.push(GameFile { name: mangled, file });
    }
    Ok(out)
}

fn param_assignment<'a>(inst: &'a PackageInstance, name: &str) -> &'a Expression {
    inst.params
        .iter()
        .find(|(id, _)| id.name == name)
        .map(|(_, e)| e)
        .expect("a package instance assigns every one of its package's declared params")
}

/// A composition-level param binding is always either a literal or a bare
/// reference to one of the enclosing composition's own `const`s, never a
/// compound expression — the same constraint that lets
/// `CountSpec::Identifier` require a bare [`Identifier`] rather than an
/// arbitrary expression, since `type_extract` must already be able to
/// resolve a `Bits` width through this exact link before export runs. A
/// recursive expression walk is therefore unnecessary here.
fn references_game_const(expr: &Expression, name: &str) -> bool {
    matches!(
        expr.kind(),
        ExpressionKind::Identifier(Identifier::GameIdentifier(GameIdentifier::Const(c)))
            if c.name == name
    )
}

/// Whether a composition-level `Integer` const is purely a `Bits` width —
/// and so gets no `init` argument, mirroring "width integers ... are not
/// arguments" (§3.2) — determined the same way story 03 decides a package
/// param needs a module var
/// ([`package::param_needs_var`]/[`package::integer_param_used_as_width`]):
/// it is width-only iff it is referenced by at least one package
/// instantiation's param binding and *every* such reference feeds a
/// package param that is itself width-only in its own package. An
/// **unreferenced** composition const is not provably a width, so it is
/// conservatively kept as a genuine value — matching §6's "composition
/// constants that are unused still become init parameters" (keeping the
/// signature positional and complete is what lets story 07 pass a game
/// instance's bindings straight through).
fn composition_int_const_is_width_only(comp: &Composition, const_name: &str) -> bool {
    let mut referenced = false;
    for inst in &comp.pkgs {
        for (pname, pty, _) in &inst.pkg.params {
            let assigned = param_assignment(inst, pname);
            if references_game_const(assigned, const_name) {
                referenced = true;
                if package::param_needs_var(&inst.pkg, pname, pty) {
                    return false;
                }
            }
        }
    }
    referenced
}

/// Whether a composition-level const becomes a router `init` argument
/// (§3.2): every `Boolean` const does; an `Integer` const does unless it is
/// purely a `Bits` width; a `Fn` const never does (function constants become
/// global operators, not runtime arguments). Shared with story 07
/// (`proof.rs`), which needs the exact same filter — applied to each side's
/// own composition — to know a `Pr[...]`'s `run(...)` argument list.
pub(super) fn composition_const_needs_arg(comp: &Composition, name: &str, ty: &Type) -> bool {
    match ty.kind() {
        TypeKind::Boolean => true,
        TypeKind::Integer => !composition_int_const_is_width_only(comp, name),
        _ => false,
    }
}

/// Resolves a `GameIdentifier::Const` occurring inside a package
/// instantiation's param-binding expression to the router's own `init`
/// argument for it — the only identifier kind that can occur there (see
/// [`references_game_const`]'s doc comment).
fn resolve_composition_const(
    id: &Identifier,
    _span: SourceSpan,
    names: &mut Names,
) -> Result<EcExpr, EcExportError> {
    match id {
        Identifier::GameIdentifier(GameIdentifier::Const(c)) => {
            Ok(EcExpr::Var(names.mangle(NameKind::Var, &c.name)?))
        }
        other => unreachable!(
            "a package instantiation's param binding at composition scope referenced an \
             unexpected identifier kind (only a composition's own consts can appear here): \
             {other:?}"
        ),
    }
}

fn render_game_file(
    theorem_name: &str,
    comp: &Composition,
    interfaces: &InterfacesOutput,
    variant_name_map: &HashMap<VariantKey, String>,
) -> Result<EcFile, EcExportError> {
    let span = interfaces::composition_span(comp);
    let mangled = &interfaces.comp_mangled[&comp.name];
    let iface = &interfaces.iface_name[&comp.name];
    let adv = &interfaces.adv_name[&comp.name];

    let keys = package::compute_all_keys(comp);
    let variant_names: Vec<String> = keys
        .iter()
        .map(|k| {
            variant_name_map
                .get(k)
                .expect("every key computed here was named by the same discovery this theorem's compute_package_variants uses")
                .clone()
        })
        .collect();

    let order = comp.ordered_pkgs_idx();

    // One dedicated registry for instance-name mangling (`Pkg_<inst>` /
    // `Inst_<inst>` both derive from it) — a fresh, call-scoped `Names`
    // shared across the whole composition, mirroring `package.rs`'s
    // `functor_names` precedent, so two differently-named instances that
    // happened to mangle to the same name are caught as a hard collision
    // instead of silently colliding.
    let mut inst_names = Names::new();
    let mut inst_mangled: Vec<String> = Vec::with_capacity(comp.pkgs.len());
    for inst in &comp.pkgs {
        inst_mangled.push(inst_names.mangle(NameKind::Module, &inst.name)?);
    }
    let clone_name: Vec<String> = inst_mangled.iter().map(|m| format!("Pkg_{m}")).collect();

    // Functor arguments per instance, in edge order grouped by first
    // occurrence of the callee (§3.2) — mirrors `package.rs`'s
    // `build_functor_params` grouping exactly, over the same `comp.edges`,
    // so the argument order here always lines up with that variant's own
    // already-rendered functor parameter order.
    let mut functor_callees: Vec<Vec<usize>> = vec![Vec::new(); comp.pkgs.len()];
    for (idx, callees) in functor_callees.iter_mut().enumerate() {
        for edge in comp.edges.iter().filter(|e| e.from() == idx) {
            if !callees.contains(&edge.to()) {
                callees.push(edge.to());
            }
        }
    }

    // What to call this instance's procs on: starts as the dotted clone
    // path, upgraded to `Inst_<inst>` below for instances with functor
    // params. Processing in `order` (callees before callers) guarantees a
    // callee's final `module_ref` entry is already settled before a caller
    // reads it to build its own alias's argument list.
    let mut module_ref: Vec<String> = (0..comp.pkgs.len())
        .map(|idx| format!("{}.{}", clone_name[idx], variant_names[idx]))
        .collect();

    let mut alias_items = Vec::new();
    for &idx in &order {
        if functor_callees[idx].is_empty() {
            continue;
        }
        let alias_name = format!("Inst_{}", inst_mangled[idx]);
        let args: Vec<String> = functor_callees[idx]
            .iter()
            .map(|&callee| module_ref[callee].clone())
            .collect();
        alias_items.push(EcItem::ModuleAlias {
            name: alias_name.clone(),
            functor: format!("{}.{}", clone_name[idx], variant_names[idx]),
            args,
        });
        module_ref[idx] = alias_name;
    }

    // The theory a package variant renders into is `Variant_<Variant>.ec`
    // (story 10) — the module inside it keeps its own unprefixed name
    // (`variant_names[idx]`), so `clone`'s `base` (the theory being cloned)
    // and the `require` list need the `Variant_` prefix, but every
    // qualified reference to the resulting module (`Pkg_<inst>.<Variant>`)
    // does not, since that resolves through the *local* clone alias, not
    // the theory name.
    let clone_items: Vec<EcItem> = order
        .iter()
        .map(|&idx| EcItem::Clone {
            base: format!("Variant_{}", variant_names[idx]),
            as_name: clone_name[idx].clone(),
            overrides: vec![],
        })
        .collect();

    let mut variant_requires: Vec<String> = Vec::new();
    for &idx in &order {
        if !variant_requires.contains(&variant_names[idx]) {
            variant_requires.push(variant_names[idx].clone());
        }
    }
    let mut plain_requires = vec!["Interfaces".to_string()];
    plain_requires.extend(variant_requires.iter().map(|v| format!("Variant_{v}")));

    // --- router -------------------------------------------------------
    let mut router_names = Names::new();
    let abort_flag = router_names.mangle(NameKind::Var, "abort_flag")?;

    let mut init_args: Vec<(String, EcType)> = Vec::new();
    for (name, ty) in &comp.consts {
        if composition_const_needs_arg(comp, name, ty) {
            let mangled_name = router_names.mangle(NameKind::Var, name)?;
            init_args.push((mangled_name, translate_type(ty, span)?));
        }
    }

    let mut init_body = vec![EcStmt::Assign {
        lhs: EcLvalue::Var(abort_flag.clone()),
        rhs: EcExpr::Bool(false),
    }];
    for &idx in &order {
        let inst = &comp.pkgs[idx];
        let pkg = &inst.pkg;
        if !package::pkg_needs_init(pkg) {
            continue;
        }
        let mut call_args = Vec::new();
        for (name, ty, pspan) in &pkg.params {
            if !package::param_needs_var(pkg, name, ty) {
                continue;
            }
            let assigned = param_assignment(inst, name);
            let mut resolver =
                |id: &Identifier, s: SourceSpan| resolve_composition_const(id, s, &mut router_names);
            call_args.push(translate_expr(assigned, *pspan, &mut resolver)?);
        }
        init_body.push(EcStmt::Call {
            lhs: None,
            module: module_ref[idx].clone(),
            proc: "init".to_string(),
            args: call_args,
        });
    }
    let init_proc = EcProc {
        name: "init".to_string(),
        args: init_args.clone(),
        ret: EcType::Unit,
        locals: vec![],
        body: EcBlock(init_body),
        ret_expr: None,
    };

    let mut export_procs = Vec::new();
    for export in &comp.exports {
        let proc_name = router_names.mangle(NameKind::Proc, export.name())?;
        let mut args = Vec::new();
        for (name, ty) in &export.sig().args {
            let mangled_name = router_names.mangle(NameKind::Var, name)?;
            args.push((mangled_name, translate_type(ty, span)?));
        }
        let ret_ec_ty = translate_type(&export.sig().ty, span)?;
        let ret_option_ty = EcType::Option(Box::new(ret_ec_ty.clone()));

        // A fresh registry is correct here (not a collision-detection gap):
        // it reproduces the callee's own already-validated `Proc`-namespace
        // mangling of one name, mirroring `package.rs`'s `translate_invoke`.
        let callee_proc = Names::new().mangle(NameKind::Proc, &export.sig().name)?;
        let call_args: Vec<EcExpr> = args.iter().map(|(n, _)| EcExpr::Var(n.clone())).collect();

        let body = EcBlock(vec![EcStmt::If {
            cond: EcExpr::Unop {
                op: EcUnop::Not,
                arg: Box::new(EcExpr::Var(abort_flag.clone())),
            },
            then_block: EcBlock(vec![
                EcStmt::Call {
                    lhs: Some(EcLvalue::Var("ec_result".to_string())),
                    module: module_ref[export.to()].clone(),
                    proc: callee_proc,
                    args: call_args,
                },
                EcStmt::If {
                    cond: EcExpr::Binop {
                        op: EcBinop::Eq,
                        lhs: Box::new(EcExpr::Var("ec_result".to_string())),
                        rhs: Box::new(EcExpr::None_(ret_ec_ty.clone())),
                    },
                    then_block: EcBlock(vec![EcStmt::Assign {
                        lhs: EcLvalue::Var(abort_flag.clone()),
                        rhs: EcExpr::Bool(true),
                    }]),
                    else_block: None,
                },
            ]),
            else_block: None,
        }]);

        export_procs.push(EcProc {
            name: proc_name,
            args,
            ret: ret_option_ty.clone(),
            locals: vec![(
                "ec_result".to_string(),
                ret_option_ty,
                Some(EcExpr::None_(ret_ec_ty)),
            )],
            body,
            ret_expr: Some(EcExpr::Var("ec_result".to_string())),
        });
    }

    let mut procs = vec![init_proc];
    procs.extend(export_procs);

    let router_module_name = format!("Game_{mangled}");
    let router = EcModule {
        name: router_module_name.clone(),
        params: vec![],
        implements: Some(format!("Interfaces.{iface}")),
        vars: vec![(abort_flag, EcType::Bool)],
        procs,
    };

    // --- experiment -----------------------------------------------------
    let run_proc = EcProc {
        name: "run".to_string(),
        args: init_args.clone(),
        ret: EcType::Bool,
        locals: vec![("b'".to_string(), EcType::Bool, None)],
        body: EcBlock(vec![
            EcStmt::Call {
                lhs: None,
                module: router_module_name.clone(),
                proc: "init".to_string(),
                args: init_args.iter().map(|(n, _)| EcExpr::Var(n.clone())).collect(),
            },
            EcStmt::Call {
                lhs: Some(EcLvalue::Var("b'".to_string())),
                module: format!("A({router_module_name})"),
                proc: "run".to_string(),
                args: vec![],
            },
        ]),
        ret_expr: Some(EcExpr::Var("b'".to_string())),
    };
    let exp = EcModule {
        name: format!("Exp_{mangled}"),
        params: vec![("A".to_string(), format!("Interfaces.{adv}"))],
        implements: None,
        vars: vec![],
        procs: vec![run_proc],
    };

    let mut items = clone_items;
    items.extend(alias_items);
    items.push(EcItem::Module(router));
    items.push(EcItem::Module(exp));

    Ok(EcFile {
        header: vec![format!(
            "Comp_{mangled}.ec for theorem `{theorem_name}`, composition `{}` — generated by \
             `domino easycrypt`.",
            comp.name
        )],
        requires: vec![
            Require {
                import: true,
                names: vec![
                    "AllCore".to_string(),
                    "Distr".to_string(),
                    "FMap".to_string(),
                    "Int".to_string(),
                    "IntDiv".to_string(),
                    "Types".to_string(),
                ],
            },
            Require {
                import: false,
                names: plain_requires,
            },
        ],
        items,
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

    fn load(dir: &str, theorem_name: &str) -> Vec<GameFile> {
        let files: &'static DirectoryFiles =
            Box::leak(Box::new(DirectoryFiles::load(Path::new(dir)).unwrap()));
        let project: &'static DirectoryProject =
            Box::leak(Box::new(DirectoryProject::load(PathBuf::from(dir), files).unwrap()));
        let theorem = project.get_theorem(theorem_name).unwrap();
        let (theorem, _auxs) = EquivalenceTransform.transform_theorem(theorem).unwrap();
        compute_game_files(&theorem).unwrap()
    }

    fn assert_golden(file: &GameFile, golden_path: &str) {
        let rendered = render_file(&file.file);
        let full_path = format!("{}/{golden_path}", env!("CARGO_MANIFEST_DIR"));
        let expected = std::fs::read_to_string(&full_path)
            .unwrap_or_else(|e| panic!("failed to read golden file {full_path}: {e}"));
        assert_eq!(
            rendered, expected,
            "rendered Comp_{}.ec != {full_path}",
            file.name
        );
    }

    fn assert_compiles(base_dir: &str, file: &str) {
        let full_base = format!("{}/{base_dir}", env!("CARGO_MANIFEST_DIR"));
        let full_file = format!("{full_base}/{file}");
        crate::writers::easycrypt::test_support::assert_compiles(&full_base, &full_file);
    }

    // --- real-project golden files ------------------------------------------

    #[test]
    fn hello_world_games_match_golden() {
        let files = load("example-projects/hello-world", "Proof");
        assert_eq!(
            files.iter().map(|f| f.name.as_str()).collect::<Vec<_>>(),
            vec![
                "SmallComposition",
                "MediumComposition",
                "MediumCompositionMoreOracles",
                "BigComposition"
            ]
        );
        for f in &files {
            assert_golden(
                f,
                &format!("testdata/easycrypt/story04/hello-world/Comp_{}.ec", f.name),
            );
        }
    }

    #[test]
    fn hello_world_games_compile() {
        for name in [
            "SmallComposition",
            "MediumComposition",
            "MediumCompositionMoreOracles",
            "BigComposition",
        ] {
            assert_compiles(
                "testdata/easycrypt/story04/hello-world",
                &format!("Comp_{name}.ec"),
            );
        }
    }

    #[test]
    fn big_composition_has_two_instance_clones_of_the_fwd_package() {
        // Acceptance criterion: "hello-world exports a composition with two
        // clones of one variant (fwd, fwd2)". `fwd` and `fwd2` are wired to
        // differently-shaped callees in `BigComposition` (`fwd` -> `rand`,
        // `fwd2` -> `fwd`), so per story 03's own findings they render as
        // two *different* variants (`Fwd_v1`/`Fwd_v2`), not one variant
        // cloned twice — see story 03's implementation report §2 for the
        // same discrepancy against that story's acceptance text. What does
        // hold, and is what this test checks: two package instances of the
        // `Fwd` package, each getting its own `clone ... as Pkg_<inst>.`.
        let files = load("example-projects/hello-world", "Proof");
        let big = files.iter().find(|f| f.name == "BigComposition").unwrap();
        let clones: Vec<&EcItem> = big
            .file
            .items
            .iter()
            .filter(|item| matches!(item, EcItem::Clone { .. }))
            .collect();
        assert_eq!(clones.len(), 3, "rand, fwd and fwd2 each get one clone");
        let as_names: Vec<&str> = clones
            .iter()
            .map(|c| match c {
                EcItem::Clone { as_name, .. } => as_name.as_str(),
                _ => unreachable!(),
            })
            .collect();
        assert_eq!(as_names, vec!["Pkg_Rand", "Pkg_Fwd", "Pkg_Fwd2"]);
    }

    #[test]
    fn simple_4whs_games_match_golden() {
        let files = load("example-projects/4WHS", "Simple4WHS");
        assert_eq!(
            files.iter().map(|f| f.name.as_str()).collect::<Vec<_>>(),
            vec!["Hybrid0", "Hybrid1", "Hybrid2", "PRF"]
        );
        for f in &files {
            assert_golden(
                f,
                &format!("testdata/easycrypt/story04/4WHS/Comp_{}.ec", f.name),
            );
        }
    }

    #[test]
    fn simple_4whs_games_compile() {
        for name in ["Hybrid0", "Hybrid1", "Hybrid2", "PRF"] {
            assert_compiles(
                "testdata/easycrypt/story04/4WHS",
                &format!("Comp_{name}.ec"),
            );
        }
    }

    #[test]
    fn hybrid0_init_takes_only_the_boolean_const_b() {
        // `n` is used only as a `Bits` width throughout `Hybrid0` (never a
        // module var in `Prot`/`KX`), so it must not become an `init`
        // argument; `prf`/`mac` are `Fn`-typed and never do either. Only the
        // `Boolean` const `b` should survive.
        let files = load("example-projects/4WHS", "Simple4WHS");
        let hybrid0 = files.iter().find(|f| f.name == "Hybrid0").unwrap();
        let EcItem::Module(router) = hybrid0
            .file
            .items
            .iter()
            .find(|i| matches!(i, EcItem::Module(m) if m.name == "Game_Hybrid0"))
            .unwrap()
        else {
            unreachable!()
        };
        let init = router.procs.iter().find(|p| p.name == "init").unwrap();
        assert_eq!(init.args, vec![("b".to_string(), EcType::Bool)]);
    }

    #[test]
    fn rendering_is_deterministic() {
        let a = load("example-projects/4WHS", "Simple4WHS");
        let b = load("example-projects/4WHS", "Simple4WHS");
        for (fa, fb) in a.iter().zip(b.iter()) {
            assert_eq!(render_file(&fa.file), render_file(&fb.file));
        }
    }
}
