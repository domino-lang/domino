// SPDX-License-Identifier: MIT OR Apache-2.0

//! Building `Comp_<Comp>.ec` (`docs/stories/easycrypt/04-games-and-router.md`
//! §3.2, file name amended by story 10 §3.1): one file per distinct
//! **composition** — several game instances can share one composition
//! (`theorem.instances` in `Simple4WHS` maps `Real`, `Ideal` and `Hybrid0`
//! all onto the `Hybrid0` composition), so this emits per composition, not
//! per instance, deduplicated by [`interfaces::discover_compositions`].
//!
//! Each file gets (story 14 §3.4 renamed and reshaped all of this): one
//! `clone Pkg_<Variant> as Cloned_Pkg_<inst>.` per package instance (story
//! 03's variants, resolved here via the same [`package::VariantKey`]
//! machinery story 03 uses internally); for an instance with imports, either
//! a direct functor application (when one callee instance already serves
//! the whole import interface unrenamed) or a composition-local
//! `Pkg_Imports_<inst>` adapter that fans the expected oracles out to the
//! instances providing them, followed either way by a `module
//! Pkg_Inst_<inst> = ...` alias — *every* instance gets this name,
//! unconditionally, whether or not it has imports; a router module
//! (`Game_<Comp>`) carrying the single `abort_flag : bool` and one export
//! proc per `comp.exports` entry; and an experiment module (`Exp_<Comp>`)
//! that initialises the router and runs the adversary. Only the *theory*
//! (file) names carry the `Pkg_`/`Comp_` prefix (story 10/14) — every module
//! name, clone alias and functor application keeps its own, unprefixed
//! spelling.

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

/// Whether instance `idx`'s imports can be satisfied by passing a single
/// callee module directly, and which one (story 14 §3.4): `Some(callee)`
/// iff every edge out of `idx` goes to the same `callee` *and* none of them
/// is aliased (`edge.alias().is_none()`, i.e. every import name is already
/// the callee's own oracle name — width subtyping covers a callee with
/// extra procs). `None` otherwise, including when `idx` has no imports at
/// all (that case is handled separately, with no functor argument at all).
fn direct_pass_callee(comp: &Composition, idx: usize) -> Option<usize> {
    let mut callee: Option<usize> = None;
    for edge in comp.edges.iter().filter(|e| e.from() == idx) {
        if edge.alias().is_some() {
            return None;
        }
        match callee {
            None => callee = Some(edge.to()),
            Some(c) if c == edge.to() => {}
            Some(_) => return None,
        }
    }
    callee
}

/// A composition-local import adapter (story 14 §3.4): one stateless proc
/// per `pkg.imports` entry, in declaration order, each forwarding to the
/// instance the matching edge points at under the *callee's* oracle name.
/// Ascribed to the uncloned `Pkg_<Variant>.<Variant>_Imports` (§2.1's second
/// row: matching is structural across the clone boundary), which is what
/// catches a mismatch at `easycrypt compile` time rather than at the
/// application site.
fn build_import_adapter(
    comp: &Composition,
    idx: usize,
    adapter_name: &str,
    variant_name: &str,
    inst_module_name: &[String],
) -> Result<EcItem, EcExportError> {
    let pkg = &comp.pkgs[idx].pkg;

    let mut names = Names::new();
    let mut procs = Vec::new();
    for (sig, ispan) in package::ordered_imports(pkg) {
        let edge = comp
            .edges
            .iter()
            .find(|e| e.from() == idx && e.name() == sig.name)
            .expect(
                "every declared import is wired to exactly one edge \
                 (MissingEdgeForImportedOracleError, composition.rs)",
            );

        let proc_name = names.mangle(NameKind::Proc, &sig.name)?;
        let mut args = Vec::new();
        let mut arg_exprs = Vec::new();
        for (name, ty) in &sig.args {
            let mangled = names.mangle(NameKind::Var, name)?;
            args.push((mangled.clone(), translate_type(ty, *ispan)?));
            arg_exprs.push(EcExpr::Var(mangled));
        }
        let ret_option_ty = EcType::Option(Box::new(translate_type(&sig.ty, *ispan)?));

        // A fresh registry is correct here (not a collision-detection gap):
        // it reproduces the callee's own already-validated `Proc`-namespace
        // mangling of one name, mirroring `package.rs`'s `translate_invoke`
        // and this file's own export-proc call site.
        let callee_proc = Names::new().mangle(NameKind::Proc, &edge.sig().name)?;

        procs.push(EcProc {
            name: proc_name,
            args,
            ret: ret_option_ty.clone(),
            locals: vec![("r".to_string(), ret_option_ty, None)],
            body: EcBlock(vec![EcStmt::Call {
                lhs: Some(EcLvalue::Var("r".to_string())),
                module: inst_module_name[edge.to()].clone(),
                proc: callee_proc,
                args: arg_exprs,
            }]),
            ret_expr: Some(EcExpr::Var("r".to_string())),
        });
    }

    Ok(EcItem::Module(EcModule {
        name: adapter_name.to_string(),
        params: vec![],
        implements: Some(format!("Pkg_{variant_name}.{variant_name}_Imports")),
        vars: vec![],
        procs,
    }))
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

    // One dedicated registry for instance-name mangling (`Cloned_Pkg_<inst>`
    // / `Pkg_Inst_<inst>` / `Pkg_Imports_<inst>` all derive from it) — a
    // fresh, call-scoped `Names` shared across the whole composition,
    // mirroring `package.rs`'s naming precedent, so two differently-named
    // instances that happened to mangle to the same name are caught as a
    // hard collision instead of silently colliding.
    let mut inst_names = Names::new();
    let mut inst_mangled: Vec<String> = Vec::with_capacity(comp.pkgs.len());
    for inst in &comp.pkgs {
        inst_mangled.push(inst_names.mangle(NameKind::Module, &inst.name)?);
    }
    let clone_name: Vec<String> = inst_mangled.iter().map(|m| format!("Cloned_Pkg_{m}")).collect();
    // Every instance gets this name, unconditionally (story 14 §3.4) — the
    // decision that lets every call site, restriction and state path name an
    // instance with no variant-name component.
    let inst_module_name: Vec<String> = inst_mangled.iter().map(|m| format!("Pkg_Inst_{m}")).collect();

    // The theory a package variant renders into is `Pkg_<Variant>.ec` (story
    // 14 §3.6) — the module inside it keeps its own unprefixed name
    // (`variant_names[idx]`), so `clone`'s `base` (the theory being cloned)
    // and the `require` list need the `Pkg_` prefix, but every qualified
    // reference to the resulting module (`Cloned_Pkg_<inst>.<Variant>`) does
    // not, since that resolves through the *local* clone alias, not the
    // theory name.
    let clone_items: Vec<EcItem> = order
        .iter()
        .map(|&idx| EcItem::Clone {
            base: format!("Pkg_{}", variant_names[idx]),
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
    plain_requires.extend(variant_requires.iter().map(|v| format!("Pkg_{v}")));

    // Adapters (if any) and the unconditional `Pkg_Inst_<inst>` alias for
    // every instance, `order` (callees-before-callers) so a callee's own
    // `Pkg_Inst_<callee>` is always already emitted before an adapter or
    // application that names it (§3.4).
    let mut alias_items = Vec::new();
    for &idx in &order {
        let pkg = &comp.pkgs[idx].pkg;
        let clone_module = format!("{}.{}", clone_name[idx], variant_names[idx]);

        if pkg.imports.is_empty() {
            alias_items.push(EcItem::ModuleAlias {
                name: inst_module_name[idx].clone(),
                functor: clone_module,
                args: vec![],
            });
            continue;
        }

        let arg = match direct_pass_callee(comp, idx) {
            Some(callee) => inst_module_name[callee].clone(),
            None => {
                let adapter_name = format!("Pkg_Imports_{}", inst_mangled[idx]);
                let adapter = build_import_adapter(
                    comp,
                    idx,
                    &adapter_name,
                    &variant_names[idx],
                    &inst_module_name,
                )?;
                alias_items.push(adapter);
                adapter_name
            }
        };
        alias_items.push(EcItem::ModuleAlias {
            name: inst_module_name[idx].clone(),
            functor: clone_module,
            args: vec![arg],
        });
    }

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
            module: inst_module_name[idx].clone(),
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
                    module: inst_module_name[export.to()].clone(),
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
        // clones of one variant (fwd, fwd2)" — now literally true (story 14
        // §3.1 dropped `imports` from `VariantKey`, so `fwd` and `fwd2` share
        // one `Fwd` variant despite being wired to differently-shaped
        // callees, `fwd` -> `rand`, `fwd2` -> `fwd`): both get their own
        // `clone Pkg_Fwd as Cloned_Pkg_<inst>.` of that single variant.
        let files = load("example-projects/hello-world", "Proof");
        let big = files.iter().find(|f| f.name == "BigComposition").unwrap();
        let clones: Vec<&EcItem> = big
            .file
            .items
            .iter()
            .filter(|item| matches!(item, EcItem::Clone { .. }))
            .collect();
        assert_eq!(clones.len(), 3, "rand, fwd and fwd2 each get one clone");
        let bases: Vec<&str> = clones
            .iter()
            .map(|c| match c {
                EcItem::Clone { base, .. } => base.as_str(),
                _ => unreachable!(),
            })
            .collect();
        assert_eq!(
            bases,
            vec!["Pkg_Rand", "Pkg_Fwd", "Pkg_Fwd"],
            "fwd and fwd2 both clone the same Pkg_Fwd theory"
        );
        let as_names: Vec<&str> = clones
            .iter()
            .map(|c| match c {
                EcItem::Clone { as_name, .. } => as_name.as_str(),
                _ => unreachable!(),
            })
            .collect();
        assert_eq!(as_names, vec!["Cloned_Pkg_Rand", "Cloned_Pkg_Fwd", "Cloned_Pkg_Fwd2"]);
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

    // --- story 14: import interfaces, adapters, the Pkg_ prefixes ----------

    fn count_pkg_imports_modules(file: &GameFile) -> usize {
        file.file
            .items
            .iter()
            .filter(|item| matches!(item, EcItem::Module(m) if m.name.starts_with("Pkg_Imports_")))
            .count()
    }

    #[test]
    fn hello_world_no_composition_needs_an_adapter() {
        // Every edge in every hello-world composition is unaliased and
        // single-callee (§3.4's direct-pass rule), so no `Pkg_Imports_*`
        // module is ever emitted.
        let files = load("example-projects/hello-world", "Proof");
        for f in &files {
            assert_eq!(
                count_pkg_imports_modules(f),
                0,
                "{} unexpectedly has an import adapter",
                f.name
            );
        }
    }

    #[test]
    fn kem_dem_game_cca_dem_gets_exactly_one_adapter_for_dem() {
        // Acceptance criterion: kem-dem's `Game_CCA_DEM` gets one adapter
        // for `DEM` (`DEM: { DEM_ENC: Scheme_DEM, DEM_DEC: Scheme_DEM, GET:
        // Key }` spans two callees — the story's own motivating multi-callee
        // case, §3.7).
        let files = load("example-projects/kem-dem/kem-dem-cca-ssp", "kem_dem_cca_ssp");
        let f = files.iter().find(|f| f.name == "Game_CCA_DEM").unwrap();
        assert_eq!(count_pkg_imports_modules(f), 1);
        let adapter = f
            .file
            .items
            .iter()
            .find(|item| matches!(item, EcItem::Module(m) if m.name == "Pkg_Imports_DEM"))
            .unwrap();
        let EcItem::Module(m) = adapter else { unreachable!() };
        assert_eq!(m.implements.as_deref(), Some("Pkg_DEM.DEM_Imports"));
    }

    #[test]
    fn hello_world_oracle_rename_new_medium_composition_gets_one_adapter_using_import_names() {
        // §3.3's own worked example: `fwd`'s import names
        // (`ChangeNameUsefulOracle`/`AnotherUsefulOracle`) differ from the
        // callee's oracle name (`UsefulOracle`) it's aliased to, so a direct
        // pass is impossible even though both imports come from the same
        // instance (`rand`) — an adapter is required, and its procs forward
        // to `Pkg_Inst_Rand.d_UsefulOracle`.
        let files = load(
            "example-projects/hello-world-oracle-rename-new",
            "Proof",
        );
        let f = files.iter().find(|f| f.name == "MediumComposition").unwrap();
        assert_eq!(count_pkg_imports_modules(f), 1);
        let adapter = f
            .file
            .items
            .iter()
            .find(|item| matches!(item, EcItem::Module(m) if m.name == "Pkg_Imports_Fwd"))
            .unwrap();
        let EcItem::Module(m) = adapter else { unreachable!() };
        assert_eq!(m.implements.as_deref(), Some("Pkg_Fwd.Fwd_Imports"));
        let proc_names: Vec<&str> = m.procs.iter().map(|p| p.name.as_str()).collect();
        assert_eq!(proc_names, vec!["d_AnotherUsefulOracle", "d_ChangeNameUsefulOracle"]);
        for p in &m.procs {
            let EcStmt::Call { module, proc, .. } = &p.body.0[0] else {
                panic!("expected the adapter proc's first statement to be a call");
            };
            assert_eq!(module, "Pkg_Inst_Rand");
            assert_eq!(proc, "d_UsefulOracle");
        }
    }
}
