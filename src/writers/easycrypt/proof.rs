// SPDX-License-Identifier: MIT OR Apache-2.0

//! Building `Eq_<Left>_<Right>.ec`
//! (`docs/stories/easycrypt/07-proof-skeleton.md`): the equivalence-proof
//! skeleton — lemma, adversary declaration, the invariant `call`, the
//! induction start, and one `admit` per oracle, in the game interface's own
//! export order. Deriving the per-oracle tactics is explicitly out of scope
//! for v1 (the story's own §1): every oracle bullet is exactly `proc;
//! inline. admit.`.
//!
//! [`compute_equivalence_files`] is the entry point story 05's
//! `export::export_theorem` calls: it also drives story 06's
//! `invariant::build_invariant_file`, since both files share one
//! `GameHop::Equivalence` loop and this story owns the orchestration
//! (`docs/stories/easycrypt/06-invariant-translation-IMPLEMENTATION-REPORT.md`
//! §10).

use std::collections::{HashMap, HashSet};

use crate::expressions::{Expression, ExpressionKind};
use crate::gamehops::equivalence::Equivalence;
use crate::identifier::game_ident::GameIdentifier;
use crate::identifier::theorem_ident::TheoremIdentifier;
use crate::identifier::Identifier;
use crate::package::Composition;
use crate::project::Project;
use crate::theorem::{GameInstance, Theorem};

use super::ast::{
    DeclareModule, EcExpr, EcFile, EcItem, EcLemma, EcSection, LemmaBinder, ProofLine, Require,
};
use super::game::composition_const_needs_arg;
use super::interfaces::{self, InterfacesOutput};
use super::invariant::{self, InvariantError, InvariantFile};
use super::names::{NameKind, Names};
use super::package::{self, VariantKey};
use super::render::render_expr;
use super::types::translate_type;
use super::EcExportError;

/// One equivalence hop's rendered proof skeleton, ready for
/// `Eq_<Left>_<Right>.ec`.
pub struct EquivalenceProofFile {
    pub file_name: String,
    pub file: EcFile,
    pub left_name: String,
    pub right_name: String,
    /// Exported oracles this equivalence's game interface covers — one
    /// `admit` bullet each. `admit_count == oracle_count` always in v1.
    pub oracle_count: usize,
    pub admit_count: usize,
    /// Set when `equivalence.trees()` names an oracle set different from
    /// the game interface's own export list (§3: "warn if that set differs
    /// from the game interface's export list") — human-readable, for the
    /// CLI's stdout report. The bullets themselves always follow the
    /// interface's export list regardless, so an oracle is never silently
    /// dropped.
    pub oracle_set_mismatch: Option<String>,
}

/// One equivalence hop's paired output: story 06's invariant file and this
/// story's own proof skeleton.
pub struct EquivalenceFiles {
    pub invariants: InvariantFile,
    pub proof: EquivalenceProofFile,
}

/// Computes every `GameHop::Equivalence`'s paired output for `theorem`, in
/// `theorem.game_hops` order (`GameHop::as_equivalence()` — v1 does not
/// descend into a `GameHop::Hybrid`'s own nested equivalence, matching
/// `export::compute_skipped`'s existing "hybrid game hops are not
/// translated" note). `interfaces` is story 04's already-built
/// `Interfaces.ec` data. The package-variant name map is recomputed once
/// here rather than threaded through, mirroring `game::compute_game_files`'s
/// own established precedent (a cheap, pure function of `theorem`).
pub fn compute_equivalence_files(
    theorem: &Theorem<'_>,
    project: &impl Project,
    interfaces: &InterfacesOutput,
) -> Result<Vec<EquivalenceFiles>, EcExportError> {
    let discovered = package::discover_variants(theorem);
    let mut variant_names = Names::new();
    let variant_name_map = package::assign_names(&discovered, &mut variant_names)?;
    let mut lemma_names = Names::new();

    let mut out = Vec::new();
    for hop in &theorem.game_hops {
        let Some(equivalence) = hop.as_equivalence() else {
            continue;
        };
        let invariants = invariant::build_invariant_file(theorem, equivalence, project)?;
        let proof = build_equivalence_file(
            theorem,
            equivalence,
            interfaces,
            &variant_name_map,
            &mut lemma_names,
        )?;
        out.push(EquivalenceFiles { invariants, proof });
    }
    Ok(out)
}

/// One side's naming layout inside its own `Comp_<mangled>.ec` file (story
/// 10): the composition's own mangled base (`Game_<mangled>`/`Exp_<mangled>`
/// module names derive from this, unprefixed), the *theory* qualifier a
/// `require`r must use to reach into that file (`comp_theory`, `Comp_
/// <mangled>` — story 10 §3.1: only the file/theory name gets the `Comp_`
/// prefix, every module name keeps its old spelling), and — in `comp.pkgs`
/// declaration order — each instance's `Pkg_<InstMangled>` clone-alias base
/// and the package variant name it clones. Recomputed independently per
/// side from `interfaces`/`variant_name_map` rather than threaded out of
/// `game.rs` (which never exposes these internals) — both are pure
/// functions of `comp`, matching story 04's own "recomputed, not threaded
/// through" precedent (its report §3).
struct CompLayout {
    comp_mangled: String,
    comp_theory: String,
    inst_mangled: Vec<String>,
    variant_names: Vec<String>,
}

fn compute_layout(
    comp: &Composition,
    interfaces: &InterfacesOutput,
    variant_name_map: &HashMap<VariantKey, String>,
) -> Result<CompLayout, EcExportError> {
    let comp_mangled = interfaces.comp_mangled[&comp.name].clone();
    let comp_theory = format!("Comp_{comp_mangled}");

    let keys = package::compute_all_keys(comp);
    let variant_names: Vec<String> = keys
        .iter()
        .map(|k| {
            variant_name_map
                .get(k)
                .expect("every key computed here was named by the same discovery compute_package_variants uses")
                .clone()
        })
        .collect();

    // Same registry/order `game.rs::render_game_file` uses for its own
    // `Pkg_<InstMangled>` clone aliases — `comp.pkgs` declaration order, not
    // `ordered_pkgs_idx()` — so restriction/record-literal paths agree with
    // what the actual game file names.
    let mut inst_names = Names::new();
    let mut inst_mangled = Vec::with_capacity(comp.pkgs.len());
    for inst in &comp.pkgs {
        inst_mangled.push(inst_names.mangle(NameKind::Module, inst.name())?);
    }

    Ok(CompLayout {
        comp_mangled,
        comp_theory,
        inst_mangled,
        variant_names,
    })
}

/// `Comp_<mangled>.Game_<mangled>` then
/// `Comp_<mangled>.Pkg_<InstMangled>.<Variant>` per instance, `comp.pkgs`
/// order — every router and every instance clone story 04 gave this
/// composition's own game file (§3: "restrictions must name
/// `Pkg_<InstMangled>` (the clone), never `Inst_<InstMangled>` (the
/// alias)"). The qualifier is `comp_theory` (story 10's `Comp_` prefix,
/// since that's the theory a `require` brings into scope); the module
/// names after it keep their pre-story-10, unprefixed spelling.
fn restrictions_for(layout: &CompLayout) -> Vec<String> {
    let mut out = vec![format!("{}.Game_{}", layout.comp_theory, layout.comp_mangled)];
    for idx in 0..layout.inst_mangled.len() {
        out.push(format!(
            "{}.Pkg_{}.{}",
            layout.comp_theory, layout.inst_mangled[idx], layout.variant_names[idx]
        ));
    }
    out
}

/// Builds one side's flat game-state record literal at the `call` site:
/// one field per `(instance, state field)` in `ordered_pkgs_idx()` order,
/// then one per qualifying package parameter
/// ([`package::param_needs_var`]), then `abort_flag` — the exact same
/// order, namespacing (`{field_ns_prefix}pkg_<instance>_<mangled field>` /
/// `{field_ns_prefix}abort_flag`) and per-instance-fresh [`Names`] mangling
/// `invariant.rs::build_side_record` uses for the record *type*, re-derived
/// independently here rather than shared (`06-invariant-translation-
/// IMPLEMENTATION-REPORT.md` §10: "story 07 builds it inline at the call
/// site ... without needing story 06's own internal lookup map"). Each
/// field's *value* is a memory-tagged module-state read
/// (`Hybrid0.Pkg_KX.KX.d_LTK{1}`), not a record projection — the two
/// translators only share the naming rule, not the expression shape.
fn build_side_record_lit(
    comp: &Composition,
    layout: &CompLayout,
    field_ns_prefix: &str,
    mem: u8,
) -> Result<EcExpr, EcExportError> {
    let mut fields: Vec<(String, EcExpr)> = Vec::new();

    for &idx in &comp.ordered_pkgs_idx() {
        let inst = &comp.pkgs[idx];
        let mut names = Names::new();
        let base_path = vec![
            layout.comp_theory.clone(),
            format!("Pkg_{}", layout.inst_mangled[idx]),
            layout.variant_names[idx].clone(),
        ];

        for (name, _ty, _span) in &inst.pkg.state {
            let mangled = names.mangle(NameKind::Var, name)?;
            let final_name = format!("{field_ns_prefix}pkg_{}_{mangled}", inst.name());
            let mut path = base_path.clone();
            path.push(mangled);
            fields.push((final_name, EcExpr::Qualified { path, mem: Some(mem) }));
        }

        for (name, ty, _span) in &inst.pkg.params {
            if !package::param_needs_var(&inst.pkg, name, ty) {
                continue;
            }
            let mangled = names.mangle(NameKind::Var, name)?;
            let final_name = format!("{field_ns_prefix}pkg_{}_{mangled}", inst.name());
            let mut path = base_path.clone();
            path.push(mangled);
            fields.push((final_name, EcExpr::Qualified { path, mem: Some(mem) }));
        }
    }

    fields.push((
        format!("{field_ns_prefix}abort_flag"),
        EcExpr::Qualified {
            path: vec![
                layout.comp_theory.clone(),
                format!("Game_{}", layout.comp_mangled),
                "abort_flag".to_string(),
            ],
            mem: Some(mem),
        },
    ));

    Ok(EcExpr::RecordLit { fields })
}

/// A composition-level `run` argument's resolved value: a literal (rendered
/// verbatim) or a reference to a theorem constant (rendered as that
/// constant's lemma binder). Mirrors `invariant.rs::ParamValue`, one level
/// up — a *composition's* own const binding rather than a *package
/// instance's* param binding — so it is re-derived rather than shared (same
/// rationale as [`build_side_record_lit`]).
enum RunArgValue {
    Literal(String),
    TheoremConst(String),
}

/// A game instance's composition-const binding is always either a literal
/// or a bare reference to the theorem's own const
/// (`example-projects/4WHS/theorem/Simple4WHS.ssp`'s `params { b: b, ... }`
/// / `params { b: false, ... }`) — never a compound expression, the same
/// invariant `game.rs::references_game_const` relies on one level down.
/// Mirrors `invariant.rs::resolve_expr_value`'s chase.
fn resolve_run_arg(expr: &Expression) -> Option<RunArgValue> {
    match expr.kind() {
        ExpressionKind::BooleanLiteral(s) => Some(RunArgValue::Literal(s.clone())),
        ExpressionKind::IntegerLiteral(i) => Some(RunArgValue::Literal(i.to_string())),
        ExpressionKind::Identifier(Identifier::TheoremIdentifier(TheoremIdentifier::Const(c))) => {
            Some(RunArgValue::TheoremConst(c.name.clone()))
        }
        ExpressionKind::Identifier(Identifier::GameIdentifier(GameIdentifier::Const(c))) => {
            c.assigned_value.as_deref().and_then(resolve_run_arg)
        }
        _ => None,
    }
}

fn literal_text_to_expr(text: &str) -> EcExpr {
    match text {
        "true" => EcExpr::Bool(true),
        "false" => EcExpr::Bool(false),
        other => EcExpr::Int(other.parse().unwrap_or(0)),
    }
}

/// One side's `run` argument list: `comp.consts`, filtered by the exact
/// rule `game.rs`'s own router `init` uses
/// ([`composition_const_needs_arg`]), in `comp.consts` declaration order —
/// so this always matches that composition's `Exp_<mangled>.run`'s real
/// argument list.
fn side_run_args(comp: &Composition, game_inst: &GameInstance) -> Vec<RunArgValue> {
    let mut out = Vec::new();
    for (name, ty) in &comp.consts {
        if !composition_const_needs_arg(comp, name, ty) {
            continue;
        }
        let assigned = game_inst
            .consts
            .iter()
            .find(|(id, _)| &id.name == name)
            .map(|(_, expr)| expr)
            .expect("a game instance binds every one of its composition's declared consts");
        let value = resolve_run_arg(assigned).unwrap_or_else(|| {
            unreachable!(
                "a game instance's composition-const binding must be a literal or a bare \
                 theorem-const reference, found {assigned:?}"
            )
        });
        out.push(value);
    }
    out
}

fn args_to_exprs(values: &[RunArgValue], binder_mangled: &HashMap<String, String>) -> Vec<EcExpr> {
    values
        .iter()
        .map(|v| match v {
            RunArgValue::Literal(text) => literal_text_to_expr(text),
            RunArgValue::TheoremConst(name) => EcExpr::Var(binder_mangled[name].clone()),
        })
        .collect()
}

fn plain_line(text: impl Into<String>) -> ProofLine {
    ProofLine {
        indent: 0,
        bullet: None,
        text: text.into(),
    }
}

fn blank_line() -> ProofLine {
    plain_line(String::new())
}

fn bullet_line(text: impl Into<String>) -> ProofLine {
    ProofLine {
        indent: 0,
        bullet: Some('+'),
        text: text.into(),
    }
}

fn build_equivalence_file(
    theorem: &Theorem<'_>,
    equivalence: &Equivalence,
    interfaces: &InterfacesOutput,
    variant_name_map: &HashMap<VariantKey, String>,
    lemma_names: &mut Names,
) -> Result<EquivalenceProofFile, EcExportError> {
    let left_game_inst = theorem
        .find_game_instance(equivalence.left_name())
        .ok_or_else(|| InvariantError::MissingGameInstance {
            name: equivalence.left_name().to_string(),
        })?;
    let right_game_inst = theorem
        .find_game_instance(equivalence.right_name())
        .ok_or_else(|| InvariantError::MissingGameInstance {
            name: equivalence.right_name().to_string(),
        })?;

    let left_comp = left_game_inst.game();
    let right_comp = right_game_inst.game();
    let span = interfaces::composition_span(left_comp);
    let same_composition = left_comp.name == right_comp.name;

    let left_layout = compute_layout(left_comp, interfaces, variant_name_map)?;
    let right_layout = compute_layout(right_comp, interfaces, variant_name_map)?;

    // --- binders: `&m` then one typed binder per theorem constant either
    // side's run() binds to a constant rather than a literal, in theorem
    // declaration order (§3) -----------------------------------------------
    let left_args = side_run_args(left_comp, left_game_inst);
    let right_args = side_run_args(right_comp, right_game_inst);

    let mut referenced: HashSet<&str> = HashSet::new();
    for v in left_args.iter().chain(right_args.iter()) {
        if let RunArgValue::TheoremConst(name) = v {
            referenced.insert(name.as_str());
        }
    }

    let mut binders = vec![LemmaBinder::Memory("m".to_string())];
    let mut binder_mangled: HashMap<String, String> = HashMap::new();
    let mut binder_names = Names::new();
    for (name, ty) in &theorem.consts {
        if !referenced.contains(name.as_str()) {
            continue;
        }
        let mangled = binder_names.mangle(NameKind::Var, name)?;
        binders.push(LemmaBinder::Typed {
            name: mangled.clone(),
            ty: translate_type(ty, span)?,
        });
        binder_mangled.insert(name.clone(), mangled);
    }

    let left_run_args = args_to_exprs(&left_args, &binder_mangled);
    let right_run_args = args_to_exprs(&right_args, &binder_mangled);

    // --- the lemma statement: Pr[...] = Pr[...] -----------------------
    let left_pr = EcExpr::Pr {
        module: format!("{}.Exp_{}(A)", left_layout.comp_theory, left_layout.comp_mangled),
        proc: "run".to_string(),
        args: left_run_args,
        memory: "m".to_string(),
        event: Box::new(EcExpr::Var("res".to_string())),
    };
    let right_pr = EcExpr::Pr {
        module: format!("{}.Exp_{}(A)", right_layout.comp_theory, right_layout.comp_mangled),
        proc: "run".to_string(),
        args: right_run_args,
        memory: "m".to_string(),
        event: Box::new(EcExpr::Var("res".to_string())),
    };
    let statement = EcExpr::Binop {
        op: super::ast::EcBinop::Eq,
        lhs: Box::new(left_pr),
        rhs: Box::new(right_pr),
    };

    let lemma_name = lemma_names.mangle(
        NameKind::Lemma,
        &format!(
            "{}_{}_equiv",
            left_game_inst.name(),
            right_game_inst.name()
        ),
    )?;

    // --- restrictions: every router and every instance clone of both
    // sides, shared composition listed once (§3) ------------------------
    let mut restrictions = restrictions_for(&left_layout);
    if !same_composition {
        restrictions.extend(restrictions_for(&right_layout));
    }
    let adv_type = format!("Interfaces.{}", interfaces.adv_name[&left_comp.name]);
    let declare = DeclareModule {
        name: "A".to_string(),
        module_type: adv_type,
        restrictions,
    };

    // --- the invariant `call` --------------------------------------------
    let left_record = build_side_record_lit(left_comp, &left_layout, "l_", 1)?;
    let right_record = build_side_record_lit(right_comp, &right_layout, "r_", 2)?;
    let inv_app = EcExpr::App {
        head: "inv".to_string(),
        args: vec![left_record, right_record],
    };

    // --- oracle bullets: the game interface's own export order (§3;
    // load-bearing per story 04's own note) -----------------------------
    let mut proc_names = Names::new();
    let mut proof = vec![
        plain_line("byequiv => //."),
        plain_line("proc; inline."),
        plain_line(format!("call (: {}); last first.", render_expr(&inv_app))),
        blank_line(),
        plain_line("auto => />."),
        plain_line("smt(emptyE map_empty)."),
    ];

    for export in &left_comp.exports {
        let proc_name = proc_names.mangle(NameKind::Proc, export.name())?;
        proof.push(blank_line());
        proof.push(plain_line(format!("(* {proc_name} *)")));
        proof.push(bullet_line("proc; inline. admit."));
    }
    proof.push(plain_line("qed."));

    let oracle_count = left_comp.exports.len();

    // §3: warn (don't silently drop) if the proof trees cover a different
    // oracle set than the interface actually exports. The bullets above
    // always follow the interface's own export list regardless.
    let tree_oracle_names: HashSet<&str> = equivalence
        .trees()
        .iter()
        .map(|(name, _)| name.as_str())
        .collect();
    let export_oracle_names: HashSet<&str> =
        left_comp.exports.iter().map(|e| e.name()).collect();
    let oracle_set_mismatch = if tree_oracle_names == export_oracle_names {
        None
    } else {
        let mut only_trees: Vec<&str> = tree_oracle_names
            .difference(&export_oracle_names)
            .copied()
            .collect();
        only_trees.sort_unstable();
        let mut only_exports: Vec<&str> = export_oracle_names
            .difference(&tree_oracle_names)
            .copied()
            .collect();
        only_exports.sort_unstable();
        Some(format!(
            "{} ~ {}: proof-tree oracle set differs from the game interface's exports \
             (only in proof trees: {}; only in exports: {})",
            left_game_inst.name(),
            right_game_inst.name(),
            if only_trees.is_empty() {
                "none".to_string()
            } else {
                only_trees.join(", ")
            },
            if only_exports.is_empty() {
                "none".to_string()
            } else {
                only_exports.join(", ")
            },
        ))
    };

    let mut items = Vec::new();
    if let Some(warning) = &oracle_set_mismatch {
        items.push(EcItem::Comment(format!(
            "warning: oracle set mismatch — {warning}"
        )));
    }
    items.push(EcItem::Section(EcSection {
        declares: vec![declare],
        items: vec![],
        lemmas: vec![EcLemma {
            name: lemma_name,
            binders,
            statement,
            proof,
        }],
    }));

    let mut comp_requires = vec![left_layout.comp_theory.clone()];
    if !same_composition {
        comp_requires.push(right_layout.comp_theory.clone());
    }
    let invariants_theory = format!(
        "Eq_{}_{}_Invariants",
        left_game_inst.name(),
        right_game_inst.name()
    );

    let file = EcFile {
        header: vec![format!(
            "Eq_{}_{}.ec for theorem `{}` — generated by `domino easycrypt`.",
            left_game_inst.name(),
            right_game_inst.name(),
            theorem.name
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
                    "Interfaces".to_string(),
                ],
            },
            Require {
                import: false,
                names: comp_requires,
            },
            Require {
                import: true,
                names: vec![invariants_theory],
            },
        ],
        items,
    };

    Ok(EquivalenceProofFile {
        file_name: format!(
            "Eq_{}_{}.ec",
            left_game_inst.name(),
            right_game_inst.name()
        ),
        file,
        left_name: left_game_inst.name().to_string(),
        right_name: right_game_inst.name().to_string(),
        oracle_count,
        admit_count: oracle_count,
        oracle_set_mismatch,
    })
}

#[cfg(test)]
mod tests {
    use std::path::{Path, PathBuf};

    use crate::project::{DirectoryFiles, DirectoryProject, Project};
    use crate::transforms::theorem_transforms::EquivalenceTransform;
    use crate::transforms::TheoremTransform;

    use super::super::interfaces::build_interfaces_file;
    use super::super::render::render_file;
    use super::*;

    fn load(dir: &str, theorem_name: &str) -> Vec<EquivalenceFiles> {
        let files: &'static DirectoryFiles =
            Box::leak(Box::new(DirectoryFiles::load(Path::new(dir)).unwrap()));
        let project: &'static DirectoryProject =
            Box::leak(Box::new(DirectoryProject::load(PathBuf::from(dir), files).unwrap()));
        let theorem = project.get_theorem(theorem_name).unwrap();
        let (theorem, _auxs) = EquivalenceTransform.transform_theorem(theorem).unwrap();
        let interfaces = build_interfaces_file(&theorem).unwrap();
        compute_equivalence_files(&theorem, project, &interfaces).unwrap()
    }

    #[test]
    fn simple_4whs_produces_the_three_translated_equivalence_hops() {
        let files = load("example-projects/4WHS", "Simple4WHS");
        let names: Vec<&str> = files.iter().map(|f| f.proof.file_name.as_str()).collect();
        assert_eq!(
            names,
            vec![
                "Eq_Hybrid0_Hybrid1.ec",
                "Eq_Hybrid1_Hybrid2.ec",
                "Eq_Real_Hybrid3_Ideal_Hybrid3.ec",
            ]
        );
    }

    #[test]
    fn hybrid0_hybrid1_bullet_order_matches_export_order() {
        let files = load("example-projects/4WHS", "Simple4WHS");
        let f = &files[0];
        assert_eq!(f.proof.oracle_count, 9);
        assert_eq!(f.proof.admit_count, 9);
        let comments: Vec<&str> = f
            .proof
            .file
            .items
            .iter()
            .find_map(|item| match item {
                EcItem::Section(s) => Some(&s.lemmas[0].proof),
                _ => None,
            })
            .unwrap()
            .iter()
            .filter_map(|l| {
                l.text
                    .strip_prefix("(* ")
                    .and_then(|s| s.strip_suffix(" *)"))
            })
            .collect();
        assert_eq!(
            comments,
            vec![
                "d_NewKey",
                "d_NewSession",
                "d_Send1",
                "d_Send2",
                "d_Send3",
                "d_Send4",
                "d_Send5",
                "d_Reveal",
                "d_Test",
            ]
        );
    }

    #[test]
    fn real_hybrid3_ideal_hybrid3_shares_one_composition_in_restrictions_and_requires() {
        let files = load("example-projects/4WHS", "Simple4WHS");
        let f = files
            .iter()
            .find(|f| f.proof.file_name == "Eq_Real_Hybrid3_Ideal_Hybrid3.ec")
            .unwrap();
        let section = f
            .proof
            .file
            .items
            .iter()
            .find_map(|item| match item {
                EcItem::Section(s) => Some(s),
                _ => None,
            })
            .unwrap();
        // Only one `-Comp_Hybrid2.Game_Hybrid2` restriction, not two.
        let router_restrictions = section.declares[0]
            .restrictions
            .iter()
            .filter(|r| r.ends_with(".Game_Hybrid2"))
            .count();
        assert_eq!(router_restrictions, 1);

        // `require Comp_Hybrid2.` once, not `require Comp_Hybrid2 Comp_Hybrid2.`.
        let comp_require = f
            .proof
            .file
            .requires
            .iter()
            .find(|r| !r.import && r.names.contains(&"Comp_Hybrid2".to_string()))
            .unwrap();
        assert_eq!(comp_require.names, vec!["Comp_Hybrid2".to_string()]);
    }

    #[test]
    fn real_hybrid3_ideal_hybrid3_run_args_are_different_literals() {
        let files = load("example-projects/4WHS", "Simple4WHS");
        let f = files
            .iter()
            .find(|f| f.proof.file_name == "Eq_Real_Hybrid3_Ideal_Hybrid3.ec")
            .unwrap();
        let section = f
            .proof
            .file
            .items
            .iter()
            .find_map(|item| match item {
                EcItem::Section(s) => Some(s),
                _ => None,
            })
            .unwrap();
        let statement = &section.lemmas[0].statement;
        let rendered = render_expr(statement);
        assert!(rendered.contains("run(false, true)"), "{rendered}");
        assert!(rendered.contains("run(true, true)"), "{rendered}");
    }

    #[test]
    fn rendering_is_deterministic() {
        let a = load("example-projects/4WHS", "Simple4WHS");
        let b = load("example-projects/4WHS", "Simple4WHS");
        for (fa, fb) in a.iter().zip(b.iter()) {
            assert_eq!(render_file(&fa.proof.file), render_file(&fb.proof.file));
        }
    }
}
