// SPDX-License-Identifier: MIT OR Apache-2.0

//! Building `Eq_<Left>_<Right>_Invariants.ec`
//! (`docs/stories/easycrypt/06-invariant-translation.md`): translating an
//! equivalence's hand-written SMT-LIB invariant (`Equivalence::invariants()`)
//! into one state record type per package, a pair of game-state records that
//! nest them (`docs/adr/0007-invariant-game-state-nests-package-state-records.md`,
//! story 42), plus a closed set of EasyCrypt operators, one per
//! `define-fun`/`define-state-relation` in the source file(s), folded into
//! `op inv`.
//!
//! The SMT-LIB text is parsed with the existing `src/util/smtparser`
//! (`smt.pest`) grammar via its `SmtParser` trait; this module supplies its
//! own minimal generic s-expression type ([`Sexp`]) as that trait's
//! `Expr`/`Stmt`, and does the real translation eagerly inside the trait's
//! `handle_definefun`/`handle_define_state_relation` overrides.

use std::collections::{HashMap, HashSet};

use miette::{Diagnostic, SourceSpan};
use thiserror::Error;

use crate::expressions::{Expression, ExpressionKind};
use crate::gamehops::equivalence::Equivalence;
use crate::identifier::game_ident::GameIdentifier;
use crate::identifier::pkg_ident::PackageIdentifier;
use crate::identifier::theorem_ident::TheoremIdentifier;
use crate::identifier::Identifier;
use crate::package::PackageInstance;
use crate::project::Project;
use crate::theorem::{GameInstance, Theorem};
use crate::types::Type;
use crate::util::smtparser::SmtParser;

use super::ast::{
    EcBinop, EcExpr, EcFile, EcItem, EcType, EcUnop, Require,
};
use super::names::{NameError, NameKind, Names};
use super::package;
use super::types::{func_op_name, translate_type};
use super::EcExportError;

/// Errors specific to invariant translation. Folds into [`EcExportError`]
/// via `#[from]` (`mod.rs`), matching [`NameError`]'s own
/// `#[error(transparent)]`-but-not-`#[diagnostic(transparent)]` treatment:
/// none of these carry a source span into Domino source (the failing
/// construct lives in a `.smt2` file, addressed by path, not by
/// [`SourceSpan`]).
#[derive(Debug, Clone, PartialEq, Eq, Error, Diagnostic)]
pub enum InvariantError {
    #[error("failed to read invariant file `{file}`: {message}")]
    Io { file: String, message: String },

    /// A construct this translator doesn't support: an unknown SMT sort, a
    /// malformed `define-fun`/`define-state-relation` shape (wrong arity,
    /// non-atom argument name, …), or a `define-state-relation` whose two
    /// binders are the same name twice. Binder *spelling* is otherwise
    /// unconstrained — `left`/`right`, `state-left`/`state-right`, or
    /// anything else all work, purely positionally.
    #[error("unsupported construct in invariant file `{file}`: {detail}")]
    Unsupported { file: String, detail: String },

    /// An s-expression that isn't one of §3.2's fixed forms and doesn't
    /// name a previously-defined `define-fun`/`define-state-relation` —
    /// acceptance criterion "an unknown atom inside a
    /// `define-state-relation` is a hard error naming the file".
    #[error("unrecognised s-expression in invariant file `{file}`: {sexp}")]
    Unrecognised { file: String, sexp: String },

    /// Two SMT definition names that differ only in `-` vs `_` (or another
    /// escaped punctuation character) both mangle to the same EasyCrypt
    /// operator name.
    #[error(
        "SMT definition names `{a}` and `{b}` in invariant file `{file}` both mangle to `{mangled}`"
    )]
    NameCollision {
        file: String,
        a: String,
        b: String,
        mangled: String,
    },

    #[error("game instance `{name}` not found for this equivalence")]
    MissingGameInstance { name: String },

    /// Two instances of one package in one equivalence whose state fields
    /// translate to different types (different widths), so they cannot
    /// share `<Pkg>_pkgstate` (ADR 0007).
    #[error(
        "package `{package}` is instantiated with different state field types in one equivalence, so its instances cannot share one `{package}_pkgstate` record type"
    )]
    PackageStateMismatch { package: String },

    /// A whole-package equality (`(= left.KX right.KX)`) between instances
    /// of different packages. In Domino the `=` would be ill-sorted.
    #[error(
        "whole-package equality in invariant file `{file}` compares instance `{left_instance}` of package `{left_package}` with instance `{right_instance}` of package `{right_package}`"
    )]
    PackageMismatch {
        file: String,
        left_instance: String,
        left_package: String,
        right_instance: String,
        right_package: String,
    },

    /// A parameter binding that is neither a literal nor, through the
    /// composition's constants, a theorem constant, so `params_inv` cannot
    /// state it.
    #[error(
        "parameter `{param}` of package instance `{instance}` in game instance `{game}` is bound to neither a literal nor a theorem constant"
    )]
    UnresolvedParam {
        game: String,
        instance: String,
        param: String,
    },

    /// Two fields of the record types declared in one invariant file with
    /// one name. Record fields are global in EasyCrypt, and the field names
    /// join package, instance and parameter names with `_`, so for example
    /// instance `T_b1` and parameter `b1` of instance `T` would both give
    /// `l_pkg_T_b1` (story 42 §3.1: a collision is a hard error).
    #[error("two fields of the invariant file's record types are both named `{field}`")]
    FieldCollision { field: String },

    #[error(transparent)]
    Name(#[from] NameError),
}

/// A generic s-expression, this module's own `Expr`/`Stmt` for
/// [`SmtParser`]: atoms carry their raw text (including any of the SMT
/// atom charset's punctuation, `- = < > $ ! + @ . *`), verbatim.
#[derive(Debug, Clone, PartialEq)]
enum Sexp {
    Atom(String),
    List(Vec<Sexp>),
}

impl std::fmt::Display for Sexp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Sexp::Atom(a) => write!(f, "{a}"),
            Sexp::List(items) => {
                write!(f, "(")?;
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{item}")?;
                }
                write!(f, ")")
            }
        }
    }
}

/// One translated invariant file's output: the `<Pkg>_pkgstate` record
/// types, the two game-state records, one `op` per translated
/// `define-fun`/`define-state-relation` (in file order), `params_inv`, and
/// the assembled `inv`.
pub struct InvariantFile {
    pub file_name: String,
    pub file: EcFile,
    pub left_state_type: String,
    pub right_state_type: String,
    /// Human-readable descriptions of every skipped form
    /// (`define-lemma`, `define-game-invariant`, `define-package-invariant`,
    /// a `randomness-mapping-*` `define-fun`), file order — for the CLI's
    /// stdout report, mirroring `export::ExportedTheorem::skipped`
    /// (story 05).
    pub skipped: Vec<String>,
}

/// Build `Eq_<left>_<right>_Invariants.ec` for `equivalence`, reading its
/// invariant file(s) (`Equivalence::invariants()`, in order) via `project`.
pub fn build_invariant_file(
    theorem: &Theorem<'_>,
    equivalence: &Equivalence,
    project: &impl Project,
) -> Result<InvariantFile, EcExportError> {
    let left_game_inst = theorem
        .find_game_instance(equivalence.left_name())
        .ok_or_else(|| {
            InvariantError::MissingGameInstance {
                name: equivalence.left_name().to_string(),
            }
        })?;
    let right_game_inst = theorem
        .find_game_instance(equivalence.right_name())
        .ok_or_else(|| {
            InvariantError::MissingGameInstance {
                name: equivalence.right_name().to_string(),
            }
        })?;

    // §3.1: both sides always get their own field-name namespace prefix
    // (`l_`/`r_`). `abort_flag` alone would otherwise collide between the
    // two records unconditionally (confirmed against real `easycrypt`:
    // two record types in one file cannot share a field name, even when
    // each record's own fields are otherwise disjoint), so this is applied
    // uniformly rather than only "when both sides share a composition" —
    // see the story's own §3.1 note and this story's implementation
    // report for the full argument.
    let mut lookup = StateLookup::default();
    let mut pkg_state_types = Vec::new();
    let left_side = build_side_record(
        left_game_inst,
        "left",
        "l",
        "l_",
        &mut lookup,
        &mut pkg_state_types,
    )?;
    let right_side = build_side_record(
        right_game_inst,
        "right",
        "r",
        "r_",
        &mut lookup,
        &mut pkg_state_types,
    )?;

    check_unique_fields(&pkg_state_types, &left_side, &right_side)?;

    let left_record_ty = EcType::Named(left_side.record_type_name.clone());
    let right_record_ty = EcType::Named(right_side.record_type_name.clone());

    let mut state = InvariantParserState {
        file: String::new(),
        lookup: &lookup,
        left_record_ty: left_record_ty.clone(),
        right_record_ty: right_record_ty.clone(),
        theorem_consts: &theorem.consts,
        ops: OpRegistry::default(),
        items: Vec::new(),
        state_relations: Vec::new(),
        skipped: Vec::new(),
    };

    for file_name in equivalence.invariants() {
        state.file = file_name.clone();
        let contents = project
            .read_input_file(file_name)
            .map_err(|err| InvariantError::Io {
                file: file_name.clone(),
                message: err.to_string(),
            })?;
        state.parse_stmts(&contents)?;
    }

    let params_inv_expr = build_params_inv(&left_side, &right_side)?;

    let mut items: Vec<EcItem> = pkg_state_types
        .into_iter()
        .map(|t| EcItem::Record {
            name: t.name,
            fields: t.fields,
        })
        .collect();
    items.push(EcItem::Record {
        name: left_side.record_type_name.clone(),
        fields: left_side.fields.clone(),
    });
    items.push(EcItem::Record {
        name: right_side.record_type_name.clone(),
        fields: right_side.fields.clone(),
    });
    items.extend(state.items);

    items.push(EcItem::OpDef {
        name: "params_inv".to_string(),
        args: vec![
            ("l".to_string(), left_record_ty.clone()),
            ("r".to_string(), right_record_ty.clone()),
        ],
        ret: Some(EcType::Bool),
        body: params_inv_expr,
    });

    let abort_eq = eq_expr(
        field_expr("l", &left_side.abort_field),
        field_expr("r", &right_side.abort_field),
    );

    let state_relation_conj = fold_and(
        state
            .state_relations
            .iter()
            .map(|name| EcExpr::App {
                head: name.clone(),
                args: vec![EcExpr::Var("l".to_string()), EcExpr::Var("r".to_string())],
            })
            .collect(),
    );

    let guarded = EcExpr::Binop {
        op: EcBinop::Implies,
        lhs: Box::new(EcExpr::Unop {
            op: EcUnop::Not,
            arg: Box::new(field_expr("l", &left_side.abort_field)),
        }),
        rhs: Box::new(state_relation_conj),
    };

    let inv_body = fold_and(vec![
        EcExpr::App {
            head: "params_inv".to_string(),
            args: vec![EcExpr::Var("l".to_string()), EcExpr::Var("r".to_string())],
        },
        abort_eq,
        guarded,
    ]);

    items.push(EcItem::OpDef {
        name: "inv".to_string(),
        args: vec![
            ("l".to_string(), left_record_ty),
            ("r".to_string(), right_record_ty),
        ],
        ret: Some(EcType::Bool),
        body: inv_body,
    });

    let file = EcFile {
        header: vec![format!(
            "generated by domino: invariant for {} ~ {}",
            left_game_inst.name(),
            right_game_inst.name()
        )],
        requires: vec![Require {
            import: true,
            names: vec![
                "AllCore".to_string(),
                "Distr".to_string(),
                "FMap".to_string(),
                "Int".to_string(),
                "IntDiv".to_string(),
                "Types".to_string(),
            ],
        }],
        items,
    };

    Ok(InvariantFile {
        file_name: format!(
            "Eq_{}_{}_Invariants.ec",
            left_game_inst.name(),
            right_game_inst.name()
        ),
        file,
        left_state_type: left_side.record_type_name,
        right_state_type: right_side.record_type_name,
        skipped: state.skipped,
    })
}

impl From<crate::util::smtparser::Error> for InvariantError {
    fn from(e: crate::util::smtparser::Error) -> Self {
        InvariantError::Unsupported {
            file: String::new(),
            detail: format!("could not parse SMT-LIB: {e}"),
        }
    }
}

// --- the record types (story 06 §3.1, story 42 §3.1–§3.2) ---------------

/// The record type holding one package's state fields:
/// `<Pkg>_pkgstate`. Shared by every instance of the package on either
/// side of the equivalence, and declared only in the invariant file.
pub(super) fn pkg_state_type_name(package: &str) -> String {
    format!("{package}_pkgstate")
}

/// A field of [`pkg_state_type_name`]: `<Pkg>_<mangled state field>`.
/// Record fields are global in EasyCrypt, and two packages may both have a
/// `State`, hence the package prefix.
pub(super) fn pkg_state_field_name(package: &str, mangled_field: &str) -> String {
    format!("{package}_{mangled_field}")
}

/// The game-record field holding one instance's package record:
/// `{l_|r_}pkg_<Inst>`.
pub(super) fn instance_field_name(field_ns_prefix: &str, instance: &str) -> String {
    format!("{field_ns_prefix}pkg_{instance}")
}

/// The game-record field holding the game's abort flag: `{l_|r_}abort_flag`.
pub(super) fn abort_field_name(field_ns_prefix: &str) -> String {
    format!("{field_ns_prefix}abort_flag")
}

/// The game-record field holding one parameter that becomes a module
/// variable ([`package::param_needs_var`]): `{l_|r_}pkg_<Inst>_<mangled param>`.
pub(super) fn param_field_name(field_ns_prefix: &str, instance: &str, mangled_param: &str) -> String {
    format!("{field_ns_prefix}pkg_{instance}_{mangled_param}")
}

/// One `<Pkg>_pkgstate` record type.
#[derive(Debug, Clone, PartialEq)]
struct PkgStateType {
    package: String,
    name: String,
    fields: Vec<(String, EcType)>,
}

/// What a `.smt2` dotted atom can resolve to, for both sides.
#[derive(Default)]
struct StateLookup {
    /// `{left|right}.<Inst>.<raw state field or parameter>` -> the
    /// projection that reads it (``l.`l_pkg_KX.`KX_d_State``,
    /// ``l.`l_pkg_KX_b``) and its type.
    fields: HashMap<String, (EcExpr, EcType)>,
    /// `{left|right}.<Inst>` -> that instance, for a whole-package equality.
    instances: HashMap<String, InstanceEntry>,
}

struct InstanceEntry {
    instance: String,
    package: String,
    /// ``l.`l_pkg_<Inst>``, or `None` for an instance without state.
    state: Option<EcExpr>,
}

/// One parameter field of a game record, with what the instance binds it to.
struct ParamField<'a> {
    instance: String,
    param: String,
    field: EcExpr,
    binding: Option<&'a Expression>,
}

struct SideRecord<'a> {
    game_name: String,
    record_type_name: String,
    fields: Vec<(String, EcType)>,
    /// Every parameter field, in record order (§3.4).
    param_fields: Vec<ParamField<'a>>,
    abort_field: String,
}

/// Adds `package`'s record type to `types`, or checks that the one already
/// there (from another instance of the package) has the same fields.
fn register_pkg_state_type(
    types: &mut Vec<PkgStateType>,
    package: &str,
    fields: Vec<(String, EcType)>,
) -> Result<(), InvariantError> {
    match types.iter().find(|t| t.package == package) {
        Some(existing) if existing.fields == fields => Ok(()),
        Some(_) => Err(InvariantError::PackageStateMismatch {
            package: package.to_string(),
        }),
        None => {
            types.push(PkgStateType {
                package: package.to_string(),
                name: pkg_state_type_name(package),
                fields,
            });
            Ok(())
        }
    }
}

/// The record for `game_inst`'s side of the equivalence (story 42 §3.2):
/// one field `{field_ns_prefix}pkg_<Inst> : <Pkg>_pkgstate` per instance
/// with state, then one field per parameter that becomes a module variable
/// ([`package::param_needs_var`]), both in `ordered_pkgs_idx()` order, then
/// `abort_flag`. Each package with state gets its `<Pkg>_pkgstate` type in
/// `pkg_state_types`. State fields and parameters are mangled per instance
/// through one [`Names`], as the package's own module variables are.
///
/// `lookup` gets `{binder}.<Inst>.<raw name>` for every state field and
/// parameter, and `{binder}.<Inst>` for every instance.
fn build_side_record<'a>(
    game_inst: &'a GameInstance,
    binder: &str,
    op_param: &str,
    field_ns_prefix: &str,
    lookup: &mut StateLookup,
    pkg_state_types: &mut Vec<PkgStateType>,
) -> Result<SideRecord<'a>, EcExportError> {
    let mut instance_fields = Vec::new();
    let mut param_decls = Vec::new();
    let mut param_fields = Vec::new();

    for &idx in &game_inst.game().ordered_pkgs_idx() {
        let inst: &PackageInstance = &game_inst.game().pkgs[idx];
        let package = inst.pkg.name.as_str();
        let mut names = Names::new();

        let mut state_fields = Vec::with_capacity(inst.pkg.state.len());
        for (name, ty, span) in &inst.pkg.state {
            let mangled = names.mangle(NameKind::Var, name)?;
            let ec_ty = translate_type(ty, *span)?;
            state_fields.push((name, pkg_state_field_name(package, &mangled), ec_ty));
        }

        let state = if state_fields.is_empty() {
            None
        } else {
            let inst_field = instance_field_name(field_ns_prefix, inst.name());
            let inst_expr = field_expr(op_param, &inst_field);
            for (raw, field, ty) in &state_fields {
                let projection = EcExpr::Field {
                    expr: Box::new(inst_expr.clone()),
                    field: field.clone(),
                };
                lookup.fields.insert(
                    format!("{binder}.{}.{raw}", inst.name()),
                    (projection, ty.clone()),
                );
            }
            register_pkg_state_type(
                pkg_state_types,
                package,
                state_fields
                    .into_iter()
                    .map(|(_, field, ty)| (field, ty))
                    .collect(),
            )?;
            instance_fields.push((inst_field, EcType::Named(pkg_state_type_name(package))));
            Some(inst_expr)
        };
        lookup.instances.insert(
            format!("{binder}.{}", inst.name()),
            InstanceEntry {
                instance: inst.name().to_string(),
                package: package.to_string(),
                state,
            },
        );

        for (name, ty, span) in &inst.pkg.params {
            if !package::param_needs_var(&inst.pkg, name, ty) {
                continue;
            }
            let mangled = names.mangle(NameKind::Var, name)?;
            let ec_ty = translate_type(ty, *span)?;
            let field = param_field_name(field_ns_prefix, inst.name(), &mangled);
            let projection = field_expr(op_param, &field);
            lookup.fields.insert(
                format!("{binder}.{}.{name}", inst.name()),
                (projection.clone(), ec_ty.clone()),
            );
            param_decls.push((field, ec_ty));
            param_fields.push(ParamField {
                instance: inst.name().to_string(),
                param: name.clone(),
                field: projection,
                binding: param_assignment(inst, name),
            });
        }
    }

    let abort_field = abort_field_name(field_ns_prefix);
    let mut fields = instance_fields;
    fields.extend(param_decls);
    fields.push((abort_field.clone(), EcType::Bool));

    Ok(SideRecord {
        game_name: game_inst.name().to_string(),
        record_type_name: format!("{}_state", game_inst.name()),
        fields,
        param_fields,
        abort_field,
    })
}

/// Checks that no two fields of the file's record types (every
/// `<Pkg>_pkgstate`, then both game records) share a name, as EasyCrypt
/// record fields are global.
fn check_unique_fields(
    pkg_state_types: &[PkgStateType],
    left: &SideRecord<'_>,
    right: &SideRecord<'_>,
) -> Result<(), InvariantError> {
    let mut seen = HashSet::new();
    let all_fields = pkg_state_types
        .iter()
        .flat_map(|t| &t.fields)
        .chain(&left.fields)
        .chain(&right.fields);
    for (field, _) in all_fields {
        if !seen.insert(field.as_str()) {
            return Err(InvariantError::FieldCollision {
                field: field.clone(),
            });
        }
    }
    Ok(())
}

/// Mangles a newly-introduced local binder (a quantifier binder, a `let`
/// binding, or a `define-fun` argument), escaping it further if it would
/// otherwise land on `l`/`r` — the fixed, unmangled names every translated
/// body already uses (unconditionally, outside `locals`/`local_names`
/// entirely) for the equivalence's own left/right record parameters
/// (`translate_atom`'s `"left"`/`"right"` cases). Without this, a `.smt2`
/// source binder that happens to be literally named `r` (or `l`) would
/// silently *shadow* the record parameter in the rendered EasyCrypt text —
/// real, not hypothetical: `kem-dem-cca-ssp`'s own invariant has `(exists
/// ((r Bits_kgenr)) (... (maybe-get right.KEM.pk) ...))`, where the
/// existential `r` collided with `right`'s own record parameter and broke
/// every dotted-field projection inside its body (`unknown record
/// projection`, caught only by actually compiling the output — nothing
/// here would have caught it structurally). Escaping through the same
/// [`Names`] registry (not a bespoke rename) keeps a *second* genuine
/// occurrence of the same raw name idempotent and a different raw name
/// that also collides a hard [`NameError`], exactly like every other
/// mangling in this crate.
fn mangle_local_binder(names: &mut Names, raw: &str) -> Result<String, NameError> {
    let mangled = names.mangle(NameKind::Var, raw)?;
    if mangled == "l" || mangled == "r" {
        return names.mangle(NameKind::Var, &format!("q_{raw}"));
    }
    Ok(mangled)
}

/// Whether `e` contains a reference to the (already-mangled) variable
/// `name` anywhere in its tree. Used by `translate_let` to drop a `let`
/// binding the body never uses. Conservative around shadowing: a nested
/// `Let`/`Quant` that rebinds `name` still counts as a "use" here, since
/// this translator's `Names` mangling never reuses a mangled name within
/// one file, so no such shadowing is ever actually produced — treating it
/// as a use anyway is simply the safe default if that ever changed.
fn expr_references_var(e: &EcExpr, name: &str) -> bool {
    match e {
        EcExpr::Var(v) => v == name,
        EcExpr::Qualified { .. } | EcExpr::Int(_) | EcExpr::Bool(_) | EcExpr::Unit => false,
        EcExpr::None_(_) | EcExpr::MapEmpty => false,
        EcExpr::Tuple(items) => items.iter().any(|it| expr_references_var(it, name)),
        EcExpr::Proj { expr, .. } | EcExpr::Field { expr, .. } => expr_references_var(expr, name),
        EcExpr::RecordLit { fields } => fields.iter().any(|(_, v)| expr_references_var(v, name)),
        EcExpr::Some_(inner) | EcExpr::Oget(inner) => expr_references_var(inner, name),
        EcExpr::MapGet { map, key } => {
            expr_references_var(map, name) || expr_references_var(key, name)
        }
        EcExpr::MapSet { map, key, value } => {
            expr_references_var(map, name)
                || expr_references_var(key, name)
                || expr_references_var(value, name)
        }
        EcExpr::MapRem { map, key } => {
            expr_references_var(map, name) || expr_references_var(key, name)
        }
        EcExpr::App { args, .. } => args.iter().any(|a| expr_references_var(a, name)),
        EcExpr::Unop { arg, .. } => expr_references_var(arg, name),
        EcExpr::Binop { lhs, rhs, .. } => {
            expr_references_var(lhs, name) || expr_references_var(rhs, name)
        }
        EcExpr::If {
            cond,
            then_expr,
            else_expr,
        } => {
            expr_references_var(cond, name)
                || expr_references_var(then_expr, name)
                || expr_references_var(else_expr, name)
        }
        EcExpr::Let { value, body, .. } => {
            expr_references_var(value, name) || expr_references_var(body, name)
        }
        EcExpr::Quant { body, .. } => expr_references_var(body, name),
        EcExpr::Pr { args, event, .. } => {
            args.iter().any(|a| expr_references_var(a, name)) || expr_references_var(event, name)
        }
        // `={glob M}` names a module, never one of this translator's own
        // local variables.
        EcExpr::GlobEq(_) => false,
    }
}

fn field_expr(op_param: &str, field: &str) -> EcExpr {
    EcExpr::Field {
        expr: Box::new(EcExpr::Var(op_param.to_string())),
        field: field.to_string(),
    }
}

/// Recognises a `.smt2` bits-literal atom emitted by
/// `src/writers/smt/expr_expr.rs`/`expr_term.rs`'s own `From<&Expression>
/// for SmtExpr` (`ExpressionKind::BitsLiteral`'s SMT-text form, used
/// verbatim in Domino's own solver-facing output and, as `Full4WHS` shows,
/// also written by hand into invariant files): `<empty-bitstring>` for
/// `Bits(*)`'s zero value, or `<{"0"|"1"}_{suffix}>` for a fixed-width
/// `Bits(n)`'s zero/one value (`<0_n>`, `<1_256>`, …) — `{suffix}` is the
/// width's raw identifier text, exactly as `CountSpec::resolved_suffix`
/// produces it (no `-` -> `_` mangling at that layer). Maps onto the same
/// `zero`/`one`/`zero_<suffix>`/`one_<suffix>` ops `Types.ec` always
/// declares for every bits type in scope (`typesfile.rs::bits_type_items`)
/// and that `types.rs::translate_bits_literal` already produces for
/// Domino-source `BitsLiteral` expressions — this is the same mapping,
/// just reached from parsed SMT text instead of a `Type`/`Expression`, so
/// the suffix is mangled the same way (`bits_suffix`'s own `-` -> `_`) to
/// land on the identical op/type names.
fn translate_bits_literal_atom(a: &str) -> Option<(EcExpr, EcType)> {
    let inner = a.strip_prefix('<')?.strip_suffix('>')?;
    if inner == "empty-bitstring" {
        return Some((EcExpr::Var("zero".to_string()), EcType::Named("bits".to_string())));
    }
    let (content, raw_suffix) = inner.split_once('_')?;
    let suffix = raw_suffix.replace('-', "_");
    let op = match content {
        "0" => format!("zero_{suffix}"),
        "1" => format!("one_{suffix}"),
        _ => return None,
    };
    Some((EcExpr::Var(op), EcType::Named(format!("bits_{suffix}"))))
}

fn eq_expr(lhs: EcExpr, rhs: EcExpr) -> EcExpr {
    EcExpr::Binop {
        op: EcBinop::Eq,
        lhs: Box::new(lhs),
        rhs: Box::new(rhs),
    }
}

/// One flat, right-nested `/\` chain ([`EcExpr::right_chain`]), and `true`
/// for no conjuncts. Conjuncts keep their order.
fn fold_and(exprs: Vec<EcExpr>) -> EcExpr {
    EcExpr::right_chain(EcBinop::And, exprs).unwrap_or(EcExpr::Bool(true))
}

// --- `params_inv` (§3.3) ----------------------------------------------

enum ParamValue {
    TheoremConst(String),
    /// The literal's own SMT-LIB text (`"true"`/`"false"`, or an integer).
    Literal(String),
}

/// A package instance's param binding is always either a literal or a
/// bare reference to the enclosing composition's own const
/// (`game.rs::references_game_const`'s established invariant); a
/// composition const is in turn always either a literal or a bare
/// reference to a theorem const. `Identifier::GameIdentifier(Const)`'s own
/// `assigned_value` (resp. `PackageIdentifier(Const)`'s `game_assignment`)
/// already carries that next link, populated during game-instance
/// instantiation — this just walks it to the end.
fn resolve_expr_value(expr: &Expression) -> Option<ParamValue> {
    match expr.kind() {
        ExpressionKind::BooleanLiteral(s) => Some(ParamValue::Literal(s.clone())),
        ExpressionKind::IntegerLiteral(i) => Some(ParamValue::Literal(i.to_string())),
        ExpressionKind::Identifier(Identifier::TheoremIdentifier(TheoremIdentifier::Const(c))) => {
            Some(ParamValue::TheoremConst(c.name.clone()))
        }
        ExpressionKind::Identifier(Identifier::GameIdentifier(GameIdentifier::Const(c))) => {
            c.assigned_value.as_deref().and_then(resolve_expr_value)
        }
        ExpressionKind::Identifier(Identifier::PackageIdentifier(PackageIdentifier::Const(c))) => {
            c.game_assignment.as_deref().and_then(resolve_expr_value)
        }
        _ => None,
    }
}

fn param_assignment<'a>(inst: &'a PackageInstance, name: &str) -> Option<&'a Expression> {
    inst.params
        .iter()
        .find(|(id, _)| id.name == name)
        .map(|(_, e)| e)
}

fn literal_expr(text: &str) -> EcExpr {
    match text {
        "true" => EcExpr::Bool(true),
        "false" => EcExpr::Bool(false),
        other => EcExpr::Int(other.parse().unwrap_or(0)),
    }
}

/// Story 42 §3.4: states every parameter field of both game records by what
/// it is bound to, never by instance or parameter name. Fields are taken in
/// record order, the left record's first. A field bound to a literal is
/// pinned to it. Each field bound to a theorem constant after the first one
/// is equated with the previous field bound to that constant, on either
/// side. The only field bound to a constant contributes nothing, since it
/// holds for every value of the constant. A binding that resolves to
/// neither is a hard [`InvariantError::UnresolvedParam`].
fn build_params_inv(left: &SideRecord, right: &SideRecord) -> Result<EcExpr, InvariantError> {
    let mut conjuncts = Vec::new();
    let mut last_bound_to: HashMap<String, &EcExpr> = HashMap::new();

    let sides = [left, right];
    let fields = sides
        .iter()
        .flat_map(|side| side.param_fields.iter().map(move |f| (side, f)));
    for (side, param) in fields {
        let value = param.binding.and_then(resolve_expr_value).ok_or_else(|| {
            InvariantError::UnresolvedParam {
                game: side.game_name.clone(),
                instance: param.instance.clone(),
                param: param.param.clone(),
            }
        })?;
        match value {
            ParamValue::Literal(lit) => {
                conjuncts.push(eq_expr(param.field.clone(), literal_expr(&lit)));
            }
            ParamValue::TheoremConst(name) => {
                if let Some(previous) = last_bound_to.insert(name, &param.field) {
                    conjuncts.push(eq_expr(previous.clone(), param.field.clone()));
                }
            }
        }
    }

    Ok(fold_and(conjuncts))
}

// --- the SMT-definition-name -> `Domino_<name>` op registry -----------

/// Maps a `define-fun`/`define-state-relation`'s raw SMT name to its
/// mangled `Domino_<name>` op name and declared return type, catching a
/// hard collision (two different raw names mangling to the same result —
/// e.g. `no-overwriting-state` and `no_overwriting_state`) the same way
/// [`Names::mangle`] does, but over this module's own richer character
/// mangling ([`mangle_smt_def_name`]) rather than [`Names`]'s bare
/// `-` -> `_` substitution.
#[derive(Default)]
struct OpRegistry {
    by_raw: HashMap<String, (String, EcType)>,
    seen_mangled: HashMap<String, String>,
}

impl OpRegistry {
    fn define(&mut self, file: &str, raw: &str, ret: EcType) -> Result<String, InvariantError> {
        let mangled = format!("Domino_{}", mangle_smt_def_name(raw));
        match self.seen_mangled.get(&mangled) {
            Some(existing) if existing == raw => {}
            Some(existing) => {
                return Err(InvariantError::NameCollision {
                    file: file.to_string(),
                    a: existing.clone(),
                    b: raw.to_string(),
                    mangled,
                })
            }
            None => {
                self.seen_mangled.insert(mangled.clone(), raw.to_string());
            }
        }
        self.by_raw.insert(raw.to_string(), (mangled.clone(), ret));
        Ok(mangled)
    }

    fn lookup(&self, raw: &str) -> Option<&(String, EcType)> {
        self.by_raw.get(raw)
    }
}

/// Mangles an SMT-LIB definition name into a legal (partial) EasyCrypt
/// identifier fragment: `-` becomes `_` (unchanged from before this
/// story); every other punctuation character the `smt.pest` atom charset
/// allows (`= < > $ ! + @ . *`) becomes an underscore-delimited word
/// (`state=` -> `state_eq`, `=prf` -> `eq_prf`), so the result is always a
/// legal EasyCrypt identifier fragment once prefixed with `Domino_`.
fn mangle_smt_def_name(raw: &str) -> String {
    let mut out = String::new();
    for c in raw.chars() {
        match c {
            'a'..='z' | 'A'..='Z' | '0'..='9' | '_' => out.push(c),
            '-' => out.push('_'),
            '=' => out.push_str("_eq_"),
            '<' => out.push_str("_lt_"),
            '>' => out.push_str("_gt_"),
            '!' => out.push_str("_not_"),
            '+' => out.push_str("_plus_"),
            '@' => out.push_str("_at_"),
            '.' => out.push_str("_dot_"),
            '*' => out.push_str("_star_"),
            '$' => out.push_str("_dollar_"),
            _ => out.push('_'),
        }
    }

    let mut collapsed = String::new();
    let mut prev_underscore = false;
    for c in out.chars() {
        if c == '_' {
            if !prev_underscore {
                collapsed.push('_');
            }
            prev_underscore = true;
        } else {
            collapsed.push(c);
            prev_underscore = false;
        }
    }
    collapsed.trim_matches('_').to_string()
}

// --- SMT sort text -> EcType --------------------------------------------

/// Tokenizes then parses a raw SMT-LIB sort string (as handed over
/// verbatim by `smtparser::implementation::SmtParser::rule_stmt`'s `defun`
/// arm, `p.next().unwrap().as_str()` on the grammar's `ty` rule) into a
/// [`Sexp`]. Sort text only ever uses the plain-identifier subset of the
/// atom charset (no `smt.pest` special characters), so a whitespace/paren
/// tokenizer is sufficient — this does not reuse the pest grammar itself.
fn parse_sort_text(s: &str) -> Sexp {
    let mut tokens = Vec::new();
    let mut cur = String::new();
    for c in s.chars() {
        match c {
            '(' | ')' => {
                if !cur.is_empty() {
                    tokens.push(std::mem::take(&mut cur));
                }
                tokens.push(c.to_string());
            }
            c if c.is_whitespace() => {
                if !cur.is_empty() {
                    tokens.push(std::mem::take(&mut cur));
                }
            }
            _ => cur.push(c),
        }
    }
    if !cur.is_empty() {
        tokens.push(cur);
    }

    let mut pos = 0;
    parse_sort_tokens(&tokens, &mut pos)
}

fn parse_sort_tokens(tokens: &[String], pos: &mut usize) -> Sexp {
    if tokens.get(*pos).map(String::as_str) == Some("(") {
        *pos += 1;
        let mut items = Vec::new();
        while tokens.get(*pos).map(String::as_str) != Some(")") {
            items.push(parse_sort_tokens(tokens, pos));
        }
        *pos += 1;
        Sexp::List(items)
    } else {
        let t = tokens.get(*pos).cloned().unwrap_or_default();
        *pos += 1;
        Sexp::Atom(t)
    }
}

/// §3.2's sort row: `Int`/`Bool` literally, `Bits_<suffix>` ->
/// `bits_<suffix>` (lowercasing only the leading `B`, mirroring
/// `types::bits_type_name`'s own naming), `(Maybe T)` -> `T option`,
/// `(TupleN …)` -> an N-tuple, `(Array K V)` -> `(K, V') fmap` where `V'`
/// is `V` with one outer `Maybe` layer peeled — Domino's own SMT writer
/// always wraps a table's value sort in `Maybe` to model an absent cell
/// (an SMT `Array` is total), whereas EasyCrypt's `fmap` already models
/// absence via `.[k]`'s own `option` return, so the two "one optionality
/// layer" encodings only agree once this layer is peeled here (confirmed
/// against `Package::state`'s own Domino-`Type` translation, which
/// likewise never adds a second `option` layer for a `Table`'s value
/// type).
fn translate_sort(s: &Sexp, file: &str) -> Result<EcType, InvariantError> {
    match s {
        Sexp::Atom(a) => match a.as_str() {
            "Int" => Ok(EcType::Int),
            "Bool" => Ok(EcType::Bool),
            _ if a.starts_with("Bits") => Ok(EcType::Named(format!("bits{}", &a[4..]))),
            other => Err(InvariantError::Unsupported {
                file: file.to_string(),
                detail: format!("unsupported SMT sort `{other}`"),
            }),
        },
        Sexp::List(items) => {
            let Some(Sexp::Atom(head)) = items.first() else {
                return Err(InvariantError::Unsupported {
                    file: file.to_string(),
                    detail: format!("malformed sort `{s}`"),
                });
            };
            match head.as_str() {
                "Maybe" if items.len() == 2 => {
                    Ok(EcType::Option(Box::new(translate_sort(&items[1], file)?)))
                }
                "Array" if items.len() == 3 => {
                    let key = translate_sort(&items[1], file)?;
                    let value = strip_maybe_and_translate(&items[2], file)?;
                    Ok(EcType::Fmap(Box::new(key), Box::new(value)))
                }
                h if h.starts_with("Tuple") => {
                    let n: usize = h[5..].parse().map_err(|_| InvariantError::Unsupported {
                        file: file.to_string(),
                        detail: format!("malformed tuple sort `{s}`"),
                    })?;
                    let comps = items[1..]
                        .iter()
                        .map(|i| translate_sort(i, file))
                        .collect::<Result<Vec<_>, _>>()?;
                    if comps.len() != n {
                        return Err(InvariantError::Unsupported {
                            file: file.to_string(),
                            detail: format!("`{h}` sort with {} components", comps.len()),
                        });
                    }
                    Ok(EcType::Tuple(comps))
                }
                other => Err(InvariantError::Unsupported {
                    file: file.to_string(),
                    detail: format!("unsupported SMT sort `{other}` in `{s}`"),
                }),
            }
        }
    }
}

fn strip_maybe_and_translate(s: &Sexp, file: &str) -> Result<EcType, InvariantError> {
    if let Sexp::List(items) = s {
        if let [Sexp::Atom(head), inner] = &items[..] {
            if head == "Maybe" {
                return translate_sort(inner, file);
            }
        }
    }
    translate_sort(s, file)
}

// --- expression translation (§3.2) --------------------------------------

/// Per-top-level-definition translation state: `locals` (passed
/// explicitly, extended by cloning on entering a `forall`/`exists`/`let`
/// scope) carries every bound name (defun arg, quantifier binder, `let`
/// binding) visible at the current point, mangled once via `local_names`
/// (shared for the definition's whole body, so a name reused at two
/// non-overlapping points, e.g. two sibling `let`s both naming `state`,
/// mangles identically — normal shadowing — while two *different* raw
/// names colliding after mangling is `local_names`' own hard error).
struct TCtx<'a> {
    file: String,
    lookup: &'a StateLookup,
    left_record_ty: EcType,
    right_record_ty: EcType,
    theorem_consts: &'a [(String, Type)],
    ops: &'a OpRegistry,
    local_names: Names,
}

type Locals = HashMap<String, (String, EcType)>;

impl<'a> TCtx<'a> {
    fn unsupported(&self, detail: impl Into<String>) -> InvariantError {
        InvariantError::Unsupported {
            file: self.file.clone(),
            detail: detail.into(),
        }
    }

    fn unrecognised(&self, s: &Sexp) -> InvariantError {
        InvariantError::Unrecognised {
            file: self.file.clone(),
            sexp: s.to_string(),
        }
    }

    fn translate(&mut self, s: &Sexp, locals: &Locals) -> Result<(EcExpr, EcType), InvariantError> {
        match s {
            Sexp::Atom(a) => self.translate_atom(a, locals, s),
            Sexp::List(items) => self.translate_list(items, locals, s),
        }
    }

    fn translate_atom(
        &self,
        a: &str,
        locals: &Locals,
        whole: &Sexp,
    ) -> Result<(EcExpr, EcType), InvariantError> {
        if let Some((mangled, ty)) = locals.get(a) {
            return Ok((EcExpr::Var(mangled.clone()), ty.clone()));
        }
        // A dotted accessor (`left.KX.State`, or `state-left.KX.State` in a
        // file that spells its own `define-state-relation` binders
        // differently) whose *head* — the segment before the first `.` —
        // resolves through `locals` to this definition's own left/right
        // binder (`handle_define_state_relation`'s `side_locals`, canonical
        // mangled name `l`/`r`). `self.lookup`'s own keys are always
        // `left.<rest>`/`right.<rest>` regardless of what the source file
        // calls its binders (`build_invariant_file` populates it with those
        // fixed prefixes unconditionally), so resolving here only needs to
        // translate the *canonical* `l`/`r` name back to that fixed prefix,
        // never the source's own spelling.
        if let Some((head, rest)) = a.split_once('.') {
            if let Some((canonical, _ty)) = locals.get(head) {
                let prefix = match canonical.as_str() {
                    "l" => Some("left"),
                    "r" => Some("right"),
                    _ => None,
                };
                if let Some(prefix) = prefix {
                    if let Some((expr, ty)) = self.lookup.fields.get(&format!("{prefix}.{rest}")) {
                        return Ok((expr.clone(), ty.clone()));
                    }
                }
            }
        }
        if a == "left" {
            return Ok((EcExpr::Var("l".to_string()), self.left_record_ty.clone()));
        }
        if a == "right" {
            return Ok((EcExpr::Var("r".to_string()), self.right_record_ty.clone()));
        }
        if let Some((expr, ty)) = self.lookup.fields.get(a) {
            return Ok((expr.clone(), ty.clone()));
        }
        if a == "true" {
            return Ok((EcExpr::Bool(true), EcType::Bool));
        }
        if a == "false" {
            return Ok((EcExpr::Bool(false), EcType::Bool));
        }
        if let Ok(n) = a.parse::<i64>() {
            return Ok((EcExpr::Int(n), EcType::Int));
        }
        if let Some(result) = translate_bits_literal_atom(a) {
            return Ok(result);
        }
        Err(self.unrecognised(whole))
    }

    fn translate_list(
        &mut self,
        items: &[Sexp],
        locals: &Locals,
        whole: &Sexp,
    ) -> Result<(EcExpr, EcType), InvariantError> {
        let Some(Sexp::Atom(head)) = items.first() else {
            return Err(self.unrecognised(whole));
        };
        let head = head.clone();
        let rest = &items[1..];

        match head.as_str() {
            "forall" | "exists" => return self.translate_quant(&head, rest, locals, whole),
            "let" => return self.translate_let(rest, locals, whole),
            "ite" => return self.translate_ite(rest, locals, whole),
            "and" => return self.translate_nary_bool(rest, locals, EcBinop::And, whole),
            "or" => return self.translate_nary_bool(rest, locals, EcBinop::Or, whole),
            "=>" => return self.translate_nary_bool(rest, locals, EcBinop::Implies, whole),
            "not" => return self.translate_not(rest, locals, whole),
            "=" => return self.translate_eq_n(rest, locals, whole),
            ">" | ">=" | "<" | "<=" => return self.translate_cmp(&head, rest, locals, whole),
            "+" | "-" | "*" => return self.translate_arith(&head, rest, locals, whole),
            "select" => return self.translate_select(rest, locals, whole),
            "store" => return self.translate_store(rest, locals, whole),
            "is-mk-none" => return self.translate_is_mk_none(rest, locals, whole),
            "maybe-get" => return self.translate_maybe_get(rest, locals, whole),
            "mk-some" => return self.translate_mk_some(rest, locals, whole),
            "as" => return self.translate_as(rest, whole),
            _ => {}
        }

        if let Some(fname) = head.strip_prefix("<<func-").and_then(|s| s.strip_suffix(">>")) {
            return self.translate_func(fname, rest, locals, whole);
        }
        if let Some(n) = head
            .strip_prefix("mk-tuple")
            .and_then(|s| s.parse::<usize>().ok())
        {
            return self.translate_mk_tuple(n, rest, locals, whole);
        }
        if let Some((n, i)) = parse_proj_name(&head) {
            return self.translate_proj(n, i, rest, locals, whole);
        }

        self.translate_call(&head, rest, locals, whole)
    }

    fn translate_quant(
        &mut self,
        head: &str,
        rest: &[Sexp],
        locals: &Locals,
        whole: &Sexp,
    ) -> Result<(EcExpr, EcType), InvariantError> {
        let [Sexp::List(binder_list), body] = rest else {
            return Err(self.unsupported(format!("malformed `{head}` in `{whole}`")));
        };
        let mut new_locals = locals.clone();
        let mut binders = Vec::new();
        for b in binder_list {
            let Sexp::List(pair) = b else {
                return Err(self.unsupported(format!("malformed `{head}` binder in `{whole}`")));
            };
            let [Sexp::Atom(name), sort_sexp] = &pair[..] else {
                return Err(self.unsupported(format!("malformed `{head}` binder in `{whole}`")));
            };
            let ty = translate_sort(sort_sexp, &self.file)?;
            let mangled = mangle_local_binder(&mut self.local_names, name)?;
            binders.push((mangled.clone(), ty.clone()));
            new_locals.insert(name.clone(), (mangled, ty));
        }
        let (body_expr, _) = self.translate(body, &new_locals)?;
        let kind = if head == "forall" {
            super::ast::Quantifier::Forall
        } else {
            super::ast::Quantifier::Exists
        };
        Ok((
            EcExpr::Quant {
                kind,
                binders,
                body: Box::new(body_expr),
            },
            EcType::Bool,
        ))
    }

    fn translate_let(
        &mut self,
        rest: &[Sexp],
        locals: &Locals,
        whole: &Sexp,
    ) -> Result<(EcExpr, EcType), InvariantError> {
        let [Sexp::List(binding_list), body] = rest else {
            return Err(self.unsupported(format!("malformed `let` in `{whole}`")));
        };
        let mut bindings = Vec::new();
        for b in binding_list {
            let Sexp::List(pair) = b else {
                return Err(self.unsupported(format!("malformed `let` binding in `{whole}`")));
            };
            let [Sexp::Atom(name), value_sexp] = &pair[..] else {
                return Err(self.unsupported(format!("malformed `let` binding in `{whole}`")));
            };
            // SMT-LIB `let` bindings are evaluated in parallel, in the
            // *outer* scope — translate every value before any of this
            // `let`'s own names are added to `locals`.
            let (value_expr, value_ty) = self.translate(value_sexp, locals)?;
            let mangled = mangle_local_binder(&mut self.local_names, name)?;
            bindings.push((name.clone(), mangled, value_expr, value_ty));
        }
        let mut new_locals = locals.clone();
        for (raw, mangled, _, ty) in &bindings {
            new_locals.insert(raw.clone(), (mangled.clone(), ty.clone()));
        }
        let (mut result, ty) = self.translate(body, &new_locals)?;
        for (_, mangled, value_expr, _) in bindings.into_iter().rev() {
            // Drop a binding of `None` (only) when the body never
            // references it, rather than emitting a dead `let`. Story 12
            // stopped annotating `None` with its type, and an SMT source
            // can bind a name to `(as mk-none ...)` and then never use it
            // (`invariant-H6_1-H7_0.smt2`'s `freshness-and-honesty-matches`
            // does exactly this — it calls `is-mk-none` directly instead of
            // comparing against the bound name). An unused `let none =
            // None in <body not mentioning none>` leaves `none`'s type as a
            // free type variable and `easycrypt compile` rejects the
            // top-level `op` outright (`this operator type contains free
            // type variables`) — the exact failure mode the story's own
            // `op bad = None.` example predicts. Eliding the binding is
            // sound (SMT-LIB `let` has no side effects to preserve) and is
            // the "fix targeted at that construct" the story asks for,
            // rather than a fallback in `None_`'s rendering.
            //
            // Scoped to `None_` specifically (not general dead-`let`
            // elimination): other unused bindings the translator already
            // emits (e.g. an unused `k = (oget state).\`6` alongside a
            // used `acc`/`ni`/...) bind a concretely-typed value, so
            // leaving them in place is both harmless to `easycrypt compile`
            // and preserves every existing golden byte-for-byte outside
            // this story's `None<:...>` -> `None` change.
            let is_dead_none =
                matches!(value_expr, EcExpr::None_(_)) && !expr_references_var(&result, &mangled);
            if !is_dead_none {
                result = EcExpr::Let {
                    name: mangled,
                    value: Box::new(value_expr),
                    body: Box::new(result),
                };
            }
        }
        Ok((result, ty))
    }

    fn translate_ite(
        &mut self,
        rest: &[Sexp],
        locals: &Locals,
        whole: &Sexp,
    ) -> Result<(EcExpr, EcType), InvariantError> {
        let [cond, then_s, else_s] = rest else {
            return Err(self.unsupported(format!("`ite` needs 3 arguments in `{whole}`")));
        };
        let (cond_expr, _) = self.translate(cond, locals)?;
        let (then_expr, then_ty) = self.translate(then_s, locals)?;
        let (else_expr, _) = self.translate(else_s, locals)?;
        Ok((
            EcExpr::If {
                cond: Box::new(cond_expr),
                then_expr: Box::new(then_expr),
                else_expr: Box::new(else_expr),
            },
            then_ty,
        ))
    }

    fn translate_nary_bool(
        &mut self,
        rest: &[Sexp],
        locals: &Locals,
        op: EcBinop,
        whole: &Sexp,
    ) -> Result<(EcExpr, EcType), InvariantError> {
        if rest.is_empty() {
            return Err(self.unsupported(format!("empty n-ary connective in `{whole}`")));
        }
        let mut exprs = Vec::with_capacity(rest.len());
        for item in rest {
            exprs.push(self.translate(item, locals)?.0);
        }
        let folded = EcExpr::right_chain(op, exprs).expect("checked non-empty above");
        Ok((folded, EcType::Bool))
    }

    fn translate_not(
        &mut self,
        rest: &[Sexp],
        locals: &Locals,
        whole: &Sexp,
    ) -> Result<(EcExpr, EcType), InvariantError> {
        let [arg] = rest else {
            return Err(self.unsupported(format!("`not` needs 1 argument in `{whole}`")));
        };
        let (arg_expr, _) = self.translate(arg, locals)?;
        Ok((
            EcExpr::Unop {
                op: EcUnop::Not,
                arg: Box::new(arg_expr),
            },
            EcType::Bool,
        ))
    }

    /// Recognises an atom of the form `<binder>.<instance>` — exactly one
    /// `.`, no field segment — whose binder resolves through `locals` to
    /// this definition's own left/right record parameter, and whose
    /// instance exists on that side: an SMT atom naming an entire package
    /// instance's state, not one field of it. `Full4WHS`'s invariants do
    /// this for real (`(= state-left.KX state-right.KX)`).
    /// [`Self::translate_eq_n`] special-cases the two-argument `=` of two
    /// such atoms (see [`Self::translate_instance_equality`]); anywhere else
    /// the atom stays unrecognised.
    ///
    /// Returns the instance's [`StateLookup::instances`] entry. Never confused with a
    /// field access (`left.KX.State`, three segments): `instance`
    /// containing a further `.` short-circuits this to `None` immediately.
    fn resolve_instance_atom(&self, a: &str, locals: &Locals) -> Option<&InstanceEntry> {
        let (head, instance) = a.split_once('.')?;
        if instance.contains('.') {
            return None;
        }
        let (canonical, _ty) = locals.get(head)?;
        let prefix = match canonical.as_str() {
            "l" => "left",
            "r" => "right",
            _ => return None,
        };
        self.lookup.instances.get(&format!("{prefix}.{instance}"))
    }

    /// A whole-package-state equality (`(= state-left.KX state-right.KX)`,
    /// story 42 §3.3). A package's state is its state fields only
    /// (`CONTEXT.md`, *Package state*), so parameters never take part:
    ///
    /// - two instances of one package with state: one equality of their
    ///   `<Pkg>_pkgstate` records, ``l.`l_pkg_KX = r.`r_pkg_KX``;
    /// - two instances of one package without state: `true`;
    /// - instances of different packages: a hard
    ///   [`InvariantError::PackageMismatch`]. In Domino the `=` would be
    ///   ill-sorted.
    fn translate_instance_equality(
        &self,
        left: &InstanceEntry,
        right: &InstanceEntry,
    ) -> Result<(EcExpr, EcType), InvariantError> {
        if left.package != right.package {
            return Err(InvariantError::PackageMismatch {
                file: self.file.clone(),
                left_instance: left.instance.clone(),
                left_package: left.package.clone(),
                right_instance: right.instance.clone(),
                right_package: right.package.clone(),
            });
        }
        // One package has one list of state fields, so both instances
        // either have state or have none.
        let equality = match (&left.state, &right.state) {
            (Some(l), Some(r)) => eq_expr(l.clone(), r.clone()),
            (None, None) => EcExpr::Bool(true),
            _ => unreachable!(
                "instances `{}` and `{}` of package `{}` disagree on having state",
                left.instance, right.instance, left.package
            ),
        };
        Ok((equality, EcType::Bool))
    }

    fn translate_eq_n(
        &mut self,
        rest: &[Sexp],
        locals: &Locals,
        whole: &Sexp,
    ) -> Result<(EcExpr, EcType), InvariantError> {
        if rest.len() < 2 {
            return Err(self.unsupported(format!("`=` needs at least 2 arguments in `{whole}`")));
        }
        if let [Sexp::Atom(a), Sexp::Atom(b)] = rest {
            if let (Some(left), Some(right)) = (
                self.resolve_instance_atom(a, locals),
                self.resolve_instance_atom(b, locals),
            ) {
                return self.translate_instance_equality(left, right);
            }
        }
        let mut exprs = Vec::with_capacity(rest.len());
        for item in rest {
            exprs.push(self.translate(item, locals)?.0);
        }
        if exprs.len() == 2 {
            let rhs = exprs.pop().unwrap();
            let lhs = exprs.pop().unwrap();
            return Ok((eq_expr(lhs, rhs), EcType::Bool));
        }
        let pairs: Vec<EcExpr> = exprs
            .windows(2)
            .map(|w| eq_expr(w[0].clone(), w[1].clone()))
            .collect();
        Ok((fold_and(pairs), EcType::Bool))
    }

    fn translate_cmp(
        &mut self,
        head: &str,
        rest: &[Sexp],
        locals: &Locals,
        whole: &Sexp,
    ) -> Result<(EcExpr, EcType), InvariantError> {
        let [a, b] = rest else {
            return Err(self.unsupported(format!("`{head}` needs 2 arguments in `{whole}`")));
        };
        let (a_expr, _) = self.translate(a, locals)?;
        let (b_expr, _) = self.translate(b, locals)?;
        // EasyCrypt's base theories (`Int`/`IntDiv`) define `<`/`<=` but
        // not `>`/`>=` for `int` — those notations resolve only via
        // `Real.>`/`Real.>=`, which then reject `int` arguments (verified
        // against `r2026.06-12-g7e192dd`: `a > b` on two `int`s fails with
        // "operator `Top.Real.>' cannot be applied ... expected ... real
        // ... applied to a value of type int"). Story 02's own Domino-
        // expression translator already discovered this and always flips
        // `GreaterThen(a, b)` to `Lt(b, a)`; this does the same for the
        // SMT-LIB `>`/`>=` forms rather than emitting `EcBinop::Gt`/`Ge`,
        // which — despite existing as AST/render constructors — are not
        // actually usable for `int`.
        let (op, lhs, rhs) = match head {
            ">" => (EcBinop::Lt, b_expr, a_expr),
            ">=" => (EcBinop::Le, b_expr, a_expr),
            "<" => (EcBinop::Lt, a_expr, b_expr),
            "<=" => (EcBinop::Le, a_expr, b_expr),
            _ => unreachable!("matched only these four in translate_list"),
        };
        Ok((
            EcExpr::Binop {
                op,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            },
            EcType::Bool,
        ))
    }

    fn translate_arith(
        &mut self,
        head: &str,
        rest: &[Sexp],
        locals: &Locals,
        whole: &Sexp,
    ) -> Result<(EcExpr, EcType), InvariantError> {
        if head == "-" && rest.len() == 1 {
            let (a_expr, _) = self.translate(&rest[0], locals)?;
            return Ok((
                EcExpr::Unop {
                    op: EcUnop::Neg,
                    arg: Box::new(a_expr),
                },
                EcType::Int,
            ));
        }
        let [a, b] = rest else {
            return Err(self.unsupported(format!("`{head}` needs 2 arguments in `{whole}`")));
        };
        let (a_expr, _) = self.translate(a, locals)?;
        let (b_expr, _) = self.translate(b, locals)?;
        let op = match head {
            "+" => EcBinop::Add,
            "-" => EcBinop::Sub,
            "*" => EcBinop::Mul,
            _ => unreachable!("matched only these three in translate_list"),
        };
        Ok((
            EcExpr::Binop {
                op,
                lhs: Box::new(a_expr),
                rhs: Box::new(b_expr),
            },
            EcType::Int,
        ))
    }

    fn translate_select(
        &mut self,
        rest: &[Sexp],
        locals: &Locals,
        whole: &Sexp,
    ) -> Result<(EcExpr, EcType), InvariantError> {
        let [a, k] = rest else {
            return Err(self.unsupported(format!("`select` needs 2 arguments in `{whole}`")));
        };
        let (a_expr, a_ty) = self.translate(a, locals)?;
        let (k_expr, _) = self.translate(k, locals)?;
        let EcType::Fmap(_, value_ty) = a_ty else {
            return Err(self.unsupported(format!("`select` on a non-map value in `{whole}`")));
        };
        Ok((
            EcExpr::MapGet {
                map: Box::new(a_expr),
                key: Box::new(k_expr),
            },
            EcType::Option(value_ty),
        ))
    }

    fn translate_store(
        &mut self,
        rest: &[Sexp],
        locals: &Locals,
        whole: &Sexp,
    ) -> Result<(EcExpr, EcType), InvariantError> {
        let [a, k, v] = rest else {
            return Err(self.unsupported(format!("`store` needs 3 arguments in `{whole}`")));
        };
        let (a_expr, a_ty) = self.translate(a, locals)?;
        let (k_expr, _) = self.translate(k, locals)?;
        let (v_expr, _) = self.translate(v, locals)?;
        Ok((
            EcExpr::MapSet {
                map: Box::new(a_expr),
                key: Box::new(k_expr),
                value: Box::new(v_expr),
            },
            a_ty,
        ))
    }

    fn translate_is_mk_none(
        &mut self,
        rest: &[Sexp],
        locals: &Locals,
        whole: &Sexp,
    ) -> Result<(EcExpr, EcType), InvariantError> {
        let [e] = rest else {
            return Err(self.unsupported(format!("`is-mk-none` needs 1 argument in `{whole}`")));
        };
        let (e_expr, e_ty) = self.translate(e, locals)?;
        let EcType::Option(inner) = e_ty else {
            return Err(self.unsupported(format!("`is-mk-none` on a non-`Maybe` value in `{whole}`")));
        };
        Ok((eq_expr(e_expr, EcExpr::None_(*inner)), EcType::Bool))
    }

    fn translate_maybe_get(
        &mut self,
        rest: &[Sexp],
        locals: &Locals,
        whole: &Sexp,
    ) -> Result<(EcExpr, EcType), InvariantError> {
        let [e] = rest else {
            return Err(self.unsupported(format!("`maybe-get` needs 1 argument in `{whole}`")));
        };
        let (e_expr, e_ty) = self.translate(e, locals)?;
        let EcType::Option(inner) = e_ty else {
            return Err(self.unsupported(format!("`maybe-get` on a non-`Maybe` value in `{whole}`")));
        };
        Ok((EcExpr::Oget(Box::new(e_expr)), *inner))
    }

    fn translate_mk_some(
        &mut self,
        rest: &[Sexp],
        locals: &Locals,
        whole: &Sexp,
    ) -> Result<(EcExpr, EcType), InvariantError> {
        let [e] = rest else {
            return Err(self.unsupported(format!("`mk-some` needs 1 argument in `{whole}`")));
        };
        let (e_expr, e_ty) = self.translate(e, locals)?;
        Ok((
            EcExpr::Some_(Box::new(e_expr)),
            EcType::Option(Box::new(e_ty)),
        ))
    }

    fn translate_as(&self, rest: &[Sexp], whole: &Sexp) -> Result<(EcExpr, EcType), InvariantError> {
        let [Sexp::Atom(tag), Sexp::List(sort_items)] = rest else {
            return Err(self.unsupported(format!("unsupported `as` form in `{whole}`")));
        };
        if tag != "mk-none" {
            return Err(self.unsupported(format!("unsupported `as` form in `{whole}`")));
        }
        let [Sexp::Atom(maybe), inner_sort] = &sort_items[..] else {
            return Err(self.unsupported(format!("unsupported `as mk-none` sort in `{whole}`")));
        };
        if maybe != "Maybe" {
            return Err(self.unsupported(format!("unsupported `as mk-none` sort in `{whole}`")));
        }
        let inner = translate_sort(inner_sort, &self.file)?;
        Ok((
            EcExpr::None_(inner.clone()),
            EcType::Option(Box::new(inner)),
        ))
    }

    fn translate_mk_tuple(
        &mut self,
        n: usize,
        rest: &[Sexp],
        locals: &Locals,
        whole: &Sexp,
    ) -> Result<(EcExpr, EcType), InvariantError> {
        if rest.len() != n {
            return Err(self.unsupported(format!(
                "`mk-tuple{n}` needs {n} arguments in `{whole}`"
            )));
        }
        let mut exprs = Vec::with_capacity(n);
        let mut tys = Vec::with_capacity(n);
        for item in rest {
            let (e, t) = self.translate(item, locals)?;
            exprs.push(e);
            tys.push(t);
        }
        Ok((EcExpr::Tuple(exprs), EcType::Tuple(tys)))
    }

    fn translate_proj(
        &mut self,
        n: usize,
        i: usize,
        rest: &[Sexp],
        locals: &Locals,
        whole: &Sexp,
    ) -> Result<(EcExpr, EcType), InvariantError> {
        let [e] = rest else {
            return Err(self.unsupported(format!("`el{n}-{i}` needs 1 argument in `{whole}`")));
        };
        let (e_expr, e_ty) = self.translate(e, locals)?;
        let EcType::Tuple(comps) = e_ty else {
            return Err(self.unsupported(format!("`el{n}-{i}` on a non-tuple value in `{whole}`")));
        };
        if comps.len() != n || i < 1 || i > n {
            return Err(self.unsupported(format!(
                "`el{n}-{i}` doesn't match its argument's {}-tuple in `{whole}`",
                comps.len()
            )));
        }
        Ok((
            EcExpr::Proj {
                expr: Box::new(e_expr),
                index: i,
            },
            comps[i - 1].clone(),
        ))
    }

    fn translate_func(
        &mut self,
        fname: &str,
        rest: &[Sexp],
        locals: &Locals,
        whole: &Sexp,
    ) -> Result<(EcExpr, EcType), InvariantError> {
        let mut args = Vec::with_capacity(rest.len());
        for item in rest {
            args.push(self.translate(item, locals)?.0);
        }
        let Some((_, ty)) = self.theorem_consts.iter().find(|(n, _)| n == fname) else {
            return Err(self.unrecognised(whole));
        };
        let crate::types::TypeKind::Fn(_, ret) = ty.kind() else {
            return Err(self.unsupported(format!("`<<func-{fname}>>` is not a function const")));
        };
        let ret_ty = translate_type(ret, SourceSpan::from((0, 0)))
            .map_err(|_| self.unsupported(format!("unsupported return type for `<<func-{fname}>>`")))?;
        Ok((
            EcExpr::App {
                head: func_op_name(fname),
                args,
            },
            ret_ty,
        ))
    }

    fn translate_call(
        &mut self,
        head: &str,
        rest: &[Sexp],
        locals: &Locals,
        whole: &Sexp,
    ) -> Result<(EcExpr, EcType), InvariantError> {
        let Some((mangled, ret_ty)) = self.ops.lookup(head).cloned() else {
            return Err(self.unrecognised(whole));
        };
        let mut args = Vec::with_capacity(rest.len());
        for item in rest {
            args.push(self.translate(item, locals)?.0);
        }
        Ok((
            EcExpr::App {
                head: mangled,
                args,
            },
            ret_ty,
        ))
    }
}

/// `elN-i` -> `(N, i)`, only when both halves parse as plain integers
/// (guards against a coincidentally `el`-prefixed, dash-containing
/// operator name being misread as a projection).
fn parse_proj_name(head: &str) -> Option<(usize, usize)> {
    let rest = head.strip_prefix("el")?;
    let (n, i) = rest.split_once('-')?;
    Some((n.parse().ok()?, i.parse().ok()?))
}

// --- driving the SMT parser ---------------------------------------------

struct InvariantParserState<'a> {
    file: String,
    lookup: &'a StateLookup,
    left_record_ty: EcType,
    right_record_ty: EcType,
    theorem_consts: &'a [(String, Type)],
    ops: OpRegistry,
    items: Vec<EcItem>,
    /// Mangled names of every translated `define-state-relation`, file
    /// order — folded into `op inv`'s guarded conjunction. `define-fun`
    /// helpers are *not* included here (only referenced via calls from
    /// inside a state relation's own body, if at all).
    state_relations: Vec<String>,
    skipped: Vec<String>,
}

impl SmtParser<InvariantError> for InvariantParserState<'_> {
    type Expr = Sexp;
    type Stmt = Sexp;

    fn handle_atom(&mut self, content: &str) -> Result<Sexp, InvariantError> {
        Ok(Sexp::Atom(content.to_string()))
    }

    fn handle_list(&mut self, content: Vec<Sexp>) -> Result<Sexp, InvariantError> {
        Ok(Sexp::List(content))
    }

    fn handle_sexp(&mut self, _parsed: Sexp) -> Result<(), InvariantError> {
        // Every real form is handled (and self.items/self.ops updated)
        // directly in the overrides below; a bare top-level s-expression
        // (the trait's own catch-all) carries no meaning here.
        Ok(())
    }

    fn handle_definefun(
        &mut self,
        funname: &str,
        args: Vec<Sexp>,
        ty: &str,
        body: Sexp,
    ) -> Result<Sexp, InvariantError> {
        if funname.starts_with("randomness-mapping-") {
            self.items.push(EcItem::Comment(format!(
                "skipped `define-fun {funname}` (randomness mapping, not translated)"
            )));
            self.skipped
                .push(format!("define-fun {funname} (randomness mapping)"));
            return Ok(Sexp::Atom(String::new()));
        }

        let mut local_names = Names::new();
        let mut locals: Locals = HashMap::new();
        let mut arg_list = Vec::with_capacity(args.len());
        for a in &args {
            let Sexp::List(pair) = a else {
                return Err(InvariantError::Unsupported {
                    file: self.file.clone(),
                    detail: format!("malformed `define-fun {funname}` argument"),
                });
            };
            let [Sexp::Atom(name), sort_sexp] = &pair[..] else {
                return Err(InvariantError::Unsupported {
                    file: self.file.clone(),
                    detail: format!("malformed `define-fun {funname}` argument"),
                });
            };
            let ec_ty = translate_sort(sort_sexp, &self.file)?;
            let mangled = mangle_local_binder(&mut local_names, name)?;
            arg_list.push((mangled.clone(), ec_ty.clone()));
            locals.insert(name.clone(), (mangled, ec_ty));
        }
        let ret_ty = translate_sort(&parse_sort_text(ty), &self.file)?;

        let (body_expr, _) = {
            let mut tctx = TCtx {
                file: self.file.clone(),
                lookup: self.lookup,
                left_record_ty: self.left_record_ty.clone(),
                right_record_ty: self.right_record_ty.clone(),
                theorem_consts: self.theorem_consts,
                ops: &self.ops,
                local_names,
            };
            tctx.translate(&body, &locals)?
        };

        let mangled_name = self.ops.define(&self.file, funname, ret_ty.clone())?;
        self.items.push(EcItem::OpDef {
            name: mangled_name,
            args: arg_list,
            ret: Some(ret_ty),
            body: body_expr,
        });
        Ok(Sexp::Atom(String::new()))
    }

    fn handle_define_state_relation(
        &mut self,
        funname: &str,
        args: Vec<Sexp>,
        body: Sexp,
    ) -> Result<Sexp, InvariantError> {
        let [Sexp::Atom(l), Sexp::Atom(r)] = &args[..] else {
            return Err(InvariantError::Unsupported {
                file: self.file.clone(),
                detail: format!("malformed `define-state-relation {funname}` binders"),
            });
        };
        // Binder *names* are this definition's own local parameter names —
        // purely positional (first = left side, second = right side),
        // exactly like an ordinary `define-fun` argument list, not a fixed
        // vocabulary. `Simple4WHS`'s own invariants spell them `left`/
        // `right` throughout, but nothing in the SMT-LIB grammar requires
        // that, and `Full4WHS`'s own invariants spell them `state-left`/
        // `state-right` instead — both are just this form's own two bound
        // names. Bound into `locals` exactly as `handle_definefun`'s own
        // arguments are (`translate_atom`'s existing `locals.get(a)` check
        // handles the bare-atom case for free); a dotted atom whose head
        // resolves through `locals` to one of these two canonical `l`/`r`
        // targets is resolved by `translate_atom`'s own dotted-access case
        // below, so `left.KX.State`/`state-left.KX.State` both work
        // uniformly without `self.lookup` ever needing to know which
        // spelling a given file chose.
        if l == r {
            return Err(InvariantError::Unsupported {
                file: self.file.clone(),
                detail: format!(
                    "`define-state-relation {funname}` binders must be two distinct names, got `({l} {r})` twice"
                ),
            });
        }
        let mut side_locals = Locals::new();
        side_locals.insert(l.clone(), ("l".to_string(), self.left_record_ty.clone()));
        side_locals.insert(r.clone(), ("r".to_string(), self.right_record_ty.clone()));

        let (body_expr, _) = {
            let mut tctx = TCtx {
                file: self.file.clone(),
                lookup: self.lookup,
                left_record_ty: self.left_record_ty.clone(),
                right_record_ty: self.right_record_ty.clone(),
                theorem_consts: self.theorem_consts,
                ops: &self.ops,
                local_names: Names::new(),
            };
            tctx.translate(&body, &side_locals)?
        };

        let mangled_name = self.ops.define(&self.file, funname, EcType::Bool)?;
        self.items.push(EcItem::OpDef {
            name: mangled_name.clone(),
            args: vec![
                ("l".to_string(), self.left_record_ty.clone()),
                ("r".to_string(), self.right_record_ty.clone()),
            ],
            ret: Some(EcType::Bool),
            body: body_expr,
        });
        self.state_relations.push(mangled_name);
        Ok(Sexp::Atom(String::new()))
    }

    fn handle_define_lemma(
        &mut self,
        funname: &str,
        _args: Vec<Sexp>,
        _body: Sexp,
    ) -> Result<Sexp, InvariantError> {
        self.items.push(EcItem::Comment(format!(
            "skipped `define-lemma {funname}` (not translated)"
        )));
        self.skipped.push(format!("define-lemma {funname}"));
        Ok(Sexp::Atom(String::new()))
    }

    fn handle_define_game_invariant(&mut self, _body: Sexp) -> Result<Sexp, InvariantError> {
        self.items.push(EcItem::Comment(
            "skipped `define-game-invariant` (not translated)".to_string(),
        ));
        self.skipped
            .push("define-game-invariant".to_string());
        Ok(Sexp::Atom(String::new()))
    }

    fn handle_define_package_invariant(&mut self, _body: Sexp) -> Result<Sexp, InvariantError> {
        self.items.push(EcItem::Comment(
            "skipped `define-package-invariant` (not translated)".to_string(),
        ));
        self.skipped
            .push("define-package-invariant".to_string());
        Ok(Sexp::Atom(String::new()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::writers::easycrypt::render::render_expr;

    fn fields_only(fields: HashMap<String, (EcExpr, EcType)>) -> StateLookup {
        StateLookup {
            fields,
            ..StateLookup::default()
        }
    }

    fn translate_body(smt: &str) -> String {
        translate_body_with(smt, &HashMap::new(), &[])
    }

    fn translate_body_with(
        smt: &str,
        lookup: &HashMap<String, (EcExpr, EcType)>,
        theorem_consts: &[(String, Type)],
    ) -> String {
        let sexp = parse_sort_text(smt);
        let ops = OpRegistry::default();
        let lookup = fields_only(lookup.clone());
        let mut tctx = TCtx {
            file: "test.smt2".to_string(),
            lookup: &lookup,
            left_record_ty: EcType::Named("Left_state".to_string()),
            right_record_ty: EcType::Named("Right_state".to_string()),
            theorem_consts,
            ops: &ops,
            local_names: Names::new(),
        };
        let (expr, _) = tctx.translate(&sexp, &Locals::new()).unwrap();
        render_expr(&expr)
    }

    #[test]
    fn forall_translates() {
        assert_eq!(
            translate_body("(forall ((x Int)) (> x 0))"),
            "forall (x : int), 0 < x"
        );
    }

    #[test]
    fn exists_translates() {
        assert_eq!(
            translate_body("(exists ((x Int)) (= x 0))"),
            "exists (x : int), x = 0"
        );
    }

    #[test]
    fn exists_binder_named_r_does_not_shadow_the_right_record_param() {
        // `kem-dem-cca-ssp`'s own invariant hits this for real:
        // `(exists ((r Bits_kgenr)) (= (maybe-get right.KEM.pk) (el2-1
        // (<<func-kem_gen>> r))))` — the existential `r` must not collide
        // with the fixed `r` record parameter every `right.*` dotted
        // accessor already resolves to.
        let mut lookup = HashMap::new();
        lookup.insert(
            "right.KEM.pk".to_string(),
            (field_expr("r", "r_pkg_KEM_pk"), EcType::Option(Box::new(EcType::Int))),
        );
        assert_eq!(
            translate_body_with(
                "(exists ((r Int)) (= right.KEM.pk (mk-some r)))",
                &lookup,
                &[],
            ),
            "exists (q_r : int), r.`r_pkg_KEM_pk = Some q_r"
        );
    }

    #[test]
    fn dotted_state_accessor_translates_to_a_field_projection() {
        let mut lookup = HashMap::new();
        lookup.insert(
            "left.KX.State".to_string(),
            (field_expr("l", "l_pkg_KX_State"), EcType::Int),
        );
        lookup.insert(
            "right.KX.State".to_string(),
            (field_expr("r", "r_pkg_KX_State"), EcType::Int),
        );
        assert_eq!(
            translate_body_with("(= left.KX.State right.KX.State)", &lookup, &[]),
            "l.`l_pkg_KX_State = r.`r_pkg_KX_State"
        );
    }

    #[test]
    fn let_single_binding_translates() {
        assert_eq!(translate_body("(let ((x 1)) x)"), "let x = 1 in x");
    }

    #[test]
    fn let_multi_binding_desugars_to_nested_lets() {
        assert_eq!(
            translate_body("(let ((x 1) (y 2)) (+ x y))"),
            "let x = 1 in let y = 2 in x + y"
        );
    }

    #[test]
    fn ite_translates() {
        assert_eq!(translate_body("(ite true 1 2)"), "if true then 1 else 2");
    }

    #[test]
    fn and_or_not_implies_translate() {
        assert_eq!(translate_body("(and true false)"), "true /\\ false");
        assert_eq!(translate_body("(or true false)"), "true \\/ false");
        assert_eq!(translate_body("(not true)"), "!true");
        assert_eq!(translate_body("(=> true false)"), "true => false");
    }

    #[test]
    fn n_ary_connectives_nest_to_the_right_and_render_flat() {
        // Story 43 §3.1: EasyCrypt's `/\`, `\/` and `=>` are right-associative,
        // and SMT-LIB's n-ary `=>` is `:right-assoc` too.
        assert_eq!(translate_body("(and true false true)"), "true /\\ false /\\ true");
        assert_eq!(translate_body("(or true false true)"), "true \\/ false \\/ true");
        assert_eq!(translate_body("(=> true false true)"), "true => false => true");
        assert_eq!(translate_body("(= 1 2 3 4)"), "1 = 2 /\\ 2 = 3 /\\ 3 = 4");
    }

    #[test]
    fn a_conjunction_inside_a_conjunction_is_spliced_into_one_chain() {
        // `/\` and `\/` are associative, so a nested chain joins its parent:
        // the same term EasyCrypt read before story 43, without parentheses.
        // `=>` is not associative and keeps its nesting.
        assert_eq!(
            translate_body("(and (and true false) (= 1 2 3) true)"),
            "true /\\ false /\\ 1 = 2 /\\ 2 = 3 /\\ true"
        );
        assert_eq!(translate_body("(or (or true false) true)"), "true \\/ false \\/ true");
        assert_eq!(translate_body("(=> (=> true false) true)"), "(true => false) => true");
        assert_eq!(translate_body("(and (or true false) true)"), "(true \\/ false) /\\ true");
    }

    #[test]
    fn eq_two_args_translates() {
        assert_eq!(translate_body("(= 1 2)"), "1 = 2");
    }

    #[test]
    fn eq_n_args_is_adjacent_pair_conjunction() {
        assert_eq!(translate_body("(= 1 2 3)"), "1 = 2 /\\ 2 = 3");
    }

    #[test]
    fn comparisons_and_arithmetic_translate() {
        // `>`/`>=` are always flipped to `<`/`<=` with swapped operands —
        // EasyCrypt's `Int`/`IntDiv` theories don't define `>`/`>=` for
        // `int` (see `translate_cmp`'s own comment).
        assert_eq!(translate_body("(> 1 2)"), "2 < 1");
        assert_eq!(translate_body("(>= 1 2)"), "2 <= 1");
        assert_eq!(translate_body("(< 1 2)"), "1 < 2");
        assert_eq!(translate_body("(<= 1 2)"), "1 <= 2");
        assert_eq!(translate_body("(+ 1 2)"), "1 + 2");
        assert_eq!(translate_body("(- 1 2)"), "1 - 2");
        assert_eq!(translate_body("(* 1 2)"), "1 * 2");
    }

    #[test]
    fn select_and_store_translate() {
        let mut lookup = HashMap::new();
        lookup.insert(
            "left.KX.State".to_string(),
            (
                field_expr("l", "l_pkg_KX_State"),
                EcType::Fmap(Box::new(EcType::Int), Box::new(EcType::Int)),
            ),
        );
        assert_eq!(
            translate_body_with("(select left.KX.State 0)", &lookup, &[]),
            "l.`l_pkg_KX_State.[0]"
        );
        assert_eq!(
            translate_body_with("(store left.KX.State 0 1)", &lookup, &[]),
            "l.`l_pkg_KX_State.[0 <- 1]"
        );
    }

    #[test]
    fn is_mk_none_and_maybe_get_translate() {
        let mut lookup = HashMap::new();
        lookup.insert(
            "left.KX.State".to_string(),
            (
                field_expr("l", "l_pkg_KX_State"),
                EcType::Option(Box::new(EcType::Int)),
            ),
        );
        assert_eq!(
            translate_body_with("(is-mk-none left.KX.State)", &lookup, &[]),
            "l.`l_pkg_KX_State = None"
        );
        assert_eq!(
            translate_body_with("(maybe-get left.KX.State)", &lookup, &[]),
            "oget l.`l_pkg_KX_State"
        );
    }

    #[test]
    fn mk_some_and_as_mk_none_translate() {
        assert_eq!(translate_body("(mk-some 1)"), "Some 1");
        assert_eq!(
            translate_body("(as mk-none (Maybe Bits_n))"),
            "None"
        );
    }

    #[test]
    fn tuple_construction_and_projection_round_trip() {
        assert_eq!(
            translate_body("(el10-4 (mk-tuple10 1 2 3 4 5 6 7 8 9 10))"),
            "(1, 2, 3, 4, 5, 6, 7, 8, 9, 10).`4"
        );
    }

    #[test]
    fn func_application_translates() {
        let consts = vec![("prf".to_string(), Type::fun(vec![Type::integer()], Type::integer()))];
        assert_eq!(
            translate_body_with("(<<func-prf>> 1)", &HashMap::new(), &consts),
            "func_prf 1"
        );
    }

    #[test]
    fn calling_a_previously_defined_op_translates() {
        let sexp = parse_sort_text("(state= left right)");
        let mut ops = OpRegistry::default();
        ops.define("test.smt2", "state=", EcType::Bool).unwrap();
        let mut tctx = TCtx {
            file: "test.smt2".to_string(),
            lookup: &StateLookup::default(),
            left_record_ty: EcType::Named("Left_state".to_string()),
            right_record_ty: EcType::Named("Right_state".to_string()),
            theorem_consts: &[],
            ops: &ops,
            local_names: Names::new(),
        };
        let (expr, _) = tctx.translate(&sexp, &Locals::new()).unwrap();
        assert_eq!(render_expr(&expr), "Domino_state_eq l r");
    }

    #[test]
    fn unknown_atom_is_a_hard_error() {
        let sexp = parse_sort_text("totally-unknown-thing");
        let ops = OpRegistry::default();
        let mut tctx = TCtx {
            file: "test.smt2".to_string(),
            lookup: &StateLookup::default(),
            left_record_ty: EcType::Named("Left_state".to_string()),
            right_record_ty: EcType::Named("Right_state".to_string()),
            theorem_consts: &[],
            ops: &ops,
            local_names: Names::new(),
        };
        let err = tctx.translate(&sexp, &Locals::new()).unwrap_err();
        assert!(matches!(err, InvariantError::Unrecognised { .. }));
    }

    #[test]
    fn mangle_smt_def_name_examples() {
        assert_eq!(mangle_smt_def_name("state="), "state_eq");
        assert_eq!(mangle_smt_def_name("=prf"), "eq_prf");
        assert_eq!(
            mangle_smt_def_name("keys-computed-correctly"),
            "keys_computed_correctly"
        );
    }

    #[test]
    fn name_collision_differing_only_by_dash_underscore_is_a_hard_error() {
        let mut ops = OpRegistry::default();
        ops.define("test.smt2", "no-overwriting-state", EcType::Bool)
            .unwrap();
        let err = ops
            .define("test.smt2", "no_overwriting_state", EcType::Bool)
            .unwrap_err();
        assert!(matches!(err, InvariantError::NameCollision { .. }));
    }

    // --- golden file: 4WHS `Simple4WHS`'s `Hybrid0 ~ Hybrid1` -----------

    fn load_hybrid0_hybrid1() -> (
        crate::theorem::Theorem<'static>,
        &'static crate::project::DirectoryProject<'static>,
    ) {
        use crate::project::{DirectoryFiles, DirectoryProject, Project};
        use crate::transforms::theorem_transforms::EasyCryptTransform;
        use crate::transforms::TheoremTransform;

        let dir = "example-projects/4WHS";
        let files: &'static DirectoryFiles =
            Box::leak(Box::new(DirectoryFiles::load(std::path::Path::new(dir)).unwrap()));
        let project: &'static DirectoryProject = Box::leak(Box::new(
            DirectoryProject::load(std::path::PathBuf::from(dir), files).unwrap(),
        ));
        let theorem = project.get_theorem("Simple4WHS").unwrap();
        let (theorem, _auxs) = EasyCryptTransform.transform_theorem(theorem).unwrap();
        (theorem, project)
    }

    fn find_equivalence<'a>(
        theorem: &'a crate::theorem::Theorem<'_>,
        left: &str,
        right: &str,
    ) -> &'a Equivalence {
        theorem
            .game_hops
            .iter()
            .find_map(|hop| match hop {
                crate::gamehops::GameHop::Equivalence(eq)
                    if eq.left_name() == left && eq.right_name() == right =>
                {
                    Some(eq)
                }
                _ => None,
            })
            .expect("equivalence not found")
    }

    #[test]
    fn hybrid0_hybrid1_invariants_file_matches_golden() {
        let (theorem, project) = load_hybrid0_hybrid1();
        let equivalence = find_equivalence(&theorem, "Hybrid0", "Hybrid1");

        let result = build_invariant_file(&theorem, equivalence, project).unwrap();
        let rendered = crate::writers::easycrypt::render::render_file(&result.file);

        let full_path = format!(
            "{}/testdata/easycrypt/story06/4WHS/Eq_Hybrid0_Hybrid1_Invariants.ec",
            env!("CARGO_MANIFEST_DIR")
        );
        let expected = std::fs::read_to_string(&full_path)
            .unwrap_or_else(|e| panic!("failed to read golden file {full_path}: {e}"));
        assert_eq!(rendered, expected, "rendered != {full_path}");

        assert_eq!(result.left_state_type, "Hybrid0_state");
        assert_eq!(result.right_state_type, "Hybrid1_state");
        assert_eq!(result.file_name, "Eq_Hybrid0_Hybrid1_Invariants.ec");
        assert!(result.skipped.is_empty());
    }

    #[test]
    fn h1_1_h2_0_invariants_file_matches_golden() {
        // Story 42 §4.3: `Full4WHS`'s hop whose right side has an instance
        // (`CR`) the left side does not.
        let (theorem, project) = load_project("example-projects/4WHS", "Full4WHS");
        let equivalence = find_equivalence(&theorem, "H1_1", "H2_0");
        let result = build_invariant_file(&theorem, equivalence, project).unwrap();
        let rendered = crate::writers::easycrypt::render::render_file(&result.file);

        let full_path = format!(
            "{}/testdata/easycrypt/story42/4WHS/Eq_H1_1_H2_0_Invariants.ec",
            env!("CARGO_MANIFEST_DIR")
        );
        let expected = std::fs::read_to_string(&full_path)
            .unwrap_or_else(|e| panic!("failed to read golden file {full_path}: {e}"));
        assert_eq!(rendered, expected, "rendered != {full_path}");
    }

    #[test]
    fn rendering_is_deterministic() {
        let (theorem, project) = load_hybrid0_hybrid1();
        let equivalence = find_equivalence(&theorem, "Hybrid0", "Hybrid1");
        let a = crate::writers::easycrypt::render::render_file(
            &build_invariant_file(&theorem, equivalence, project).unwrap().file,
        );
        let b = crate::writers::easycrypt::render::render_file(
            &build_invariant_file(&theorem, equivalence, project).unwrap().file,
        );
        assert_eq!(a, b);
    }

    #[test]
    fn hybrid0_hybrid1_invariants_file_compiles() {
        let (theorem, project) = load_hybrid0_hybrid1();
        let equivalence = find_equivalence(&theorem, "Hybrid0", "Hybrid1");
        let result = build_invariant_file(&theorem, equivalence, project).unwrap();
        let rendered = crate::writers::easycrypt::render::render_file(&result.file);

        let scratch_dir = std::env::temp_dir().join(format!(
            "domino-easycrypt-story06-{}",
            std::process::id()
        ));
        std::fs::create_dir_all(&scratch_dir).unwrap();
        let file_path = scratch_dir.join(&result.file_name);
        std::fs::write(&file_path, &rendered).unwrap();

        let types_dir = format!("{}/testdata/easycrypt/story02/4WHS", env!("CARGO_MANIFEST_DIR"));
        crate::writers::easycrypt::test_support::assert_compiles_with_paths(
            &[scratch_dir.to_str().unwrap(), &types_dir],
            file_path.to_str().unwrap(),
        );

        let _ = std::fs::remove_dir_all(&scratch_dir);
    }

    #[test]
    fn sort_translation_covers_the_table() {
        assert_eq!(translate_sort(&parse_sort_text("Int"), "f").unwrap(), EcType::Int);
        assert_eq!(translate_sort(&parse_sort_text("Bool"), "f").unwrap(), EcType::Bool);
        assert_eq!(
            translate_sort(&parse_sort_text("Bits_n"), "f").unwrap(),
            EcType::Named("bits_n".to_string())
        );
        assert_eq!(
            translate_sort(&parse_sort_text("(Maybe Bits_n)"), "f").unwrap(),
            EcType::Option(Box::new(EcType::Named("bits_n".to_string())))
        );
        assert_eq!(
            translate_sort(&parse_sort_text("(Array Int (Maybe Bits_n))"), "f").unwrap(),
            EcType::Fmap(
                Box::new(EcType::Int),
                Box::new(EcType::Named("bits_n".to_string()))
            )
        );
        assert_eq!(
            translate_sort(&parse_sort_text("(Tuple2 Int Bool)"), "f").unwrap(),
            EcType::Tuple(vec![EcType::Int, EcType::Bool])
        );
    }

    #[test]
    fn bits_literal_atoms_translate_to_the_types_ec_zero_one_ops() {
        // `Full4WHS`'s own `invariant-H7_1_1_0-H7_1_1_1.smt2` hits this for
        // real: `(let ((zeron <0_n>)) ...)` — `<0_n>` is
        // `src/writers/smt/expr_expr.rs`'s own SMT-text encoding of
        // `BitsLiteral("0", Bits_n)`, not a placeholder.
        assert_eq!(translate_body("<0_n>"), "zero_n");
        assert_eq!(translate_body("<1_n>"), "one_n");
        assert_eq!(translate_body("<1_256>"), "one_256");
        assert_eq!(translate_body("<empty-bitstring>"), "zero");
    }

    #[test]
    fn bits_literal_atom_suffix_is_mangled_dash_to_underscore() {
        assert_eq!(
            translate_bits_literal_atom("<0_key-width>"),
            Some((
                EcExpr::Var("zero_key_width".to_string()),
                EcType::Named("bits_key_width".to_string())
            ))
        );
    }

    // --- acceptance criteria exercised end to end, via `parse_stmts` -----

    fn fresh_state() -> InvariantParserState<'static> {
        InvariantParserState {
            file: "test.smt2".to_string(),
            lookup: Box::leak(Box::new(StateLookup::default())),
            left_record_ty: EcType::Named("Left_state".to_string()),
            right_record_ty: EcType::Named("Right_state".to_string()),
            theorem_consts: &[],
            ops: OpRegistry::default(),
            items: Vec::new(),
            state_relations: Vec::new(),
            skipped: Vec::new(),
        }
    }

    #[test]
    fn define_lemma_is_skipped_with_a_comment_and_reported() {
        let mut state = fresh_state();
        state
            .parse_stmts("(define-lemma foo-Send1 (a b c d) true)")
            .unwrap();
        assert_eq!(state.skipped, vec!["define-lemma foo-Send1".to_string()]);
        assert_eq!(
            state.items,
            vec![EcItem::Comment(
                "skipped `define-lemma foo-Send1` (not translated)".to_string()
            )]
        );
    }

    #[test]
    fn randomness_mapping_defun_is_skipped_with_a_comment_and_reported() {
        let mut state = fresh_state();
        state
            .parse_stmts(
                "(define-fun randomness-mapping-NewKey ((id-0 SampleId)) Bool true)",
            )
            .unwrap();
        assert_eq!(
            state.skipped,
            vec!["define-fun randomness-mapping-NewKey (randomness mapping)".to_string()]
        );
    }

    #[test]
    fn unknown_atom_inside_a_define_state_relation_is_a_hard_error_naming_the_file() {
        let mut state = fresh_state();
        let err = state
            .parse_stmts("(define-state-relation invariant (left right) totally-unknown-thing)")
            .unwrap_err();
        match err {
            InvariantError::Unrecognised { file, .. } => assert_eq!(file, "test.smt2"),
            other => panic!("expected Unrecognised, got {other:?}"),
        }
    }

    #[test]
    fn define_state_relation_binders_must_be_distinct() {
        let mut state = fresh_state();
        let err = state
            .parse_stmts("(define-state-relation foo (a a) true)")
            .unwrap_err();
        assert!(matches!(err, InvariantError::Unsupported { .. }));
    }

    #[test]
    fn define_state_relation_binder_names_are_positional_not_a_fixed_vocabulary() {
        // `Full4WHS`'s own invariants spell these `state-left`/`state-right`
        // instead of `Simple4WHS`'s `left`/`right` — a `define-state-
        // relation`'s two binders are its own local parameter names
        // (positional: first = left side, second = right side), not a
        // fixed required spelling.
        let mut state = fresh_state();
        state
            .parse_stmts("(define-state-relation foo (a b) true)")
            .unwrap();
        assert_eq!(state.state_relations, vec!["Domino_foo".to_string()]);
    }

    #[test]
    fn define_state_relation_dotted_access_works_with_any_binder_spelling() {
        let mut lookup = HashMap::new();
        lookup.insert(
            "left.KX.State".to_string(),
            (field_expr("l", "l_pkg_KX_State"), EcType::Int),
        );
        lookup.insert(
            "right.KX.State".to_string(),
            (field_expr("r", "r_pkg_KX_State"), EcType::Int),
        );
        let mut state = InvariantParserState {
            lookup: Box::leak(Box::new(fields_only(lookup))),
            ..fresh_state()
        };
        state
            .parse_stmts(
                "(define-state-relation foo (state-left state-right) \
                 (= state-left.KX.State state-right.KX.State))",
            )
            .unwrap();
        let EcItem::OpDef { body, .. } = &state.items[0] else {
            panic!("expected an op def");
        };
        assert_eq!(
            render_expr(body),
            "l.`l_pkg_KX_State = r.`r_pkg_KX_State"
        );
    }

    // --- acceptance criteria exercised against real target projects ------

    #[test]
    fn real_hybrid3_ideal_hybrid3_share_a_composition_but_get_non_colliding_fields() {
        let (theorem, project) = load_hybrid0_hybrid1();
        let equivalence = find_equivalence(&theorem, "Real_Hybrid3", "Ideal_Hybrid3");
        let result = build_invariant_file(&theorem, equivalence, project).unwrap();

        assert_eq!(result.left_state_type, "Real_Hybrid3_state");
        assert_eq!(result.right_state_type, "Ideal_Hybrid3_state");

        let record_fields = |type_name: &str| {
            result
                .file
                .items
                .iter()
                .find_map(|item| match item {
                    EcItem::Record { name, fields } if name == type_name => Some(fields),
                    _ => None,
                })
                .unwrap_or_else(|| panic!("no record type `{type_name}`"))
        };
        let left_fields = record_fields("Real_Hybrid3_state");
        let right_fields = record_fields("Ideal_Hybrid3_state");
        let left_names: std::collections::HashSet<_> =
            left_fields.iter().map(|(n, _)| n.clone()).collect();
        let right_names: std::collections::HashSet<_> =
            right_fields.iter().map(|(n, _)| n.clone()).collect();
        assert!(
            left_names.is_disjoint(&right_names),
            "left/right record fields must not collide: {left_names:?} vs {right_names:?}"
        );

        // Both sides instantiate the same `Hybrid2` composition (as
        // `Real_Hybrid3`/`Ideal_Hybrid3`), so every left field's `l_`-
        // stripped name reappears as a right field under `r_` — confirming
        // the "share a composition" case the story's own acceptance
        // criterion names, not just "some non-colliding fields".
        let stripped_left: std::collections::HashSet<_> = left_names
            .iter()
            .map(|n| n.strip_prefix("l_").unwrap().to_string())
            .collect();
        let stripped_right: std::collections::HashSet<_> = right_names
            .iter()
            .map(|n| n.strip_prefix("r_").unwrap().to_string())
            .collect();
        assert_eq!(stripped_left, stripped_right);
    }

    #[test]
    fn real_hybrid3_ideal_hybrid3_params_inv_states_literals_directly() {
        let (theorem, project) = load_hybrid0_hybrid1();
        let equivalence = find_equivalence(&theorem, "Real_Hybrid3", "Ideal_Hybrid3");
        let result = build_invariant_file(&theorem, equivalence, project).unwrap();

        let params_inv = result
            .file
            .items
            .iter()
            .find_map(|item| match item {
                EcItem::OpDef { name, body, .. } if name == "params_inv" => Some(body),
                _ => None,
            })
            .expect("params_inv op");
        let rendered = crate::writers::easycrypt::render::render_expr(params_inv);

        // `Real_Hybrid3` binds `Hybrid2`'s idealization bit `bprf` to the
        // literal `true` (its own `b` to `false`); `Ideal_Hybrid3` binds
        // `bprf` to `true` too (both hops are on the "PRF is real" side of
        // the reduction) — see `Simple4WHS.ssp`'s `instance Real_Hybrid3`/
        // `instance Ideal_Hybrid3` blocks. Both resolve to literals on both
        // sides, so `params_inv` states each side's value directly rather
        // than equating them.
        assert!(rendered.contains("l_pkg_Prf_b = true"));
        assert!(rendered.contains("r_pkg_Prf_b = true"));
    }

    // --- story 42: the synthetic project `testdata/easycrypt/story42/params` --
    //
    // `L ~ R` (compositions `Left` / `Right`), theorem constants `x y z w`:
    //
    // | Left instance (package) | binding        | Right instance (package) | binding          |
    // |-------------------------|----------------|--------------------------|------------------|
    // | `Store` (`Ctr`)         | `b: y`         | `Keep` (`CtrToo`)        | `flag: y`        |
    // | `OnlyL` (`Ctr`)         | `b: true`      | `OnlyR` (`CtrToo`)       | `flag: false`    |
    // | `Front` (`Pass`, no state) | `b: x`      | `Front` (`Pass`)         | `b: x`           |
    // | `T` (`Twin`)            | `b1: z, b2: z` | `T` (`Twin`)             | `b1: w, b2: true`|
    //
    // Theorem `Params` holds `L ~ R`. Theorem `ParamsBad` holds `L_bad ~
    // R_bad`, the same pair with an invariant comparing `Store` with `Keep`,
    // so that `Params` still exports as a whole. Theorem `ParamsWidths`
    // holds `N ~ W`, two instances of package `Key` whose state is
    // `Bits(n)` for two different `n`. Theorem `ParamsClash` holds `C1 ~
    // C2`, both of composition `Clash`, where instance `T_b1` (with state)
    // and parameter `b1` of instance `T` both name the field `l_pkg_T_b1`.

    fn load_project(dir: &str, theorem_name: &str) -> (
        crate::theorem::Theorem<'static>,
        &'static crate::project::DirectoryProject<'static>,
    ) {
        use crate::project::{DirectoryFiles, DirectoryProject, Project};
        use crate::transforms::theorem_transforms::EasyCryptTransform;
        use crate::transforms::TheoremTransform;

        let files: &'static DirectoryFiles =
            Box::leak(Box::new(DirectoryFiles::load(std::path::Path::new(dir)).unwrap()));
        let project: &'static DirectoryProject = Box::leak(Box::new(
            DirectoryProject::load(std::path::PathBuf::from(dir), files).unwrap(),
        ));
        let theorem = project.get_theorem(theorem_name).unwrap();
        let (theorem, _auxs) = EasyCryptTransform.transform_theorem(theorem).unwrap();
        (theorem, project)
    }

    const PARAMS_PROJECT: &str = "testdata/easycrypt/story42/params";

    fn params_project_file(
        theorem_name: &str,
        left: &str,
        right: &str,
    ) -> Result<String, EcExportError> {
        let (theorem, project) = load_project(PARAMS_PROJECT, theorem_name);
        let equivalence = find_equivalence(&theorem, left, right);
        let result = build_invariant_file(&theorem, equivalence, project)?;
        Ok(crate::writers::easycrypt::render::render_file(&result.file))
    }

    /// The text of one top-level item of a rendered file, from its first
    /// line (`op <name> `, `type <name> `) to its closing `.`.
    fn item_text<'a>(rendered: &'a str, head: &str) -> &'a str {
        let start = rendered
            .find(&format!("\n{head} "))
            .unwrap_or_else(|| panic!("no `{head}` in:\n{rendered}"))
            + 1;
        let len = rendered[start..].find(".\n").expect("item ends with `.`") + 1;
        &rendered[start..start + len]
    }

    fn params_inv_text(rendered: &str) -> &str {
        item_text(rendered, "op params_inv")
    }

    #[test]
    fn each_package_with_state_gets_one_state_record_type_shared_by_both_sides() {
        let rendered = params_project_file("Params", "L", "R").unwrap();
        assert_eq!(
            item_text(&rendered, "type Ctr_pkgstate"),
            "type Ctr_pkgstate = {\n  Ctr_ctr : int\n}."
        );
        assert_eq!(
            item_text(&rendered, "type CtrToo_pkgstate"),
            "type CtrToo_pkgstate = {\n  CtrToo_ctr : int\n}."
        );
        assert_eq!(rendered.matches("type Twin_pkgstate").count(), 1, "{rendered}");
        assert!(!rendered.contains("Pass_pkgstate"), "{rendered}");
    }

    #[test]
    fn the_game_record_nests_one_package_record_per_instance_with_state_then_the_parameters() {
        let rendered = params_project_file("Params", "L", "R").unwrap();
        assert_eq!(
            item_text(&rendered, "type L_state"),
            "type L_state = {\n  \
               l_pkg_Store : Ctr_pkgstate;\n  \
               l_pkg_OnlyL : Ctr_pkgstate;\n  \
               l_pkg_T : Twin_pkgstate;\n  \
               l_pkg_Store_b : bool;\n  \
               l_pkg_OnlyL_b : bool;\n  \
               l_pkg_Front_b : bool;\n  \
               l_pkg_T_b1 : bool;\n  \
               l_pkg_T_b2 : bool;\n  \
               l_abort_flag : bool\n\
             }."
        );
    }

    #[test]
    fn a_dotted_state_atom_is_a_projection_of_the_package_record() {
        let rendered = params_project_file("Params", "L", "R").unwrap();
        assert_eq!(
            item_text(&rendered, "op Domino_dotted_state"),
            "op Domino_dotted_state (l : L_state) (r : R_state) : bool =\n  \
               l.`l_pkg_Store.`Ctr_ctr = r.`r_pkg_Keep.`CtrToo_ctr."
        );
    }

    #[test]
    fn a_dotted_parameter_atom_is_the_game_record_parameter_field() {
        let rendered = params_project_file("Params", "L", "R").unwrap();
        assert_eq!(
            item_text(&rendered, "op Domino_dotted_param"),
            "op Domino_dotted_param (l : L_state) (r : R_state) : bool =\n  \
               l.`l_pkg_Front_b = r.`r_pkg_Front_b."
        );
    }

    #[test]
    fn a_whole_package_equality_with_state_is_one_record_equality_without_parameters() {
        let rendered = params_project_file("Params", "L", "R").unwrap();
        assert_eq!(
            item_text(&rendered, "op Domino_same_package_with_state"),
            "op Domino_same_package_with_state (l : L_state) (r : R_state) : bool =\n  \
               l.`l_pkg_T = r.`r_pkg_T."
        );
    }

    #[test]
    fn a_whole_package_equality_between_stateless_instances_is_true() {
        let rendered = params_project_file("Params", "L", "R").unwrap();
        assert_eq!(
            item_text(&rendered, "op Domino_same_package_stateless"),
            "op Domino_same_package_stateless (l : L_state) (r : R_state) : bool =\n  \
               true."
        );
    }

    #[test]
    fn a_whole_package_equality_between_different_packages_is_a_hard_error() {
        let err = params_project_file("ParamsBad", "L_bad", "R_bad").unwrap_err();
        let EcExportError::Invariant(InvariantError::PackageMismatch {
            left_instance,
            left_package,
            right_instance,
            right_package,
            ..
        }) = &err
        else {
            panic!("expected PackageMismatch, got {err:?}");
        };
        assert_eq!(
            (left_instance.as_str(), left_package.as_str()),
            ("Store", "Ctr")
        );
        assert_eq!(
            (right_instance.as_str(), right_package.as_str()),
            ("Keep", "CtrToo")
        );
        let message = err.to_string();
        assert!(message.contains("Ctr") && message.contains("CtrToo"), "{message}");
    }

    #[test]
    fn instances_of_one_package_with_different_state_types_are_a_hard_error() {
        // `ParamsWidths`: `Key`'s state is `k: Bits(n)`, with `n` bound to
        // `narrow` on the left and `wide` on the right.
        let err = params_project_file("ParamsWidths", "N", "W").unwrap_err();
        assert!(
            matches!(
                &err,
                EcExportError::Invariant(InvariantError::PackageStateMismatch { package })
                    if package == "Key"
            ),
            "{err:?}"
        );
    }

    #[test]
    fn two_record_fields_with_one_name_are_a_hard_error() {
        let err = params_project_file("ParamsClash", "C1", "C2").unwrap_err();
        assert!(
            matches!(
                &err,
                EcExportError::Invariant(InvariantError::FieldCollision { field })
                    if field == "l_pkg_T_b1"
            ),
            "{err:?}"
        );
    }

    #[test]
    fn params_inv_pins_a_literal_of_an_instance_only_on_the_left() {
        let rendered = params_project_file("Params", "L", "R").unwrap();
        assert!(
            params_inv_text(&rendered).contains("l.`l_pkg_OnlyL_b = true"),
            "{rendered}"
        );
    }

    #[test]
    fn params_inv_pins_a_literal_of_an_instance_only_on_the_right() {
        let rendered = params_project_file("Params", "L", "R").unwrap();
        assert!(
            params_inv_text(&rendered).contains("r.`r_pkg_OnlyR_flag = false"),
            "{rendered}"
        );
    }

    #[test]
    fn params_inv_equates_one_constant_across_different_instance_and_parameter_names() {
        let rendered = params_project_file("Params", "L", "R").unwrap();
        assert!(
            params_inv_text(&rendered).contains("l.`l_pkg_Store_b = r.`r_pkg_Keep_flag"),
            "{rendered}"
        );
    }

    #[test]
    fn params_inv_chains_one_constant_bound_twice_on_the_same_side() {
        let rendered = params_project_file("Params", "L", "R").unwrap();
        assert!(
            params_inv_text(&rendered).contains("l.`l_pkg_T_b1 = l.`l_pkg_T_b2"),
            "{rendered}"
        );
    }

    #[test]
    fn params_inv_says_nothing_about_the_only_parameter_bound_to_its_constant() {
        // `w` is bound only to `R`'s `T.b1`.
        let rendered = params_project_file("Params", "L", "R").unwrap();
        assert!(!params_inv_text(&rendered).contains("r_pkg_T_b1"), "{rendered}");
    }

    #[test]
    fn params_inv_states_its_conjuncts_in_field_collection_order() {
        let rendered = params_project_file("Params", "L", "R").unwrap();
        assert_eq!(
            params_inv_text(&rendered),
            "op params_inv (l : L_state) (r : R_state) : bool =\n     \
                  l.`l_pkg_OnlyL_b = true\n  \
               /\\ l.`l_pkg_T_b1 = l.`l_pkg_T_b2\n  \
               /\\ l.`l_pkg_Store_b = r.`r_pkg_Keep_flag\n  \
               /\\ r.`r_pkg_OnlyR_flag = false\n  \
               /\\ l.`l_pkg_Front_b = r.`r_pkg_Front_b\n  \
               /\\ r.`r_pkg_T_b2 = true."
        );
    }

    /// The conjuncts of a `/\` chain, `[]` for `true`.
    fn conjuncts_of(e: &EcExpr) -> Vec<&EcExpr> {
        match e {
            EcExpr::Bool(true) => vec![],
            EcExpr::Binop {
                op: EcBinop::And,
                lhs,
                rhs,
            } => {
                let mut out = conjuncts_of(lhs);
                out.extend(conjuncts_of(rhs));
                out
            }
            other => vec![other],
        }
    }

    /// Story 42 §4.2: in every equivalence of 4WHS, every parameter field of
    /// either game record is pinned to its literal, or equated (as one
    /// connected chain) with every other field bound to the same theorem
    /// constant, or is the only field bound to its constant and is not
    /// mentioned. Also, `params_inv` states nothing else. The expectation is
    /// computed from the game instances, not from `params_inv`.
    #[test]
    fn params_inv_states_every_parameter_of_every_4whs_equivalence() {
        use std::collections::BTreeMap;

        enum Expected {
            Literal(String),
            Const(String),
        }

        for theorem_name in ["Simple4WHS", "Full4WHS"] {
            let (theorem, project) = load_project("example-projects/4WHS", theorem_name);
            for hop in &theorem.game_hops {
                let crate::gamehops::GameHop::Equivalence(equivalence) = hop else {
                    continue;
                };
                let hop_name = format!(
                    "{theorem_name} {} ~ {}",
                    equivalence.left_name(),
                    equivalence.right_name()
                );

                // Expectation, from the instances: field text -> binding.
                let mut expected: Vec<(String, Expected)> = Vec::new();
                for (game_name, var, prefix) in [
                    (equivalence.left_name(), "l", "l_"),
                    (equivalence.right_name(), "r", "r_"),
                ] {
                    let game_inst = theorem.find_game_instance(game_name).unwrap();
                    for inst in &game_inst.game().pkgs {
                        for (param, ty, _) in &inst.pkg.params {
                            if !package::param_needs_var(&inst.pkg, param, ty) {
                                continue;
                            }
                            let mangled = Names::new().mangle(NameKind::Var, param).unwrap();
                            let field = format!("{var}.`{prefix}pkg_{}_{mangled}", inst.name());
                            let binding = param_assignment(inst, param)
                                .and_then(resolve_expr_value)
                                .unwrap_or_else(|| panic!("{hop_name}: {field} unresolved"));
                            expected.push((
                                field,
                                match binding {
                                    ParamValue::Literal(lit) => Expected::Literal(lit),
                                    ParamValue::TheoremConst(c) => Expected::Const(c),
                                },
                            ));
                        }
                    }
                }

                // What `params_inv` says: one `(lhs, rhs)` per conjunct.
                let result = build_invariant_file(&theorem, equivalence, project)
                    .unwrap_or_else(|e| panic!("{hop_name}: {e}"));
                let body = result
                    .file
                    .items
                    .iter()
                    .find_map(|item| match item {
                        EcItem::OpDef { name, body, .. } if name == "params_inv" => Some(body),
                        _ => None,
                    })
                    .unwrap();
                let stated: Vec<(String, String)> = conjuncts_of(body)
                    .into_iter()
                    .map(|c| match c {
                        EcExpr::Binop {
                            op: EcBinop::Eq,
                            lhs,
                            rhs,
                        } => (render_expr(lhs), render_expr(rhs)),
                        other => panic!("{hop_name}: unexpected conjunct {}", render_expr(other)),
                    })
                    .collect();

                let mut by_const: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
                for (field, binding) in &expected {
                    match binding {
                        Expected::Literal(lit) => assert!(
                            stated.contains(&(field.clone(), lit.clone())),
                            "{hop_name}: {field} is not pinned to {lit}: {stated:?}"
                        ),
                        Expected::Const(c) => by_const.entry(c).or_default().push(field),
                    }
                }

                let mut accounted = 0;
                for (constant, fields) in &by_const {
                    let in_group = |f: &String| fields.contains(&f.as_str());
                    let equalities: Vec<&(String, String)> = stated
                        .iter()
                        .filter(|(a, b)| in_group(a) && in_group(b))
                        .collect();
                    accounted += equalities.len();
                    if fields.len() == 1 {
                        assert!(
                            stated.iter().all(|(a, b)| a != fields[0] && b != fields[0]),
                            "{hop_name}: {} is the only field bound to {constant}: {stated:?}",
                            fields[0]
                        );
                        continue;
                    }
                    // Every field bound to `constant` is reached from the first.
                    let mut reached = vec![fields[0]];
                    loop {
                        let before = reached.len();
                        for (a, b) in &equalities {
                            if reached.contains(&a.as_str()) && !reached.contains(&b.as_str()) {
                                reached.push(b);
                            } else if reached.contains(&b.as_str()) && !reached.contains(&a.as_str()) {
                                reached.push(a);
                            }
                        }
                        if reached.len() == before {
                            break;
                        }
                    }
                    for field in fields {
                        assert!(
                            reached.contains(field),
                            "{hop_name}: {field} is not equated with the other fields bound to {constant}: {stated:?}"
                        );
                    }
                }
                let literals = expected
                    .iter()
                    .filter(|(_, b)| matches!(b, Expected::Literal(_)))
                    .count();
                assert_eq!(
                    stated.len(),
                    literals + accounted,
                    "{hop_name}: params_inv states something else: {stated:?}"
                );
            }
        }
    }

    #[test]
    fn the_params_project_invariant_file_compiles() {
        let (theorem, project) = load_project(PARAMS_PROJECT, "Params");
        let equivalence = find_equivalence(&theorem, "L", "R");
        let result = build_invariant_file(&theorem, equivalence, project).unwrap();
        let rendered = crate::writers::easycrypt::render::render_file(&result.file);

        let scratch_dir = std::env::temp_dir().join(format!(
            "domino-easycrypt-story42-{}",
            std::process::id()
        ));
        std::fs::create_dir_all(&scratch_dir).unwrap();
        let file_path = scratch_dir.join(&result.file_name);
        std::fs::write(&file_path, &rendered).unwrap();
        std::fs::write(
            scratch_dir.join("Types.ec"),
            "require import AllCore Distr FMap Int IntDiv.\n",
        )
        .unwrap();
        crate::writers::easycrypt::test_support::assert_compiles_with_paths(
            &[scratch_dir.to_str().unwrap()],
            file_path.to_str().unwrap(),
        );
        let _ = std::fs::remove_dir_all(&scratch_dir);
    }

    #[test]
    fn hybrid1_hybrid2_multi_file_invariant_skips_randomness_mapping_defuns() {
        let (theorem, project) = load_hybrid0_hybrid1();
        let equivalence = find_equivalence(&theorem, "Hybrid1", "Hybrid2");
        let result = build_invariant_file(&theorem, equivalence, project).unwrap();
        assert!(
            result
                .skipped
                .iter()
                .any(|s| s.contains("randomness mapping")),
            "expected at least one skipped randomness-mapping define-fun, got {:?}",
            result.skipped
        );
    }
}
