// SPDX-License-Identifier: MIT OR Apache-2.0

//! Building `Eq_<Left>_<Right>_Invariants.ec`
//! (`docs/stories/easycrypt/06-invariant-translation.md`): translating an
//! equivalence's hand-written SMT-LIB invariant (`Equivalence::invariants()`)
//! into a pair of flat game-state records plus a closed set of EasyCrypt
//! operators, one per `define-fun`/`define-state-relation` in the source
//! file(s), folded into `op inv`.
//!
//! The SMT-LIB text is parsed with the existing `src/util/smtparser`
//! (`smt.pest`) grammar via its `SmtParser` trait; this module supplies its
//! own minimal generic s-expression type ([`Sexp`]) as that trait's
//! `Expr`/`Stmt`, and does the real translation eagerly inside the trait's
//! `handle_definefun`/`handle_define_state_relation` overrides.

use std::collections::HashMap;

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

/// One translated invariant file's output: the two flat game-state
/// records, one `op` per translated `define-fun`/`define-state-relation`
/// (in file order), `params_inv`, and the assembled `inv`.
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
    let mut lookup: HashMap<String, (EcExpr, EcType)> = HashMap::new();
    let left_side = build_side_record(left_game_inst, "left", "l", "l_", &mut lookup)?;
    let right_side = build_side_record(right_game_inst, "right", "r", "r_", &mut lookup)?;

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

    let params_inv_expr = build_params_inv(left_game_inst, right_game_inst, &lookup);

    let mut items = vec![
        EcItem::Record {
            name: left_side.record_type_name.clone(),
            fields: left_side.fields.clone(),
        },
        EcItem::Record {
            name: right_side.record_type_name.clone(),
            fields: right_side.fields.clone(),
        },
    ];
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

// --- the game-state records (§3.1) -----------------------------------

struct SideRecord {
    record_type_name: String,
    fields: Vec<(String, EcType)>,
    abort_field: String,
}

/// Mangles one `(instance, raw field/param name)` pair into its final record
/// field, pushing it onto `fields` and indexing it into `combined_lookup` —
/// shared by [`build_side_record`]'s state-field and param-field loops,
/// which otherwise differ only in *which* list of `(String, Type,
/// SourceSpan)` they walk and the [`package::param_needs_var`] filter the
/// caller already applied before calling this.
#[allow(clippy::too_many_arguments)]
fn add_side_field(
    inst: &PackageInstance,
    name: &str,
    ty: &Type,
    span: SourceSpan,
    binder: &str,
    op_param: &str,
    field_ns_prefix: &str,
    names: &mut Names,
    fields: &mut Vec<(String, EcType)>,
    combined_lookup: &mut HashMap<String, (EcExpr, EcType)>,
) -> Result<(), EcExportError> {
    let mangled = names.mangle(NameKind::Var, name)?;
    let ec_ty = translate_type(ty, span)?;
    let final_name = format!("{field_ns_prefix}pkg_{}_{mangled}", inst.name());
    fields.push((final_name.clone(), ec_ty.clone()));
    let ec_expr = EcExpr::Field {
        expr: Box::new(EcExpr::Var(op_param.to_string())),
        field: final_name,
    };
    combined_lookup.insert(format!("{binder}.{}.{name}", inst.name()), (ec_expr, ec_ty));
    Ok(())
}

/// One flat record for `game_inst`'s side of the equivalence: one field per
/// `(instance, state field)` in `ordered_pkgs_idx()` order, then one field
/// per qualifying package parameter ([`package::param_needs_var`] — the
/// same rule that gives that parameter a persistent module `var` in
/// story 03/04's own package rendering), then `abort_flag`. Every field
/// name is namespaced `{field_ns_prefix}pkg_{instance}_{mangled field}`
/// (or `{field_ns_prefix}abort_flag`); `combined_lookup` is populated with
/// `{binder}.{instance}.{raw field/param name}` -> the field's already-
/// built `EcExpr::Field`/`EcType`, both for resolving a `.smt2` dotted
/// atom (`left.KX.State`) and for `params_inv`'s own lookups (§3.3).
fn build_side_record(
    game_inst: &GameInstance,
    binder: &str,
    op_param: &str,
    field_ns_prefix: &str,
    combined_lookup: &mut HashMap<String, (EcExpr, EcType)>,
) -> Result<SideRecord, EcExportError> {
    let mut fields = Vec::new();

    for &idx in &game_inst.game().ordered_pkgs_idx() {
        let inst: &PackageInstance = &game_inst.game().pkgs[idx];
        let mut names = Names::new();

        for (name, ty, span) in &inst.pkg.state {
            add_side_field(
                inst, name, ty, *span, binder, op_param, field_ns_prefix, &mut names,
                &mut fields, combined_lookup,
            )?;
        }

        for (name, ty, span) in &inst.pkg.params {
            if !package::param_needs_var(&inst.pkg, name, ty) {
                continue;
            }
            add_side_field(
                inst, name, ty, *span, binder, op_param, field_ns_prefix, &mut names,
                &mut fields, combined_lookup,
            )?;
        }
    }

    let abort_field = format!("{field_ns_prefix}abort_flag");
    fields.push((abort_field.clone(), EcType::Bool));

    Ok(SideRecord {
        record_type_name: format!("{}_state", game_inst.name()),
        fields,
        abort_field,
    })
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

fn fold_and(exprs: Vec<EcExpr>) -> EcExpr {
    let mut it = exprs.into_iter();
    let Some(first) = it.next() else {
        return EcExpr::Bool(true);
    };
    it.fold(first, |acc, e| EcExpr::Binop {
        op: EcBinop::And,
        lhs: Box::new(acc),
        rhs: Box::new(e),
    })
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

/// §3.3: relates the idealization bits and value-integer parameters of
/// every package instance present (by raw name) on both sides. Instance
/// correspondence is by matching raw `PackageInstance` name across the two
/// sides' compositions — correct for every target project, where an
/// equivalence's two sides always reuse the same instance names (whether
/// or not they share a composition).
fn build_params_inv(
    left_game_inst: &GameInstance,
    right_game_inst: &GameInstance,
    lookup: &HashMap<String, (EcExpr, EcType)>,
) -> EcExpr {
    let mut conjuncts = Vec::new();

    for left_inst in &left_game_inst.game().pkgs {
        let Some(right_inst) = right_game_inst
            .game()
            .pkgs
            .iter()
            .find(|r| r.name == left_inst.name)
        else {
            continue;
        };

        for (pname, pty, _) in &left_inst.pkg.params {
            if !package::param_needs_var(&left_inst.pkg, pname, pty) {
                continue;
            }
            let Some((_, rty, _)) = right_inst.pkg.params.iter().find(|(n, _, _)| n == pname)
            else {
                continue;
            };
            if !package::param_needs_var(&right_inst.pkg, pname, rty) {
                continue;
            }

            let Some(left_expr) = param_assignment(left_inst, pname) else {
                continue;
            };
            let Some(right_expr) = param_assignment(right_inst, pname) else {
                continue;
            };

            let Some((left_field, _)) =
                lookup.get(&format!("left.{}.{pname}", left_inst.name()))
            else {
                continue;
            };
            let Some((right_field, _)) =
                lookup.get(&format!("right.{}.{pname}", right_inst.name()))
            else {
                continue;
            };

            match (resolve_expr_value(left_expr), resolve_expr_value(right_expr)) {
                (Some(ParamValue::TheoremConst(a)), Some(ParamValue::TheoremConst(b)))
                    if a == b =>
                {
                    conjuncts.push(eq_expr(left_field.clone(), right_field.clone()));
                }
                (left_val, right_val) => {
                    if let Some(ParamValue::Literal(lit)) = left_val {
                        conjuncts.push(eq_expr(left_field.clone(), literal_expr(&lit)));
                    }
                    if let Some(ParamValue::Literal(lit)) = right_val {
                        conjuncts.push(eq_expr(right_field.clone(), literal_expr(&lit)));
                    }
                }
            }
        }
    }

    fold_and(conjuncts)
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
    lookup: &'a HashMap<String, (EcExpr, EcType)>,
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
                    if let Some((expr, ty)) = self.lookup.get(&format!("{prefix}.{rest}")) {
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
        if let Some((expr, ty)) = self.lookup.get(a) {
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
            result = EcExpr::Let {
                name: mangled,
                value: Box::new(value_expr),
                body: Box::new(result),
            };
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
        let mut it = exprs.into_iter();
        let first = it.next().expect("checked non-empty above");
        let folded = it.fold(first, |acc, e| EcExpr::Binop {
            op,
            lhs: Box::new(acc),
            rhs: Box::new(e),
        });
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
    /// this definition's own left/right record parameter: an SMT atom
    /// naming an entire package instance's state, not one field of it.
    /// `Full4WHS`'s invariants do this for real (`(= state-left.KX
    /// state-right.KX)`), comparing a whole package instance's state in
    /// one `=` rather than field-by-field — `self.lookup` only ever holds
    /// per-`(instance, field)` entries (`build_side_record`/
    /// `add_side_field`), so there is no single value this atom could
    /// resolve to on its own; [`Self::translate_eq_n`] special-cases the
    /// two-argument `=` form instead, expanding it into a conjunction over
    /// every field both sides share (see
    /// [`Self::translate_instance_equality`]).
    ///
    /// Returns `("left"|"right", instance_name)`. Never confused with a
    /// genuine field access (`left.KX.State`, three segments): `instance`
    /// containing a further `.` short-circuits this to `None` immediately.
    fn resolve_instance_atom<'b>(&self, a: &'b str, locals: &Locals) -> Option<(&'static str, &'b str)> {
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
        // Not a whole-instance reference if `a` itself is already a known
        // field (shouldn't happen — field keys always have a third
        // segment — but guards against a pathological instance name
        // containing no further structure) or if this instance has no
        // known fields at all (an unrelated/unknown atom, left to the
        // normal `unrecognised` error path).
        if self.lookup.contains_key(&format!("{prefix}.{instance}")) {
            return None;
        }
        let field_prefix = format!("{prefix}.{instance}.");
        if !self.lookup.keys().any(|k| k.starts_with(&field_prefix)) {
            return None;
        }
        Some((prefix, instance))
    }

    /// Expands a whole-package-state equality (`(= state-left.KX
    /// state-right.KX)`) into a conjunction of per-field equalities, one
    /// per raw field/param name present in `self.lookup` under *both*
    /// `{left_prefix}.{left_instance}.` and `{right_prefix}.{right_instance}.`
    /// (sorted for determinism — matches this story's implementation
    /// report §9 sketch). A field present on only one side is silently
    /// skipped, mirroring [`build_params_inv`]'s own asymmetric-field
    /// tolerance rather than erroring.
    fn translate_instance_equality(
        &self,
        left_prefix: &str,
        left_instance: &str,
        right_prefix: &str,
        right_instance: &str,
        whole: &Sexp,
    ) -> Result<(EcExpr, EcType), InvariantError> {
        let left_field_prefix = format!("{left_prefix}.{left_instance}.");
        let right_field_prefix = format!("{right_prefix}.{right_instance}.");

        let mut left_fields: Vec<&str> = self
            .lookup
            .keys()
            .filter_map(|k| k.strip_prefix(left_field_prefix.as_str()))
            .collect();
        left_fields.sort_unstable();

        let mut conjuncts = Vec::new();
        for field in left_fields {
            let right_key = format!("{right_field_prefix}{field}");
            let Some((right_expr, _)) = self.lookup.get(&right_key) else {
                continue;
            };
            let (left_expr, _) = self
                .lookup
                .get(&format!("{left_field_prefix}{field}"))
                .expect("just collected this key from self.lookup itself");
            conjuncts.push(eq_expr(left_expr.clone(), right_expr.clone()));
        }

        if conjuncts.is_empty() {
            return Err(self.unsupported(format!(
                "whole-package-state equality `{whole}` between `{left_instance}` and `{right_instance}` has no fields in common"
            )));
        }

        Ok((fold_and(conjuncts), EcType::Bool))
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
            if let (Some((lp, linst)), Some((rp, rinst))) = (
                self.resolve_instance_atom(a, locals),
                self.resolve_instance_atom(b, locals),
            ) {
                return self.translate_instance_equality(lp, linst, rp, rinst, whole);
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
    lookup: &'a HashMap<String, (EcExpr, EcType)>,
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
        let mut tctx = TCtx {
            file: "test.smt2".to_string(),
            lookup,
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
            "l.`l_pkg_KX_State = None<:int>"
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
            "None<:bits_n>"
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
            lookup: &HashMap::new(),
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
            lookup: &HashMap::new(),
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
        use crate::transforms::theorem_transforms::EquivalenceTransform;
        use crate::transforms::TheoremTransform;

        let dir = "example-projects/4WHS";
        let files: &'static DirectoryFiles =
            Box::leak(Box::new(DirectoryFiles::load(std::path::Path::new(dir)).unwrap()));
        let project: &'static DirectoryProject = Box::leak(Box::new(
            DirectoryProject::load(std::path::PathBuf::from(dir), files).unwrap(),
        ));
        let theorem = project.get_theorem("Simple4WHS").unwrap();
        let (theorem, _auxs) = EquivalenceTransform.transform_theorem(theorem).unwrap();
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
            lookup: Box::leak(Box::new(HashMap::new())),
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
            lookup: Box::leak(Box::new(lookup)),
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

    #[test]
    fn whole_package_state_equality_expands_to_a_field_by_field_conjunction() {
        // `Full4WHS`'s own `invariant-KX-H1_0.smt2` does exactly this:
        // `(= state-left.KX state-right.KX)`, comparing a whole package
        // instance's state in one `=` rather than field-by-field.
        let mut lookup = HashMap::new();
        lookup.insert(
            "left.KX.State".to_string(),
            (field_expr("l", "l_pkg_KX_State"), EcType::Int),
        );
        lookup.insert(
            "right.KX.State".to_string(),
            (field_expr("r", "r_pkg_KX_State"), EcType::Int),
        );
        lookup.insert(
            "left.KX.LTK".to_string(),
            (field_expr("l", "l_pkg_KX_LTK"), EcType::Int),
        );
        lookup.insert(
            "right.KX.LTK".to_string(),
            (field_expr("r", "r_pkg_KX_LTK"), EcType::Int),
        );
        let mut state = InvariantParserState {
            lookup: Box::leak(Box::new(lookup)),
            ..fresh_state()
        };
        state
            .parse_stmts(
                "(define-state-relation foo (state-left state-right) \
                 (= state-left.KX state-right.KX))",
            )
            .unwrap();
        let EcItem::OpDef { body, .. } = &state.items[0] else {
            panic!("expected an op def");
        };
        assert_eq!(
            render_expr(body),
            "l.`l_pkg_KX_LTK = r.`r_pkg_KX_LTK /\\ l.`l_pkg_KX_State = r.`r_pkg_KX_State"
        );
    }

    #[test]
    fn whole_package_state_equality_skips_fields_present_on_only_one_side() {
        let mut lookup = HashMap::new();
        lookup.insert(
            "left.KX.State".to_string(),
            (field_expr("l", "l_pkg_KX_State"), EcType::Int),
        );
        lookup.insert(
            "right.KX.State".to_string(),
            (field_expr("r", "r_pkg_KX_State"), EcType::Int),
        );
        lookup.insert(
            "left.KX.Extra".to_string(),
            (field_expr("l", "l_pkg_KX_Extra"), EcType::Int),
        );
        let mut state = InvariantParserState {
            lookup: Box::leak(Box::new(lookup)),
            ..fresh_state()
        };
        state
            .parse_stmts(
                "(define-state-relation foo (state-left state-right) \
                 (= state-left.KX state-right.KX))",
            )
            .unwrap();
        let EcItem::OpDef { body, .. } = &state.items[0] else {
            panic!("expected an op def");
        };
        assert_eq!(render_expr(body), "l.`l_pkg_KX_State = r.`r_pkg_KX_State");
    }

    #[test]
    fn instance_level_equality_with_no_shared_fields_is_a_hard_error() {
        let mut lookup = HashMap::new();
        lookup.insert(
            "left.KX.State".to_string(),
            (field_expr("l", "l_pkg_KX_State"), EcType::Int),
        );
        lookup.insert(
            "right.KX.Other".to_string(),
            (field_expr("r", "r_pkg_KX_Other"), EcType::Int),
        );
        let mut state = InvariantParserState {
            lookup: Box::leak(Box::new(lookup)),
            ..fresh_state()
        };
        let err = state
            .parse_stmts(
                "(define-state-relation foo (state-left state-right) \
                 (= state-left.KX state-right.KX))",
            )
            .unwrap_err();
        assert!(matches!(err, InvariantError::Unsupported { .. }));
    }

    // --- acceptance criteria exercised against real target projects ------

    #[test]
    fn real_hybrid3_ideal_hybrid3_share_a_composition_but_get_non_colliding_fields() {
        let (theorem, project) = load_hybrid0_hybrid1();
        let equivalence = find_equivalence(&theorem, "Real_Hybrid3", "Ideal_Hybrid3");
        let result = build_invariant_file(&theorem, equivalence, project).unwrap();

        assert_eq!(result.left_state_type, "Real_Hybrid3_state");
        assert_eq!(result.right_state_type, "Ideal_Hybrid3_state");

        let EcItem::Record { fields: left_fields, .. } = &result.file.items[0] else {
            panic!("expected the left record first");
        };
        let EcItem::Record { fields: right_fields, .. } = &result.file.items[1] else {
            panic!("expected the right record second");
        };
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
