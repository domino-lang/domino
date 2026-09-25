// SPDX-License-Identifier: MIT OR Apache-2.0

//! Translating Domino packages into EasyCrypt package-variant modules
//! (`docs/stories/easycrypt/03-package-variants.md`).
//!
//! A **variant** is a package specialised to one assignment of its integer
//! and function parameters (boolean parameters are not part of the key — see
//! [`VariantKey`]). [`compute_package_variants`] walks every game instance in
//! a [`Theorem`], deduplicates package instances that share a variant key,
//! and renders one [`EcFile`] per distinct variant.
//!
//! The oracle-body translator is a near-identity lowering (story 16 §3.5):
//! `easycryptify` (the last stage of `EasyCryptTransform`, run before export)
//! has already turned every oracle into EasyCrypt's single-exit shape — no
//! `abort`, one trailing `return ec_result`, every `Unwrap` and `invoke`
//! guarded where it stood, and every signature `Maybe(T)` (`T option`, `None`
//! is abort). The writer does no control-flow reasoning of its own.

use std::collections::{HashMap, HashSet};

use miette::SourceSpan;

use crate::expressions::{Expression, ExpressionKind};
use crate::identifier::{pkg_ident::PackageIdentifier, Identifier};
use crate::package::{Composition, Edge, OracleDef, OracleSig, Package};
use crate::statement::{
    Assignment, AssignmentRhs, CodeBlock, IfThenElse, InvokeOracle, Pattern, Statement,
};
use crate::theorem::Theorem;
use crate::types::{CountSpec, Type, TypeKind};

use super::ast::{
    EcBlock, EcExpr, EcFile, EcItem, EcLvalue, EcModule, EcProc, EcStmt, EcType, ProcSig, Require,
};
use super::names::{NameKind, Names};
use crate::transforms::easycryptify;
use super::types::{bits_suffix, translate_expr, translate_type};
use super::EcExportError;

// ---------------------------------------------------------------------------
// Variant keys
// ---------------------------------------------------------------------------

/// The key that determines whether two package instances share one EasyCrypt
/// module (§3.1, amended by story 14 §3.1). A package's module is a function
/// of the package and its `Bits(...)` instantiation *only* — the wiring
/// (which instances it imports from, any renaming) is a fact about the
/// composition, resolved by a composition-local adapter instead (`game.rs`
/// §3.4), never embedded here. `int_params` keeps only the integer params
/// that are actually baked into a type (a `Bits` width,
/// [`integer_param_used_as_width`]); a non-width integer param becomes a
/// module variable ([`param_needs_var`]) and so two instances differing only
/// there render identically and must share one module.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(super) struct VariantKey {
    pkg_name: String,
    int_params: Vec<(String, ParamValue)>,
    fn_params: Vec<(String, ParamValue)>,
}

/// A package parameter's assigned value, canonicalised so that the *same*
/// theorem constant compares equal across different game instances even
/// though [`crate::packageinstance::instantiate`] tags each instantiation's
/// copy of the identifier with a different `game_inst_name`/`pkg_inst_name`.
/// [`Identifier::as_theorem_identifier`] already strips exactly that
/// instance-specific tagging by walking down to the underlying
/// [`crate::identifier::theorem_ident::TheoremIdentifier`], so it is reused
/// here instead of comparing raw [`Expression`]s.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum ParamValue {
    TheoremConst(String),
    /// Fallback for a literal (or otherwise non-identifier) assignment,
    /// which carries no per-instance tagging and so compares correctly as
    /// raw `Expression` equality.
    Literal(Box<Expression>),
}

fn canonical_param_value(expr: &Expression) -> ParamValue {
    if let ExpressionKind::Identifier(id) = expr.kind() {
        if let Some(theorem_id) = id.as_theorem_identifier() {
            return ParamValue::TheoremConst(theorem_id.ident());
        }
    }
    ParamValue::Literal(Box::new(expr.clone()))
}

/// Computes every package instance's [`VariantKey`] within `comp`, indexed
/// by `comp.pkgs`'s position. Story 14 §3.1 dropped `imports` from the key,
/// so a key no longer depends on any other package instance's key — each
/// instance is computed independently, in any order.
pub(super) fn compute_all_keys(comp: &Composition) -> Vec<VariantKey> {
    (0..comp.pkgs.len()).map(|idx| compute_key(comp, idx)).collect()
}

fn compute_key(comp: &Composition, pkg_idx: usize) -> VariantKey {
    let inst = &comp.pkgs[pkg_idx];
    let pkg = &inst.pkg;

    let mut int_params = Vec::new();
    let mut fn_params = Vec::new();
    for (name, ty, _span) in &pkg.params {
        let assigned = inst
            .params
            .iter()
            .find(|(id, _)| &id.name == name)
            .map(|(_, expr)| expr)
            .expect("a package instance must assign every one of its package's declared params");
        match ty.kind() {
            TypeKind::Integer if integer_param_used_as_width(pkg, name) => {
                int_params.push((name.clone(), canonical_param_value(assigned)));
            }
            TypeKind::Integer => {}
            TypeKind::Fn(..) => fn_params.push((name.clone(), canonical_param_value(assigned))),
            _ => {}
        }
    }

    VariantKey {
        pkg_name: pkg.name.clone(),
        int_params,
        fn_params,
    }
}

/// One package instance per (key, representative composition, index within
/// it), in first-discovery order across the whole theorem: game instances in
/// `theorem.instances` order, then `ordered_pkgs_idx()` within each (§3.1).
pub(super) fn discover_variants(theorem: &Theorem<'_>) -> Vec<(VariantKey, Composition, usize)> {
    let mut discovered: Vec<(VariantKey, Composition, usize)> = Vec::new();
    for game_inst in &theorem.instances {
        let comp = game_inst.game();
        let keys = compute_all_keys(comp);
        for idx in comp.ordered_pkgs_idx() {
            let key = keys[idx].clone();
            if !discovered.iter().any(|(k, _, _)| k == &key) {
                discovered.push((key, comp.clone(), idx));
            }
        }
    }
    discovered
}

/// Assigns each distinct key its final EasyCrypt module name (§3.1): the
/// package's own (mangled) name if it has exactly one variant in the
/// theorem, else `<Pkg>_v1`, `<Pkg>_v2`, ... in discovery order.
pub(super) fn assign_names(
    discovered: &[(VariantKey, Composition, usize)],
    names: &mut Names,
) -> Result<HashMap<VariantKey, String>, EcExportError> {
    let mut groups: Vec<(String, Vec<&VariantKey>)> = Vec::new();
    for (key, _, _) in discovered {
        match groups.iter_mut().find(|(pkg_name, _)| pkg_name == &key.pkg_name) {
            Some((_, keys)) => keys.push(key),
            None => groups.push((key.pkg_name.clone(), vec![key])),
        }
    }

    let mut result = HashMap::new();
    for (pkg_name, keys) in groups {
        let mangled = names.mangle(NameKind::Module, &pkg_name)?;
        if keys.len() == 1 {
            result.insert(keys[0].clone(), mangled);
        } else {
            for (i, key) in keys.into_iter().enumerate() {
                result.insert(key.clone(), format!("{mangled}_v{}", i + 1));
            }
        }
    }
    Ok(result)
}

/// One deduplicated package variant, ready to render as `Pkg_<name>.ec`
/// (story 10, prefix renamed by story 14 §3.6) — `name` itself is unprefixed
/// (it is also the module's own name), the `Pkg_` prefix is added only where
/// the file is written (`export.rs`).
#[derive(Debug, Clone)]
pub struct PackageVariant {
    pub name: String,
    pub file: EcFile,
}

/// Computes every package variant reachable from `theorem`, one [`EcFile`]
/// per distinct variant, deterministic and deduplicated across the whole
/// theorem (§3.1).
pub fn compute_package_variants(theorem: &Theorem<'_>) -> Result<Vec<PackageVariant>, EcExportError> {
    compute_package_variants_observed(theorem, &mut super::progress::NopExportObserver)
}

/// [`compute_package_variants`] reporting the `packages` phase (story 21).
pub fn compute_package_variants_observed(
    theorem: &Theorem<'_>,
    observer: &mut dyn super::progress::ExportObserver,
) -> Result<Vec<PackageVariant>, EcExportError> {
    let discovered = discover_variants(theorem);
    let mut scope = super::progress::PhaseScope::start(
        observer,
        super::progress::ExportPhase::Packages,
        discovered.len(),
    );
    let mut names = Names::new();
    let name_map = assign_names(&discovered, &mut names)?;

    let mut out = Vec::with_capacity(discovered.len());
    for (key, comp, idx) in &discovered {
        let name = name_map
            .get(key)
            .expect("every discovered key was named in assign_names")
            .clone();
        scope.item(&format!("Pkg_{name}"));
        let file = render_variant(comp, *idx, &name, key)?;
        out.push(PackageVariant { name, file });
    }
    scope.finish();
    Ok(out)
}

// ---------------------------------------------------------------------------
// Module rendering
// ---------------------------------------------------------------------------

/// Per-package naming state, shared across a variant's `init` proc and every
/// oracle proc so that a state field, a param-turned-var, a local and an
/// oracle argument that happen to share a raw Domino name still resolve
/// (idempotently) to the *same* EasyCrypt name — see the story's §6 note on
/// state/local shadowing.
struct PackageScope {
    /// The `Var` namespace: state fields, param-vars, oracle args, locals.
    names: Names,
}

pub(super) fn ident_raw_name_and_type(id: &Identifier) -> (String, Type) {
    match id {
        Identifier::PackageIdentifier(p) => (p.ident(), p.get_type()),
        Identifier::Generated(name, ty) => (name.clone(), ty.clone()),
        other => unreachable!(
            "identifier kind not expected in easycrypt-exported oracle code: {other:?}"
        ),
    }
}

fn is_state_field(id: &Identifier) -> bool {
    matches!(id, Identifier::PackageIdentifier(PackageIdentifier::State(_)))
}

/// Whether `pkg`'s integer parameter `param_name` is ever used as a `Bits`
/// width (a `CountSpec::Identifier` naming it) — walking state field types,
/// oracle signatures, and every `Type` embedded in oracle code (`Sample`,
/// `BitsLiteral`, `EmptyTable`, `None`). If it is, the parameter is baked
/// into a type name (`bits_n`) and needs no module variable; otherwise it is
/// a genuine runtime value and needs one (§3.2: "Non-Bits-width integer
/// parameters ... become module variables too").
pub(super) fn integer_param_used_as_width(pkg: &Package, param_name: &str) -> bool {
    fn type_uses(ty: &Type, name: &str) -> bool {
        match ty.kind() {
            TypeKind::Bits(CountSpec::Identifier(id)) => matches!(
                id.as_ref(),
                Identifier::PackageIdentifier(PackageIdentifier::Const(c)) if c.name == name
            ),
            TypeKind::Maybe(t) | TypeKind::List(t) | TypeKind::Set(t) => type_uses(t, name),
            TypeKind::Tuple(ts) => ts.iter().any(|t| type_uses(t, name)),
            TypeKind::Table(k, v) => type_uses(k, name) || type_uses(v, name),
            TypeKind::Fn(args, ret) => args.iter().any(|t| type_uses(t, name)) || type_uses(ret, name),
            _ => false,
        }
    }

    fn expr_uses(expr: &Expression, name: &str) -> bool {
        match expr.kind() {
            ExpressionKind::Bot
            | ExpressionKind::StringLiteral(_)
            | ExpressionKind::IntegerLiteral(_)
            | ExpressionKind::BooleanLiteral(_)
            | ExpressionKind::Identifier(_) => false,
            ExpressionKind::Sample(ty) | ExpressionKind::EmptyTable(ty) | ExpressionKind::None(ty) => {
                type_uses(ty, name)
            }
            ExpressionKind::BitsLiteral(_, ty) => type_uses(ty, name),
            ExpressionKind::TableAccess(_, e) => expr_uses(e, name),
            ExpressionKind::Tuple(es)
            | ExpressionKind::List(es)
            | ExpressionKind::Set(es)
            | ExpressionKind::Equals(es)
            | ExpressionKind::And(es)
            | ExpressionKind::Or(es)
            | ExpressionKind::Xor(es)
            | ExpressionKind::Concat(es) => es.iter().any(|e| expr_uses(e, name)),
            ExpressionKind::FnCall(_, args) => args.iter().any(|e| expr_uses(e, name)),
            ExpressionKind::Some(e)
            | ExpressionKind::Unwrap(e)
            | ExpressionKind::Not(e)
            | ExpressionKind::Neg(e)
            | ExpressionKind::Inv(e)
            | ExpressionKind::Sum(e)
            | ExpressionKind::Prod(e)
            | ExpressionKind::Any(e)
            | ExpressionKind::All(e)
            | ExpressionKind::Union(e)
            | ExpressionKind::Cut(e)
            | ExpressionKind::SetDiff(e) => expr_uses(e, name),
            ExpressionKind::Add(a, b)
            | ExpressionKind::Sub(a, b)
            | ExpressionKind::Mul(a, b)
            | ExpressionKind::Div(a, b)
            | ExpressionKind::Pow(a, b)
            | ExpressionKind::Mod(a, b)
            | ExpressionKind::LessThen(a, b)
            | ExpressionKind::GreaterThen(a, b)
            | ExpressionKind::LessThenEq(a, b)
            | ExpressionKind::GreaterThenEq(a, b) => expr_uses(a, name) || expr_uses(b, name),
        }
    }

    fn stmt_uses(stmt: &Statement, name: &str) -> bool {
        match stmt {
            Statement::Abort(_) => false,
            Statement::Return(expr, _) => expr.as_ref().is_some_and(|e| expr_uses(e, name)),
            Statement::Assignment(Assignment { pattern, rhs }, _) => {
                let pattern_uses = matches!(pattern, Pattern::Table { index, .. } if expr_uses(index, name));
                let rhs_uses = match rhs {
                    AssignmentRhs::Expression(e) => expr_uses(e, name),
                    AssignmentRhs::Sample { ty, .. } => type_uses(ty, name),
                    AssignmentRhs::Invoke { args, return_type, .. } => {
                        args.iter().any(|a| expr_uses(a, name))
                            || return_type.as_ref().is_some_and(|t| type_uses(t, name))
                    }
                };
                pattern_uses || rhs_uses
            }
            Statement::InvokeOracle(InvokeOracle { args, .. }) => args.iter().any(|a| expr_uses(a, name)),
            Statement::IfThenElse(IfThenElse { cond, then_block, else_block, .. }) => {
                expr_uses(cond, name)
                    || then_block.0.iter().any(|s| stmt_uses(s, name))
                    || else_block.0.iter().any(|s| stmt_uses(s, name))
            }
            Statement::For(_, start, end, body, _) => {
                expr_uses(start, name) || expr_uses(end, name) || body.0.iter().any(|s| stmt_uses(s, name))
            }
        }
    }

    if pkg.state.iter().any(|(_, ty, _)| type_uses(ty, param_name)) {
        return true;
    }
    for oracle in &pkg.oracles {
        if oracle.sig.args.iter().any(|(_, ty)| type_uses(ty, param_name)) {
            return true;
        }
        if type_uses(&oracle.sig.ty, param_name) {
            return true;
        }
        if oracle.code.0.iter().any(|s| stmt_uses(s, param_name)) {
            return true;
        }
    }
    false
}

/// Whether a package parameter becomes a module `var` (§3.2): every
/// `Boolean` param does; an `Integer` param does unless it is used purely as
/// a `Bits` width ([`integer_param_used_as_width`]); every other type
/// (`Fn`, …) never does. Shared with story 04 (`game.rs`), which needs the
/// exact same decision both to know a package variant's `init` argument list
/// (so it can pass matching bindings from the router) and, applied to a
/// composition's own `consts`, to decide the router's own `init` signature.
pub(super) fn param_needs_var(pkg: &Package, name: &str, ty: &Type) -> bool {
    match ty.kind() {
        TypeKind::Boolean => true,
        TypeKind::Integer => !integer_param_used_as_width(pkg, name),
        _ => false,
    }
}

/// Whether `pkg` gets an `init` proc at all (§3.2): it does unless it has
/// neither state nor a var-needing param. Story 04 needs this to know
/// whether to skip a package instance's `init` call when assembling the
/// router's own `init` body.
pub(super) fn pkg_needs_init(pkg: &Package) -> bool {
    !pkg.state.is_empty()
        || pkg
            .params
            .iter()
            .any(|(name, ty, _)| param_needs_var(pkg, name, ty))
}

/// `pkg.imports`, in a stable order — **not** `pkg.imports`'s own Vec order,
/// which is not guaranteed deterministic across independent parses (a
/// parser-internal characteristic, unrelated to this epic — pre-story-14
/// code never iterated `pkg.imports` directly for rendering, only
/// `comp.edges`, which *is* a stably-ordered `Vec`). Import names are unique
/// per package (§2.2's "Import names are unique per instance" — enforced per
/// caller instance, and a package's own declared list can't repeat a name
/// either), so sorting by name is an unambiguous, deterministic
/// canonicalisation. `game.rs`'s `build_import_adapter` sorts the same way,
/// so an adapter's proc order always matches the interface it satisfies.
pub(super) fn ordered_imports(pkg: &Package) -> Vec<&(OracleSig, SourceSpan)> {
    let mut imports: Vec<&(OracleSig, SourceSpan)> = pkg.imports.iter().collect();
    imports.sort_by(|a, b| a.0.name.cmp(&b.0.name));
    imports
}

/// One `ProcSig` per import, in [`ordered_imports`] order, mangled exactly
/// the way `interfaces.rs`'s old (now-deleted) `build_variant_procs`
/// mangled an oracle: `NameKind::Proc` for the name, `NameKind::Var` for
/// each argument, return type `T option` (story 14 §3.2 — the shared shape
/// moved here since this is now its only caller).
fn build_import_procs(pkg: &Package) -> Result<Vec<ProcSig>, EcExportError> {
    let mut names = Names::new();
    let mut procs = Vec::new();
    for (sig, span) in ordered_imports(pkg) {
        let proc_name = names.mangle(NameKind::Proc, &sig.name)?;
        let mut args = Vec::new();
        for (name, ty) in &sig.args {
            let mangled = names.mangle(NameKind::Var, name)?;
            args.push((mangled, translate_type(ty, *span)?));
        }
        // `easycryptify` has already made the signature `Maybe(T)`, which
        // translates to `T option` — no extra wrapping (story 16 §3.5).
        let ret = translate_type(&sig.ty, *span)?;
        procs.push(ProcSig {
            name: proc_name,
            args,
            ret,
        });
    }
    Ok(procs)
}

/// A package's own import interface (story 14 §3.2): one module type built
/// from `pkg.imports` alone, in declaration order — composition-independent,
/// unlike the pre-story-14 shape this replaces. Named `<Variant>_Imports`,
/// strictly longer than the module's own name so it can never collide with
/// it. Returns `None` for a package with no imports, which gets neither a
/// module type nor a functor parameter, exactly as before.
fn build_import_interface(
    pkg: &Package,
    variant_name: &str,
) -> Result<Option<(EcItem, String)>, EcExportError> {
    if pkg.imports.is_empty() {
        return Ok(None);
    }
    let iface_name = format!("{variant_name}_Imports");
    let procs = build_import_procs(pkg)?;
    let item = EcItem::ModuleType {
        name: iface_name.clone(),
        params: vec![],
        includes: vec![],
        procs,
    };
    Ok(Some((item, iface_name)))
}

fn describe_param(v: &ParamValue) -> String {
    match v {
        ParamValue::TheoremConst(name) => name.clone(),
        ParamValue::Literal(_) => "<literal>".to_string(),
    }
}

fn variant_comment(key: &VariantKey, variant_name: &str) -> String {
    let mut parts: Vec<String> = Vec::new();
    for (name, val) in &key.int_params {
        parts.push(format!("{name} = {}", describe_param(val)));
    }
    for (name, val) in &key.fn_params {
        parts.push(format!("{name} = func_{}", describe_param(val)));
    }
    if parts.is_empty() {
        format!("{variant_name}: {}", key.pkg_name)
    } else {
        format!("{variant_name}: {}", parts.join(", "))
    }
}

fn no_identifier_resolver(_id: &Identifier, _span: SourceSpan) -> Result<EcExpr, EcExportError> {
    unreachable!("a default-value expression never contains an Identifier")
}

fn render_variant(
    comp: &Composition,
    pkg_idx: usize,
    variant_name: &str,
    key: &VariantKey,
) -> Result<EcFile, EcExportError> {
    let inst = &comp.pkgs[pkg_idx];
    let pkg = &inst.pkg;

    if !inst.types.is_empty() {
        // `PackageInstance::types` (unlike `state`/`params`/`OracleDef`)
        // carries no `SourceSpan` of its own in Domino's data model — the
        // same gap `typesfile.rs::theorem_level_span()` documents for
        // `Theorem::consts`. Point at the nearest spanned thing this package
        // has (its first state field, else its first oracle, else a
        // zero-length placeholder for the — currently untestable — case of
        // a package with type params and nothing else) rather than adding a
        // fake span field just for this one error.
        let span = pkg
            .state
            .first()
            .map(|(_, _, s)| *s)
            .or_else(|| pkg.oracles.first().map(|o| o.file_pos))
            .unwrap_or((0, 0).into());
        return Err(EcExportError::PackageTypeParameters { span });
    }

    let import_iface = build_import_interface(pkg, variant_name)?;
    let functor_param_decls: Vec<(String, String)> = match &import_iface {
        Some((_, iface_name)) => vec![("O".to_string(), iface_name.clone())],
        None => vec![],
    };
    let mut scope = PackageScope { names: Names::new() };

    let mut module_vars = Vec::new();
    for (name, ty, span) in &pkg.state {
        let mangled = scope.names.mangle(NameKind::Var, name)?;
        module_vars.push((mangled, translate_type(ty, *span)?));
    }

    let mut param_vars: Vec<(String, EcType)> = Vec::new();
    for (name, ty, span) in &pkg.params {
        if param_needs_var(pkg, name, ty) {
            let mangled = scope.names.mangle(NameKind::Var, name)?;
            param_vars.push((mangled, translate_type(ty, *span)?));
        }
    }
    module_vars.extend(param_vars.iter().cloned());

    let init_proc = if pkg.state.is_empty() && param_vars.is_empty() {
        None
    } else {
        let mut body = Vec::new();
        for (name, ty, span) in &pkg.state {
            let mangled = scope.names.mangle(NameKind::Var, name)?;
            let default_expr = ty.default_expression();
            let rhs = translate_expr(&default_expr, *span, &mut no_identifier_resolver)?;
            body.push(EcStmt::Assign {
                lhs: EcLvalue::Var(mangled),
                rhs,
            });
        }
        let mut args = Vec::new();
        for (mangled, ty) in &param_vars {
            let arg_name = format!("{mangled}_");
            args.push((arg_name.clone(), ty.clone()));
            body.push(EcStmt::Assign {
                lhs: EcLvalue::Var(mangled.clone()),
                rhs: EcExpr::Var(arg_name),
            });
        }
        Some(EcProc {
            name: "init".to_string(),
            args,
            ret: EcType::Unit,
            locals: vec![],
            body: EcBlock(body),
            ret_expr: None,
        })
    };

    let mut procs = Vec::new();
    procs.extend(init_proc);
    for oracle in &pkg.oracles {
        procs.push(build_proc(&mut scope, oracle)?);
    }

    let module = EcModule {
        name: variant_name.to_string(),
        params: functor_param_decls,
        implements: None,
        vars: module_vars,
        procs,
    };

    let requires = vec![Require {
        import: true,
        names: vec![
            "AllCore".to_string(),
            "Distr".to_string(),
            "FMap".to_string(),
            "Int".to_string(),
            "IntDiv".to_string(),
            "Types".to_string(),
        ],
    }];

    let mut items = Vec::new();
    if let Some((iface_item, _)) = import_iface {
        items.push(iface_item);
    }
    items.push(EcItem::Module(module));

    Ok(EcFile {
        header: vec![variant_comment(key, variant_name)],
        requires,
        items,
    })
}

// ---------------------------------------------------------------------------
// Oracle translation
// ---------------------------------------------------------------------------

fn collect_locals(
    cb: &CodeBlock,
    scope: &mut PackageScope,
    out: &mut Vec<(String, EcType)>,
    seen: &mut HashSet<String>,
) -> Result<(), EcExportError> {
    for stmt in &cb.0 {
        match stmt {
            Statement::Assignment(Assignment { pattern, .. }, span) => match pattern {
                Pattern::Ident(id) => record_local(id, scope, out, seen, *span)?,
                Pattern::Tuple(ids) => {
                    for id in ids {
                        record_local(id, scope, out, seen, *span)?;
                    }
                }
                // The table itself (state, or a generated local already
                // declared by its own `<gen> <- empty` Ident-pattern
                // assignment from `tableinitialize`) needs no new `var` here.
                Pattern::Table { .. } => {}
            },
            Statement::IfThenElse(IfThenElse { then_block, else_block, .. }) => {
                collect_locals(then_block, scope, out, seen)?;
                collect_locals(else_block, scope, out, seen)?;
            }
            Statement::Abort(_) | Statement::Return(_, _) | Statement::InvokeOracle(_) => {}
            Statement::For(_, _, _, body, _) => collect_locals(body, scope, out, seen)?,
        }
    }
    Ok(())
}

/// The EasyCrypt name of a variable. `easycryptify`'s own locals
/// (`ec_result`, `ec_done`, `ec_r<N>` — [`easycryptify::is_generated_name`])
/// are exporter-owned and pass through verbatim: the mangler reserves the
/// `ec_` prefix precisely for such names and escapes every *user* identifier
/// starting with it (`ec_foo` → `d_ec_foo`), so they can never collide.
fn var_name(scope: &mut PackageScope, id: &Identifier) -> Result<String, EcExportError> {
    let (raw, _ty) = ident_raw_name_and_type(id);
    var_spelling(
        &mut scope.names,
        &raw,
        matches!(id, Identifier::Generated(..)),
    )
}

/// [`var_name`] on a raw name: `generated` says whether it names an
/// [`Identifier::Generated`], the only kind `easycryptify`'s own locals are.
/// Shared with the debugger listing (story 08), which spells a package's
/// variables exactly as its module does.
pub(super) fn var_spelling(
    names: &mut Names,
    raw: &str,
    generated: bool,
) -> Result<String, EcExportError> {
    if generated && easycryptify::is_generated_name(raw) {
        return Ok(raw.to_string());
    }
    Ok(names.mangle(NameKind::Var, raw)?)
}

fn record_local(
    id: &Identifier,
    scope: &mut PackageScope,
    out: &mut Vec<(String, EcType)>,
    seen: &mut HashSet<String>,
    span: SourceSpan,
) -> Result<(), EcExportError> {
    if is_state_field(id) {
        return Ok(());
    }
    // Keyed by the *EasyCrypt* name: `easycryptify`'s `ec_result` and a
    // user local spelled `ec_result` share a raw name but not a declaration.
    let (_raw, ty) = ident_raw_name_and_type(id);
    let mangled = var_name(scope, id)?;
    if !seen.insert(mangled.clone()) {
        return Ok(());
    }
    let ecty = translate_type(&ty, span)?;
    out.push((mangled, ecty));
    Ok(())
}

/// Translates one oracle whose body `easycryptify` has already lowered
/// (story 16 §3.1): its signature returns `Maybe(T)` (rendered `T option`),
/// its body contains no `Abort`, and its only `Return` is the final
/// statement. The writer therefore does no control-flow reasoning of its own
/// — the body is lowered statement by statement and the trailing `Return`
/// becomes the proc's `return`.
fn build_proc(scope: &mut PackageScope, oracle: &OracleDef) -> Result<EcProc, EcExportError> {
    let span = oracle.file_pos;
    let ret = translate_type(&oracle.sig.ty, span)?;

    let mut args = Vec::new();
    for (name, ty) in &oracle.sig.args {
        let mangled = scope.names.mangle(NameKind::Var, name)?;
        args.push((mangled, translate_type(ty, span)?));
    }

    let mut locals = Vec::new();
    let mut seen = HashSet::new();
    collect_locals(&oracle.code, scope, &mut locals, &mut seen)?;

    let Some((Statement::Return(Some(ret_value), ret_span), body_stmts)) =
        oracle.code.0.split_last()
    else {
        unreachable!(
            "easycryptify ends every oracle body in a single `return ec_result` \
             (oracle `{}`)",
            oracle.sig.name
        )
    };

    let mut temps = SampleTemps::default();
    let mut translator = OracleTranslator {
        naming: &mut *scope,
        temps: &mut temps,
    };
    let body = translator.translate_block(body_stmts)?;
    let ret_expr = translator.translate_e(ret_value, *ret_span)?;

    let mut ec_locals: Vec<(String, EcType, Option<EcExpr>)> =
        locals.into_iter().map(|(name, ty)| (name, ty, None)).collect();
    for (name, ty) in temps.decls {
        ec_locals.push((name, ty, None));
    }

    let proc_name = scope.names.mangle(NameKind::Proc, &oracle.sig.name)?;

    Ok(EcProc {
        name: proc_name,
        args,
        ret,
        locals: ec_locals,
        body,
        ret_expr: Some(ret_expr),
    })
}

/// How the identifiers of an oracle body are spelled in EasyCrypt.
///
/// Inside the package's own module ([`PackageScope`]) every variable — state
/// field, parameter, argument, local — is a bare name. The debugger listing
/// (story 08, `super::lower`) inlines several procedures into one, so there
/// state is qualified with its instance module (`Pkg_Inst_KEM.pk`) and a
/// callee's locals may be renamed apart from its caller's.
pub(super) trait OracleNaming {
    /// `id` in expression position.
    fn expr(&mut self, id: &Identifier) -> Result<EcExpr, EcExportError>;
    /// `id` as the target of an assignment: a (possibly qualified)
    /// program-variable path.
    fn target(&mut self, id: &Identifier) -> Result<String, EcExportError>;
}

impl OracleNaming for PackageScope {
    fn expr(&mut self, id: &Identifier) -> Result<EcExpr, EcExportError> {
        Ok(EcExpr::Var(var_name(self, id)?))
    }

    fn target(&mut self, id: &Identifier) -> Result<String, EcExportError> {
        var_name(self, id)
    }
}

/// `ec_s<N>` proc-local declarations for a sample into a table entry
/// (`T[k] <-$ τ`, which EasyCrypt cannot express directly), appended to
/// [`EcProc::locals`] afterwards. Every other generated local —
/// `ec_result`, `ec_done`, the `ec_r<N>` invoke temporaries — arrives from
/// `easycryptify` as an ordinary Domino local.
#[derive(Default)]
pub(super) struct SampleTemps {
    ctr: usize,
    pub(super) decls: Vec<(String, EcType)>,
}

/// Translates one statement of an `easycryptify`-lowered oracle body with
/// the given naming — the per-statement entry point of the oracle
/// translator, for the debugger listing (story 08). An `if` is translated
/// whole, branches included.
pub(super) fn translate_oracle_stmt(
    naming: &mut dyn OracleNaming,
    temps: &mut SampleTemps,
    stmt: &Statement,
) -> Result<Vec<EcStmt>, EcExportError> {
    OracleTranslator { naming, temps }.translate_stmt(stmt)
}

/// Translates one expression of an oracle body with the given naming.
pub(super) fn translate_oracle_expr(
    naming: &mut dyn OracleNaming,
    expr: &Expression,
    span: SourceSpan,
) -> Result<EcExpr, EcExportError> {
    let mut temps = SampleTemps::default();
    OracleTranslator {
        naming,
        temps: &mut temps,
    }
    .translate_e(expr, span)
}

struct OracleTranslator<'a> {
    naming: &'a mut dyn OracleNaming,
    temps: &'a mut SampleTemps,
}

impl OracleTranslator<'_> {
    /// Declares and returns a fresh `ec_s<N>` sample temporary of type `ty`.
    fn declare_sample_temp(&mut self, ty: EcType) -> String {
        self.temps.ctr += 1;
        let name = format!("ec_s{}", self.temps.ctr);
        self.temps.decls.push((name.clone(), ty));
        name
    }

    fn translate_e(&mut self, expr: &Expression, span: SourceSpan) -> Result<EcExpr, EcExportError> {
        let naming = &mut *self.naming;
        let mut resolver =
            |id: &Identifier, _s: SourceSpan| -> Result<EcExpr, EcExportError> { naming.expr(id) };
        translate_expr(expr, span, &mut resolver)
    }

    fn resolve_name(&mut self, id: &Identifier) -> Result<String, EcExportError> {
        self.naming.target(id)
    }

    fn sample_distr(&self, ty: &Type, span: SourceSpan) -> Result<EcExpr, EcExportError> {
        match ty.kind() {
            TypeKind::Bits(count) => {
                let name = match bits_suffix(count) {
                    Some(suffix) => format!("dbits_{suffix}"),
                    None => "dbits".to_string(),
                };
                Ok(EcExpr::Var(name))
            }
            _ => Err(EcExportError::UnsupportedStatement {
                construct: "Sample of a non-Bits type (EasyCrypt export only supports sampling Bits)",
                span,
            }),
        }
    }

    fn translate_pattern(&mut self, pattern: &Pattern) -> Result<EcLvalue, EcExportError> {
        Ok(match pattern {
            Pattern::Ident(id) => EcLvalue::Var(self.resolve_name(id)?),
            Pattern::Tuple(ids) => EcLvalue::Tuple(
                ids.iter()
                    .map(|id| self.resolve_name(id))
                    .collect::<Result<Vec<_>, _>>()?,
            ),
            Pattern::Table { .. } => {
                unreachable!("table patterns are translated by their own callers")
            }
        })
    }

    /// Translates `stmts` one statement at a time (story 16 §3.5). The input
    /// is `easycryptify`'s output, so nothing here terminates early: an
    /// `Unwrap` is already guarded (and becomes a plain `oget`), an `invoke`
    /// already binds its `ec_r<N>` temporary, and an `if` with an empty else
    /// branch renders with no `else` at all.
    fn translate_block(&mut self, stmts: &[Statement]) -> Result<EcBlock, EcExportError> {
        let mut out = Vec::new();
        for stmt in stmts {
            out.extend(self.translate_stmt(stmt)?);
        }
        Ok(EcBlock(out))
    }

    /// One statement of [`Self::translate_block`]. Every statement becomes
    /// one EasyCrypt statement, except a sample into a table entry, which
    /// becomes two.
    fn translate_stmt(&mut self, stmt: &Statement) -> Result<Vec<EcStmt>, EcExportError> {
        let mut out = Vec::new();
        {
            match stmt {
                Statement::Abort(_) => unreachable!("easycryptify leaves no `abort` in an oracle body"),
                Statement::Return(..) => unreachable!(
                    "easycryptify leaves a single `return`, as the last statement of the body"
                ),
                Statement::For(..) => unreachable!("easycryptify rejects every surviving `for` loop"),

                Statement::IfThenElse(ite) => {
                    let cond = self.translate_e(&ite.cond, ite.full_span)?;
                    let then_block = self.translate_block(&ite.then_block.0)?;
                    let else_block = if ite.else_block.0.is_empty() {
                        None
                    } else {
                        Some(self.translate_block(&ite.else_block.0)?)
                    };
                    out.push(EcStmt::If {
                        cond,
                        then_block,
                        else_block,
                    });
                }

                Statement::Assignment(Assignment { pattern, rhs }, span) => {
                    let span = *span;
                    match rhs {
                        AssignmentRhs::Expression(expr) => match pattern {
                            Pattern::Table { ident, index } => {
                                out.extend(self.translate_table_write(ident, index, expr, span)?);
                            }
                            _ => {
                                let lhs = self.translate_pattern(pattern)?;
                                let rhs = self.translate_e(expr, span)?;
                                out.push(EcStmt::Assign { lhs, rhs });
                            }
                        },

                        AssignmentRhs::Sample { ty, .. } => {
                            let distr = self.sample_distr(ty, span)?;
                            match pattern {
                                Pattern::Ident(id) => {
                                    let name = self.resolve_name(id)?;
                                    out.push(EcStmt::Sample {
                                        lhs: EcLvalue::Var(name),
                                        distr,
                                    });
                                }
                                Pattern::Table { ident, index } => {
                                    let sample_ty = translate_type(ty, span)?;
                                    let tmp = self.declare_sample_temp(sample_ty);
                                    out.push(EcStmt::Sample {
                                        lhs: EcLvalue::Var(tmp.clone()),
                                        distr,
                                    });
                                    let key = self.translate_e(index, span)?;
                                    let map = self.resolve_name(ident)?;
                                    out.push(EcStmt::Assign {
                                        lhs: EcLvalue::MapSet { map, key },
                                        rhs: EcExpr::Var(tmp),
                                    });
                                }
                                Pattern::Tuple(_) => {
                                    unreachable!("the parser rejects a tuple-pattern sample")
                                }
                            }
                        }

                        AssignmentRhs::Invoke { args, edge, .. } => {
                            let Pattern::Ident(_) = pattern else {
                                unreachable!("easycryptify binds every invoke to an `ec_r<N>` temporary")
                            };
                            let lhs = self.translate_pattern(pattern)?;
                            out.push(self.translate_invoke(Some(lhs), args, edge, span)?);
                        }
                    }
                }

                Statement::InvokeOracle(InvokeOracle { args, edge, file_pos, .. }) => {
                    // `easycryptify` binds even a bare invoke, to check its
                    // abort; kept for completeness.
                    out.push(self.translate_invoke(None, args, edge, *file_pos)?);
                }
            }
        }
        Ok(out)
    }

    /// `T[k] <- rhs` (§3.4). `rhs` may be `Unwrap`-headed — `T[k] <-
    /// Unwrap(m)` for `m : Maybe(Maybe(V))`, once story 17 has inlined
    /// `unwrapify`'s temporary back into it. It is guarded by then and falls
    /// to the general arm below, which only ever `oget`s it.
    fn translate_table_write(
        &mut self,
        ident: &Identifier,
        index: &Expression,
        rhs_expr: &Expression,
        span: SourceSpan,
    ) -> Result<Vec<EcStmt>, EcExportError> {
        let map = self.resolve_name(ident)?;
        let map_expr = self.naming.expr(ident)?;
        let key = self.translate_e(index, span)?;

        match rhs_expr.kind() {
            ExpressionKind::Some(inner) => {
                let value = self.translate_e(inner, span)?;
                Ok(vec![EcStmt::Assign {
                    lhs: EcLvalue::MapSet { map, key },
                    rhs: value,
                }])
            }
            ExpressionKind::None(_) => Ok(vec![EcStmt::Assign {
                lhs: EcLvalue::Var(map),
                rhs: EcExpr::MapRem {
                    map: Box::new(map_expr),
                    key: Box::new(key),
                },
            }]),
            _ => {
                let TypeKind::Maybe(inner_ty) = rhs_expr.get_type().into_kind() else {
                    unreachable!("a table write's right-hand side is always Maybe-typed")
                };
                let inner_ec_ty = translate_type(&inner_ty, span)?;
                let rhs = self.translate_e(rhs_expr, span)?;
                let cond = EcExpr::Binop {
                    op: super::ast::EcBinop::Eq,
                    lhs: Box::new(rhs.clone()),
                    rhs: Box::new(EcExpr::None_(inner_ec_ty)),
                };
                let else_expr = EcExpr::MapSet {
                    map: Box::new(map_expr.clone()),
                    key: Box::new(key.clone()),
                    value: Box::new(EcExpr::Oget(Box::new(rhs))),
                };
                let then_expr = EcExpr::MapRem {
                    map: Box::new(map_expr),
                    key: Box::new(key),
                };
                Ok(vec![EcStmt::Assign {
                    lhs: EcLvalue::Var(map),
                    rhs: EcExpr::If {
                        cond: Box::new(cond),
                        then_expr: Box::new(then_expr),
                        else_expr: Box::new(else_expr),
                    },
                }])
            }
        }
    }

    /// `ec_r<N> <@ O.p(args)` (story 14 §3.3). `lhs` is `None` only for a
    /// bare `invoke`, which `easycryptify` never leaves behind.
    fn translate_invoke(
        &mut self,
        lhs: Option<EcLvalue>,
        args: &[Expression],
        edge: &Option<Edge>,
        span: SourceSpan,
    ) -> Result<EcStmt, EcExportError> {
        let edge = edge
            .as_ref()
            .expect("resolveoracles attaches a resolved Edge to every invoke reaching export");

        // Story 14 §3.3: a package's module is independent of its
        // composition, so the functor parameter is always `O` and the body
        // calls the *import* name (`edge.name()`, the caller's own name —
        // §2.2 of the story) rather than the callee's oracle name
        // (`edge.sig().name`). A composition resolves any renaming in its
        // own adapter (`game.rs` §3.4), not here. A fresh registry is
        // correct (not a collision-detection gap): this reproduces this
        // package's own already-validated `Fwd_Imports`-namespace mangling
        // of one name (`build_import_procs`, run over the same `pkg.imports`
        // list when this variant's import interface was built).
        let module = "O".to_string();
        let proc = Names::new().mangle(NameKind::Proc, edge.name())?;

        let translated_args = args
            .iter()
            .map(|a| self.translate_e(a, span))
            .collect::<Result<Vec<_>, _>>()?;

        Ok(EcStmt::Call {
            lhs,
            module,
            proc,
            args: translated_args,
        })
    }
}

#[cfg(test)]
mod tests {
    use std::path::{Path, PathBuf};

    use crate::identifier::pkg_ident::PackageConstIdentifier;
    use crate::package::OracleSig;
    use crate::packageinstance::PackageInstance;
    use crate::project::{DirectoryFiles, DirectoryProject, Project};
    use crate::transforms::theorem_transforms::EasyCryptTransform;
    use crate::transforms::{TheoremTransform, Transformation as _};

    use super::super::render::render_file;
    use super::*;

    fn span() -> SourceSpan {
        (0, 1).into()
    }

    fn gend(name: &str, ty: Type) -> Identifier {
        Identifier::Generated(name.to_string(), ty)
    }

    /// A single-oracle, no-params, no-imports package instance, for tests
    /// that exercise one translation rule in isolation.
    fn minimal_instance(oracle_name: &str, ret_ty: Type, code: Vec<Statement>) -> PackageInstance {
        let pkg = Package {
            name: "Test".to_string(),
            types: vec![],
            params: vec![],
            state: vec![],
            oracles: vec![OracleDef {
                sig: OracleSig {
                    name: oracle_name.to_string(),
                    args: vec![],
                    ty: ret_ty,
                },
                code: CodeBlock(code),
                file_pos: span(),
            }],
            imports: vec![],
            invariants: vec![],
            file_name: "test.pkg.ssp".to_string(),
            file_contents: String::new(),
        };
        PackageInstance {
            name: "test".to_string(),
            params: vec![],
            types: vec![],
            pkg,
        }
    }

    fn render_single(inst: PackageInstance) -> Result<EcFile, EcExportError> {
        let comp = Composition {
            pkgs: vec![inst],
            edges: vec![],
            exports: vec![],
            name: "TestComp".to_string(),
            consts: vec![],
            invariants: vec![],
        };
        // The writer consumes `easycryptify`'s output (story 16), exactly as
        // `export_theorem` hands it over via `EasyCryptTransform`.
        let (comp, ()) = crate::transforms::easycryptify::Transformation(&comp).transform()?;
        let keys = compute_all_keys(&comp);
        render_variant(&comp, 0, "Test", &keys[0])
    }

    // --- §3.4: table write with an explicit `None` -------------------------

    /// The real projects this story's other golden tests cover never write
    /// a bare `None` into a table (`T[k] <- None`, as opposed to `Some(e)`
    /// or a general `Maybe`-typed expression) — checked directly, so this
    /// rule needs its own isolated fixture.
    #[test]
    fn table_write_with_explicit_none_is_a_bare_rem() {
        let t_ty = Type::table(Type::integer(), Type::integer());
        let t = gend("t", t_ty.clone());
        let pkg = Package {
            name: "Test".to_string(),
            types: vec![],
            params: vec![],
            state: vec![("t".to_string(), t_ty, span())],
            oracles: vec![OracleDef {
                sig: OracleSig {
                    name: "Clear".to_string(),
                    args: vec![("k".to_string(), Type::integer())],
                    ty: Type::empty(),
                },
                code: CodeBlock(vec![
                    Statement::Assignment(
                        Assignment {
                            pattern: Pattern::Table {
                                ident: t,
                                index: gend("k", Type::integer()).into(),
                            },
                            rhs: AssignmentRhs::Expression(Expression::from_kind(
                                ExpressionKind::None(Type::integer()),
                            )),
                        },
                        span(),
                    ),
                    Statement::Return(None, span()),
                ]),
                file_pos: span(),
            }],
            imports: vec![],
            invariants: vec![],
            file_name: "test.pkg.ssp".to_string(),
            file_contents: String::new(),
        };
        let inst = PackageInstance {
            name: "test".to_string(),
            params: vec![],
            types: vec![],
            pkg,
        };
        let file = render_single(inst).unwrap();
        let rendered = render_file(&file);
        assert!(
            rendered.contains("t <- rem t k;"),
            "expected a bare `rem`, got:\n{rendered}"
        );
        assert!(
            !rendered.contains("if"),
            "a bare `None` table write must not need an `if`, got:\n{rendered}"
        );
    }

    // --- §3.3: oracle with no return type -------------------------------

    #[test]
    fn oracle_with_no_return_type_is_unit_option_and_some_tt() {
        let inst = minimal_instance(
            "NoReturn",
            Type::empty(),
            vec![Statement::Return(None, span())],
        );
        let file = render_single(inst).unwrap();
        let rendered = render_file(&file);
        assert!(
            rendered.contains("proc d_NoReturn() : unit option = {"),
            "expected `unit option` return type, got:\n{rendered}"
        );
        assert!(
            rendered.contains("ec_result <- Some tt;"),
            "expected `Some tt`, got:\n{rendered}"
        );
    }

    // --- story 16: `Maybe`-returning oracles --------------------------------

    /// No project under `example-projects/` or `test-projects/` has an oracle
    /// that already returns `Maybe(T)`, so this is hand-built (story 16 §3.4):
    /// the outer option is abort, the inner the value.
    #[test]
    fn oracle_already_returning_maybe_is_t_option_option() {
        let inst = minimal_instance(
            "Lookup",
            Type::maybe(Type::integer()),
            vec![Statement::Return(
                Some(Expression::from_kind(ExpressionKind::None(Type::integer()))),
                span(),
            )],
        );
        let file = render_single(inst).unwrap();
        let rendered = render_file(&file);
        assert!(
            rendered.contains("proc d_Lookup() : int option option = {"),
            "expected `int option option`, got:\n{rendered}"
        );
        assert!(
            rendered.contains("var ec_result : int option option;"),
            "got:\n{rendered}"
        );
        assert!(rendered.contains("ec_result <- Some None;"), "got:\n{rendered}");
    }

    /// A user identifier starting with `ec_` is still escaped (`d_ec_…`), so
    /// it can never collide with `easycryptify`'s own `ec_result`.
    #[test]
    fn a_user_local_named_ec_result_does_not_collide() {
        let local = Identifier::PackageIdentifier(PackageIdentifier::Local(
            crate::identifier::pkg_ident::PackageLocalIdentifier {
                pkg_name: "Test".to_string(),
                oracle_name: "O".to_string(),
                name: "ec_result".to_string(),
                ty: Type::integer(),
                pkg_inst_name: Some("test".to_string()),
                game_name: None,
                game_inst_name: None,
                theorem_name: None,
            },
        ));
        let inst = minimal_instance(
            "O",
            Type::integer(),
            vec![
                Statement::Assignment(
                    Assignment {
                        pattern: Pattern::Ident(local.clone()),
                        rhs: AssignmentRhs::Expression(Expression::integer(1)),
                    },
                    span(),
                ),
                Statement::Return(Some(local.into()), span()),
            ],
        );
        let rendered = render_file(&render_single(inst).unwrap());
        assert!(rendered.contains("var d_ec_result : int;"), "got:\n{rendered}");
        assert!(rendered.contains("ec_result <- Some d_ec_result;"), "got:\n{rendered}");
    }

    // --- §4: hard errors --------------------------------------------------

    #[test]
    fn package_type_parameters_is_a_hard_error() {
        let mut inst = minimal_instance("O", Type::empty(), vec![Statement::Return(None, span())]);
        inst.types = vec![("T".to_string(), Type::integer())];
        let err = render_single(inst).unwrap_err();
        assert!(matches!(err, EcExportError::PackageTypeParameters { .. }));
    }

    #[test]
    fn a_surviving_for_loop_is_a_hard_error() {
        let ident = gend("i", Type::integer());
        let inst = minimal_instance(
            "O",
            Type::empty(),
            vec![Statement::For(
                ident,
                Expression::integer(0),
                Expression::integer(1),
                CodeBlock(vec![]),
                span(),
            )],
        );
        let err = render_single(inst).unwrap_err();
        assert!(matches!(
            err,
            EcExportError::UnsupportedStatement { construct: "For (loopunroll leaves only unbounded loops, which have no EasyCrypt translation)", .. }
        ));
    }

    #[test]
    fn sampling_a_non_bits_type_is_a_hard_error() {
        let x = gend("x", Type::integer());
        let inst = minimal_instance(
            "O",
            Type::integer(),
            vec![
                Statement::Assignment(
                    Assignment {
                        pattern: Pattern::Ident(x.clone()),
                        rhs: AssignmentRhs::Sample {
                            ty: Type::integer(),
                            sample_name: None,
                            sample_id: None,
                        },
                    },
                    span(),
                ),
                Statement::Return(Some(x.into()), span()),
            ],
        );
        let err = render_single(inst).unwrap_err();
        assert!(matches!(
            err,
            EcExportError::UnsupportedStatement {
                construct: "Sample of a non-Bits type (EasyCrypt export only supports sampling Bits)",
                ..
            }
        ));
    }

    // --- real-project golden files ----------------------------------------

    fn load_variants(dir: &str, theorem_name: &str) -> Vec<PackageVariant> {
        let files: &'static DirectoryFiles =
            Box::leak(Box::new(DirectoryFiles::load(Path::new(dir)).unwrap()));
        let project: &'static DirectoryProject =
            Box::leak(Box::new(DirectoryProject::load(PathBuf::from(dir), files).unwrap()));
        let theorem = project.get_theorem(theorem_name).unwrap();
        let (theorem, _auxs) = EasyCryptTransform.transform_theorem(theorem).unwrap();
        compute_package_variants(&theorem).unwrap()
    }

    fn assert_golden(variant: &PackageVariant, golden_path: &str) {
        let rendered = render_file(&variant.file);
        let full_path = format!("{}/{golden_path}", env!("CARGO_MANIFEST_DIR"));
        let expected = std::fs::read_to_string(&full_path)
            .unwrap_or_else(|e| panic!("failed to read golden file {full_path}: {e}"));
        assert_eq!(rendered, expected, "rendered {} != {full_path}", variant.name);
    }

    fn assert_compiles(dir: &str, file: &str) {
        let full_dir = format!("{}/{dir}", env!("CARGO_MANIFEST_DIR"));
        let full_file = format!("{full_dir}/{file}");
        crate::writers::easycrypt::test_support::assert_compiles(&full_dir, &full_file);
    }

    #[test]
    fn hello_world_variant_names_collapse_fwd_and_fwd2() {
        // Story 14 §3.1 acceptance criterion: a package's `VariantKey` no
        // longer embeds its callees' keys, so `fwd` (wired to `rand`) and
        // `fwd2` (wired to `fwd`) — two instances of the same `Fwd` package
        // with identical `Bits(...)` params — now share one variant, despite
        // being wired to differently-shaped callees. Pre-story-14 this test
        // asserted the opposite (`vec!["Rand", "Fwd_v1", "Fwd_v2"]`) — see
        // `hello_world_fwd_and_fwd2_share_one_key_regardless_of_wiring`
        // below for the direct proof, and the implementation report.
        let variants = load_variants("example-projects/hello-world", "Proof");
        let names: Vec<&str> = variants.iter().map(|v| v.name.as_str()).collect();
        assert_eq!(names, vec!["Rand", "Fwd"]);
    }

    #[test]
    fn hello_world_fwd_and_fwd2_share_one_key_regardless_of_wiring() {
        let dir = "example-projects/hello-world";
        let files: &'static DirectoryFiles =
            Box::leak(Box::new(DirectoryFiles::load(Path::new(dir)).unwrap()));
        let project: &'static DirectoryProject =
            Box::leak(Box::new(DirectoryProject::load(PathBuf::from(dir), files).unwrap()));
        let theorem = project.get_theorem("Proof").unwrap();
        let (theorem, _auxs) = EasyCryptTransform.transform_theorem(theorem).unwrap();

        let medium = theorem.find_game_instance("medium_composition").unwrap().game();
        let big = theorem.find_game_instance("big_composition").unwrap().game();

        let medium_keys = compute_all_keys(medium);
        let big_keys = compute_all_keys(big);

        let medium_fwd_idx = medium.pkgs.iter().position(|p| p.name == "fwd").unwrap();
        let big_fwd_idx = big.pkgs.iter().position(|p| p.name == "fwd").unwrap();
        let big_fwd2_idx = big.pkgs.iter().position(|p| p.name == "fwd2").unwrap();

        assert_eq!(
            medium_keys[medium_fwd_idx], big_keys[big_fwd_idx],
            "medium_composition's `fwd` and big_composition's `fwd` share a key regardless of \
             their callee's shape"
        );
        assert_eq!(
            big_keys[big_fwd_idx], big_keys[big_fwd2_idx],
            "big_composition's `fwd` (wired to rand) and `fwd2` (wired to fwd) are the same \
             package with the same params, so they must share a key too — story 14 §3.1 dropped \
             `imports` from the key entirely"
        );
    }

    #[test]
    fn hello_world_variants_match_golden() {
        let variants = load_variants("example-projects/hello-world", "Proof");
        for v in &variants {
            assert_golden(
                v,
                &format!("testdata/easycrypt/story03/hello-world/Pkg_{}.ec", v.name),
            );
        }
    }

    #[test]
    fn hello_world_rand_compiles_standalone() {
        assert_compiles("testdata/easycrypt/story03/hello-world", "Pkg_Rand.ec");
    }

    #[test]
    fn simple_4whs_variant_names() {
        let variants = load_variants("example-projects/4WHS", "Simple4WHS");
        let names: Vec<&str> = variants.iter().map(|v| v.name.as_str()).collect();
        assert_eq!(
            names,
            // `PRF` no longer needs an escape hatch (story 10 retired the
            // stdlib-collision name list): the module is named plain
            // `PRF`, and its file is `Pkg_PRF.ec` (story 14 §3.6), which
            // cannot collide with EasyCrypt's own `theories/crypto/PRF.eca`
            // or with the `PRF` composition's own `Comp_PRF.ec`.
            vec!["Prot", "KX", "Prot_NoKey", "KX_NoKeys", "PRF", "Prot_NoPrf", "KX_NoPrf"],
            "each of these packages must dedup to exactly one variant across the whole theorem \
             (Real/Ideal/Hybrid0 share one boolean-parametrised KX, etc.)"
        );
    }

    #[test]
    fn simple_4whs_variants_match_golden() {
        let variants = load_variants("example-projects/4WHS", "Simple4WHS");
        for v in &variants {
            assert_golden(v, &format!("testdata/easycrypt/story03/4WHS/Pkg_{}.ec", v.name));
        }
    }

    #[test]
    fn simple_4whs_prot_and_prf_compile_standalone() {
        // Prot and PRF import no oracles, so they don't need their own
        // import interface to typecheck. Every other 4WHS variant here
        // (KX/KX_NoKeys/Prot_NoPrf/KX_NoPrf) imports at least one oracle and
        // so references its own `<Variant>_Imports`; they are golden-file-only
        // checked (no separate `Interfaces.ec` dependency any more — story
        // 14 §3.2/§3.5 — but standalone compilation still needs nothing
        // beyond `Types.ec`).
        assert_compiles("testdata/easycrypt/story03/4WHS", "Pkg_Prot.ec");
        assert_compiles("testdata/easycrypt/story03/4WHS", "Pkg_PRF.ec");
    }

    // --- story 16 acceptance: `Send1` / `Send3` / `NewSession` -------------

    /// The body of `proc <name>(` in `rendered`, up to its closing `  }`.
    fn proc_text<'a>(rendered: &'a str, name: &str) -> &'a str {
        let start = rendered
            .find(&format!("proc {name}("))
            .unwrap_or_else(|| panic!("no proc {name}"));
        let len = rendered[start..].find("\n  }\n").expect("proc is closed");
        &rendered[start..start + len]
    }

    fn full_4whs_kx_noprfkey() -> String {
        let variants = load_variants("example-projects/4WHS", "Full4WHS");
        let v = variants
            .iter()
            .find(|v| v.name == "KX_noprfkey")
            .expect("Full4WHS has a KX_noprfkey variant");
        render_file(&v.file)
    }

    #[test]
    fn full_4whs_send1_has_one_if_per_abort_point_and_no_empty_branch() {
        let rendered = full_4whs_kx_noprfkey();
        let send1 = proc_text(&rendered, "d_Send1");
        // The `State[ctr]` test is written once (story 18 §4), so what is
        // left is the `State` test and the `invoke` guard.
        assert_eq!(send1.matches(" if (").count(), 2, "{send1}");
        assert!(!send1.contains("else"), "no `else` on an abort-only branch:\n{send1}");
        assert!(!send1.contains("ec_done"), "{send1}");
        assert!(!send1.contains("{\n\n"), "no empty branch:\n{send1}");
    }

    fn full_4whs_variant(name: &str) -> String {
        let variants = load_variants("example-projects/4WHS", "Full4WHS");
        let v = variants
            .iter()
            .find(|v| v.name == name)
            .unwrap_or_else(|| panic!("Full4WHS has a {name} variant"));
        render_file(&v.file)
    }

    /// `KX_nochecks::Send3` is the oracle story 16 §1.1 quotes: one join
    /// (after the `if (_mess = 2)` cascade), so exactly one flag guard, and
    /// the tail appears once.
    #[test]
    fn full_4whs_kx_nochecks_send3_has_its_tail_once_and_one_flag_guard() {
        let rendered = full_4whs_variant("KX_nochecks");
        let send3 = proc_text(&rendered, "d_Send3");
        assert_eq!(send3.matches("if (!ec_done)").count(), 1, "{send3}");
        assert_eq!(send3.matches("d_State.[ctr] <- state;").count(), 1, "{send3}");
        assert_eq!(send3.matches("ec_result <- Some msg_;").count(), 1, "{send3}");
    }

    /// `KX_noprfkey::Send3` additionally writes `ReverseMac` *inside*
    /// `if (mess == 2)`, after the `First`/`Second` cascade. Before story 17
    /// that was a second, nested join with its own flag guard; the cascade's
    /// three dominated `Unwrap(sid)` guards were what could terminate it.
    /// With them dropped (story 17 §3.3) the cascade cannot terminate, and
    /// one guard is left. The tail still appears once.
    #[test]
    fn full_4whs_kx_noprfkey_send3_has_its_tail_once_and_one_flag_guard() {
        let rendered = full_4whs_kx_noprfkey();
        let send3 = proc_text(&rendered, "d_Send3");
        assert_eq!(send3.matches("if (!ec_done)").count(), 1, "{send3}");
        assert_eq!(send3.matches("d_State.[ctr] <- state;").count(), 1, "{send3}");
        assert_eq!(send3.matches("ec_result <- Some msg_;").count(), 1, "{send3}");
        assert_eq!(send3.matches("d_ReverseMac.[").count(), 1, "{send3}");
        assert_eq!(send3.matches("(sid = None)").count(), 1, "{send3}");
        assert!(!send3.contains("unwrap_"), "{send3}");
    }

    /// Story 17 §1.2/§4: `KX_nochecks::Send3` (the oracle story 16 §1.1
    /// quotes) declares no `unwrap_N`, tests `sid = None` once, and its
    /// `if (_mess = 2)` cascade is the Domino source's structure. The one
    /// difference from §1.2's listing is the `else { ec_done <- true; }`
    /// arm: `sid = None` still aborts there, and the tail after the join
    /// must not run when it does.
    #[test]
    fn full_4whs_kx_nochecks_send3_cascade_has_one_sid_guard_and_no_temporaries() {
        let rendered = full_4whs_variant("KX_nochecks");
        let send3 = proc_text(&rendered, "d_Send3");
        assert!(!send3.contains("unwrap_"), "{send3}");
        assert_eq!(send3.matches("(sid = None)").count(), 1, "{send3}");
        let cascade = "
        if (_mess = 2) {
          if (!(sid = None)) {
            if (d_First.[oget sid] = None) {
              d_First.[oget sid] <- ctr;
            } else {
              if (d_Second.[oget sid] = None) {
                d_Second.[oget sid] <- ctr;
              }
            }
          } else {
            ec_done <- true;
          }
        }
        if (!ec_done) {
";
        assert!(send3.contains(cascade), "{send3}");
        // the `State[ctr]` unwrap binds `state` directly
        assert!(send3.contains("state <- oget d_State.[ctr];"), "{send3}");
    }

    #[test]
    fn full_4whs_new_session_declares_no_flag() {
        let rendered = full_4whs_kx_noprfkey();
        let new_session = proc_text(&rendered, "d_NewSession");
        assert!(!new_session.contains("ec_done"), "{new_session}");
        // and keeps the statements before its `invoke` (the pre-story-16
        // writer dropped them)
        assert!(new_session.contains("ctr_ <- ctr_ + 1;"), "{new_session}");
    }

    // --- naming / dedup on hand-built fixtures ------------------------------

    fn param_ident(pkg_name: &str, name: &str, ty: Type, assigned: Expression) -> (PackageConstIdentifier, Expression) {
        (
            PackageConstIdentifier::new(name.to_string(), pkg_name.to_string(), ty),
            assigned,
        )
    }

    /// A package with one `Integer` param `n` and no oracles, used to build
    /// tiny compositions for variant-key tests without pulling in a whole
    /// project. `n` is never referenced by a `Bits` width here, so story
    /// 14 §3.1 drops it from the key entirely (it becomes a module `var`
    /// instead) — see [`width_pkg`] for a package where `n` *is* a width.
    fn param_pkg(pkg_name: &str) -> Package {
        Package {
            name: pkg_name.to_string(),
            types: vec![],
            params: vec![("n".to_string(), Type::integer(), span())],
            state: vec![],
            oracles: vec![],
            imports: vec![],
            invariants: vec![],
            file_name: "p.pkg.ssp".to_string(),
            file_contents: String::new(),
        }
    }

    /// Like [`param_pkg`], but `n` is used as a `Bits` width in a state
    /// field, so [`integer_param_used_as_width`] keeps it in the
    /// [`VariantKey`] (story 14 §3.1).
    fn width_pkg(pkg_name: &str) -> Package {
        let n_id = Identifier::PackageIdentifier(PackageIdentifier::Const(
            PackageConstIdentifier::new("n".to_string(), pkg_name.to_string(), Type::integer()),
        ));
        Package {
            name: pkg_name.to_string(),
            types: vec![],
            params: vec![("n".to_string(), Type::integer(), span())],
            state: vec![(
                "x".to_string(),
                Type::bits(CountSpec::Identifier(Box::new(n_id))),
                span(),
            )],
            oracles: vec![],
            imports: vec![],
            invariants: vec![],
            file_name: "p.pkg.ssp".to_string(),
            file_contents: String::new(),
        }
    }

    fn instance_with_n(pkg: Package, pkg_name: &str, inst_name: &str, n_value: i64) -> PackageInstance {
        PackageInstance {
            name: inst_name.to_string(),
            params: vec![param_ident(pkg_name, "n", Type::integer(), Expression::integer(n_value))],
            types: vec![],
            pkg,
        }
    }

    #[test]
    fn distinct_int_param_literals_used_as_a_width_produce_distinct_variants() {
        let comp = Composition {
            pkgs: vec![
                instance_with_n(width_pkg("P"), "P", "a", 1),
                instance_with_n(width_pkg("P"), "P", "b", 2),
            ],
            edges: vec![],
            exports: vec![],
            name: "C".to_string(),
            consts: vec![],
            invariants: vec![],
        };
        let keys = compute_all_keys(&comp);
        assert_ne!(keys[0], keys[1]);

        let mut names = Names::new();
        let discovered = vec![(keys[0].clone(), comp.clone(), 0), (keys[1].clone(), comp.clone(), 1)];
        let name_map = assign_names(&discovered, &mut names).unwrap();
        assert_eq!(name_map[&keys[0]], "P_v1");
        assert_eq!(name_map[&keys[1]], "P_v2");
    }

    #[test]
    fn identical_int_param_literals_produce_one_variant() {
        let comp = Composition {
            pkgs: vec![
                instance_with_n(width_pkg("P"), "P", "a", 7),
                instance_with_n(width_pkg("P"), "P", "b", 7),
            ],
            edges: vec![],
            exports: vec![],
            name: "C".to_string(),
            consts: vec![],
            invariants: vec![],
        };
        let keys = compute_all_keys(&comp);
        assert_eq!(keys[0], keys[1]);
    }

    #[test]
    fn distinct_int_param_literals_not_used_as_a_width_still_produce_one_variant() {
        // Story 14 §3.1 acceptance criterion: a non-width `Integer` param
        // becomes a module `var` (`param_needs_var`), not a key component,
        // so two instances differing only there must share one module —
        // unlike a width param ([`distinct_int_param_literals_used_as_a_width_produce_distinct_variants`]
        // above), which still splits them.
        let comp = Composition {
            pkgs: vec![
                instance_with_n(param_pkg("P"), "P", "a", 1),
                instance_with_n(param_pkg("P"), "P", "b", 2),
            ],
            edges: vec![],
            exports: vec![],
            name: "C".to_string(),
            consts: vec![],
            invariants: vec![],
        };
        let keys = compute_all_keys(&comp);
        assert_eq!(keys[0], keys[1]);
    }
}
