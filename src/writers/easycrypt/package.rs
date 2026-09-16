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
//! The oracle-body translator (§3.3-3.6 of the story) turns Domino's abort
//! statement into EasyCrypt's `T option` return convention: every procedure
//! has a single `ec_result` local and a single trailing `return ec_result;`.
//! `treeify` (run before export) pushes the continuation of every `if` into
//! both branches, but does **not** do this for `Unwrap` or an oracle
//! `invoke` — the translator nests the rest of the block into the `else` of
//! those two itself (§3.5).

use std::collections::{HashMap, HashSet};

use miette::SourceSpan;

use crate::expressions::{Expression, ExpressionKind};
use crate::identifier::{pkg_ident::PackageIdentifier, Identifier};
use crate::package::{Composition, Edge, OracleDef, Package};
use crate::statement::{
    Assignment, AssignmentRhs, CodeBlock, IfThenElse, InvokeOracle, Pattern, Statement,
};
use crate::theorem::Theorem;
use crate::types::{CountSpec, Type, TypeKind};

use super::ast::{EcBlock, EcExpr, EcFile, EcItem, EcLvalue, EcModule, EcProc, EcStmt, EcType, Require};
use super::names::{NameKind, Names};
use super::types::{bits_suffix, translate_expr, translate_type};
use super::EcExportError;

// ---------------------------------------------------------------------------
// Variant keys
// ---------------------------------------------------------------------------

/// The key that determines whether two package instances share one EasyCrypt
/// module (§3.1). Boolean parameters are deliberately absent — they become
/// `init` arguments instead. `imports` embeds the *callee's own key*
/// recursively (not a name), so structural equality of two [`VariantKey`]s is
/// exactly "these two package instances would render to the same module",
/// with no need to resolve names before comparing.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(super) struct VariantKey {
    pkg_name: String,
    int_params: Vec<(String, ParamValue)>,
    fn_params: Vec<(String, ParamValue)>,
    /// One entry per distinct callee (in first-edge order), each with the
    /// ordered list of oracle names imported from it.
    imports: Vec<(Vec<String>, Box<VariantKey>)>,
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
/// by `comp.pkgs`'s position — `comp.ordered_pkgs_idx()` guarantees a
/// callee's key is already computed by the time its caller needs to embed it
/// (§3.1: "rightmost games ... come first").
pub(super) fn compute_all_keys(comp: &Composition) -> Vec<VariantKey> {
    let mut computed: Vec<Option<VariantKey>> = vec![None; comp.pkgs.len()];
    for idx in comp.ordered_pkgs_idx() {
        let key = compute_key(comp, idx, &computed);
        computed[idx] = Some(key);
    }
    computed
        .into_iter()
        .map(|k| k.expect("ordered_pkgs_idx visits every package instance exactly once"))
        .collect()
}

fn compute_key(comp: &Composition, pkg_idx: usize, computed: &[Option<VariantKey>]) -> VariantKey {
    let inst = &comp.pkgs[pkg_idx];

    let mut int_params = Vec::new();
    let mut fn_params = Vec::new();
    for (name, ty, _span) in &inst.pkg.params {
        let assigned = inst
            .params
            .iter()
            .find(|(id, _)| &id.name == name)
            .map(|(_, expr)| expr)
            .expect("a package instance must assign every one of its package's declared params");
        match ty.kind() {
            TypeKind::Integer => int_params.push((name.clone(), canonical_param_value(assigned))),
            TypeKind::Fn(..) => fn_params.push((name.clone(), canonical_param_value(assigned))),
            _ => {}
        }
    }

    // Group edges from this instance by callee, preserving first-occurrence order.
    let mut imports: Vec<(usize, Vec<String>)> = Vec::new();
    for edge in comp.edges.iter().filter(|e| e.from() == pkg_idx) {
        let name = edge.name().to_string();
        match imports.iter_mut().find(|(to, _)| *to == edge.to()) {
            Some((_, names)) => names.push(name),
            None => imports.push((edge.to(), vec![name])),
        }
    }
    let imports = imports
        .into_iter()
        .map(|(to, names)| {
            let callee_key = computed[to]
                .clone()
                .expect("callees are computed before their callers by ordered_pkgs_idx");
            (names, Box::new(callee_key))
        })
        .collect();

    VariantKey {
        pkg_name: inst.pkg.name.clone(),
        int_params,
        fn_params,
        imports,
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

/// One deduplicated package variant, ready to render as `packages/<name>.ec`.
#[derive(Debug, Clone)]
pub struct PackageVariant {
    pub name: String,
    pub file: EcFile,
}

/// Computes every package variant reachable from `theorem`, one [`EcFile`]
/// per distinct variant, deterministic and deduplicated across the whole
/// theorem (§3.1).
pub fn compute_package_variants(theorem: &Theorem<'_>) -> Result<Vec<PackageVariant>, EcExportError> {
    let discovered = discover_variants(theorem);
    let mut names = Names::new();
    let name_map = assign_names(&discovered, &mut names)?;

    let mut out = Vec::with_capacity(discovered.len());
    for (key, comp, idx) in &discovered {
        let name = name_map
            .get(key)
            .expect("every discovered key was named in assign_names")
            .clone();
        let keys = compute_all_keys(comp);
        let file = render_variant(comp, *idx, &name, &keys, &name_map)?;
        out.push(PackageVariant { name, file });
    }
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
    /// Callee package index (within the composition) -> this module's
    /// functor parameter name for it (e.g. `P_Prot`).
    functor_params: HashMap<usize, String>,
}

fn ident_raw_name_and_type(id: &Identifier) -> (String, Type) {
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

fn build_functor_params(
    comp: &Composition,
    pkg_idx: usize,
    keys: &[VariantKey],
    name_map: &HashMap<VariantKey, String>,
) -> Result<(Vec<(String, String)>, HashMap<usize, String>), EcExportError> {
    let mut params = Vec::new();
    let mut lookup = HashMap::new();
    // One registry shared across every functor parameter of this module: two
    // callee instances whose names mangle to the same `P_<...>` would
    // otherwise silently produce two identically-named functor parameters
    // (illegal EasyCrypt) instead of the hard collision error the naming
    // convention promises (`docs/stories/easycrypt/00-overview.md` §3:
    // "A residual collision is a hard error").
    let mut functor_names = Names::new();
    for edge in comp.edges.iter().filter(|e| e.from() == pkg_idx) {
        let to = edge.to();
        if lookup.contains_key(&to) {
            continue;
        }
        let inst_name = &comp.pkgs[to].name;
        let mangled_inst = functor_names.mangle(NameKind::Module, inst_name)?;
        let param_name = format!("P_{mangled_inst}");
        let callee_variant = name_map
            .get(&keys[to])
            .expect("every callee's variant name was computed before its caller is rendered")
            .clone();
        params.push((param_name.clone(), format!("Interfaces.{callee_variant}_i")));
        lookup.insert(to, param_name);
    }
    Ok((params, lookup))
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
    keys: &[VariantKey],
    name_map: &HashMap<VariantKey, String>,
) -> Result<EcFile, EcExportError> {
    let inst = &comp.pkgs[pkg_idx];
    let pkg = &inst.pkg;
    let key = &keys[pkg_idx];

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

    let (functor_param_decls, functor_lookup) = build_functor_params(comp, pkg_idx, keys, name_map)?;
    let mut scope = PackageScope {
        names: Names::new(),
        functor_params: functor_lookup,
    };

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

    let mut requires = vec![Require {
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
    if !module.params.is_empty() {
        requires.push(Require {
            import: false,
            names: vec!["Interfaces".to_string()],
        });
    }

    Ok(EcFile {
        header: vec![variant_comment(key, variant_name)],
        requires,
        items: vec![EcItem::Module(module)],
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
    let (raw, ty) = ident_raw_name_and_type(id);
    if seen.contains(&raw) {
        return Ok(());
    }
    seen.insert(raw.clone());
    let mangled = scope.names.mangle(NameKind::Var, &raw)?;
    let ecty = translate_type(&ty, span)?;
    out.push((mangled, ecty));
    Ok(())
}

fn build_proc(scope: &mut PackageScope, oracle: &OracleDef) -> Result<EcProc, EcExportError> {
    let span = oracle.file_pos;
    let ret_ec_ty = translate_type(&oracle.sig.ty, span)?;
    let ret_option_ty = EcType::Option(Box::new(ret_ec_ty.clone()));

    let mut args = Vec::new();
    for (name, ty) in &oracle.sig.args {
        let mangled = scope.names.mangle(NameKind::Var, name)?;
        args.push((mangled, translate_type(ty, span)?));
    }

    let mut locals = Vec::new();
    let mut seen = HashSet::new();
    collect_locals(&oracle.code, scope, &mut locals, &mut seen)?;

    let mut ec_locals = vec![(
        "ec_result".to_string(),
        ret_option_ty.clone(),
        Some(EcExpr::None_(ret_ec_ty)),
    )];
    for (name, ty) in locals {
        ec_locals.push((name, ty, None));
    }

    let mut translator = OracleTranslator {
        scope,
        temp_ctr: 0,
        temp_decls: Vec::new(),
    };
    let body = translator.translate_block(&oracle.code.0)?;
    for (name, ty) in translator.temp_decls {
        ec_locals.push((name, ty, None));
    }

    let proc_name = scope.names.mangle(NameKind::Proc, &oracle.sig.name)?;

    Ok(EcProc {
        name: proc_name,
        args,
        ret: ret_option_ty,
        locals: ec_locals,
        body,
        ret_expr: Some(EcExpr::Var("ec_result".to_string())),
    })
}

struct OracleTranslator<'a> {
    scope: &'a mut PackageScope,
    temp_ctr: usize,
    /// `ec_r<N>` proc-local declarations, collected as they are introduced
    /// during translation (their type is only known once the corresponding
    /// call/sample is translated) and appended to [`EcProc::locals`]
    /// afterwards — EasyCrypt requires every proc-local, including these
    /// generated temporaries, to have an explicit `var` declaration.
    temp_decls: Vec<(String, EcType)>,
}

impl OracleTranslator<'_> {
    /// Declares and returns a fresh `ec_r<N>` temporary of type `ty`.
    fn declare_temp(&mut self, ty: EcType) -> String {
        self.temp_ctr += 1;
        let name = format!("ec_r{}", self.temp_ctr);
        self.temp_decls.push((name.clone(), ty));
        name
    }

    fn translate_e(&mut self, expr: &Expression, span: SourceSpan) -> Result<EcExpr, EcExportError> {
        let mut resolver = |id: &Identifier, _s: SourceSpan| -> Result<EcExpr, EcExportError> {
            let (raw, _ty) = ident_raw_name_and_type(id);
            let mangled = self.scope.names.mangle(NameKind::Var, &raw)?;
            Ok(EcExpr::Var(mangled))
        };
        translate_expr(expr, span, &mut resolver)
    }

    fn resolve_name(&mut self, id: &Identifier) -> Result<String, EcExportError> {
        let (raw, _ty) = ident_raw_name_and_type(id);
        Ok(self.scope.names.mangle(NameKind::Var, &raw)?)
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

    /// `Unwrap`'s operand must be `Maybe`-typed by construction; extracts and
    /// translates the inner type, for the `None<:T>` annotation in the
    /// nested-if abort check (§3.5).
    fn maybe_inner_ec_type(&self, expr: &Expression, span: SourceSpan) -> Result<EcType, EcExportError> {
        let TypeKind::Maybe(inner) = expr.get_type().into_kind() else {
            unreachable!("Unwrap's operand is always Maybe-typed")
        };
        translate_type(&inner, span)
    }

    /// Translates `stmts`, implementing §3.3-3.5: `Return`/`Abort` end the
    /// current block immediately (discarding anything syntactically
    /// following them — `treeify` can leave unreachable statements after an
    /// already-terminal branch when it blindly appends the continuation of a
    /// *later* `if`/`assert` into a branch that already returned or
    /// aborted; see the implementation report), and `Unwrap`/`Invoke` nest
    /// the rest of the block into the `else` of a freshly built `if`.
    fn translate_block(&mut self, stmts: &[Statement]) -> Result<EcBlock, EcExportError> {
        let mut out = Vec::new();
        let mut i = 0;
        while i < stmts.len() {
            match &stmts[i] {
                Statement::Abort(_) => return Ok(EcBlock(out)),

                Statement::Return(value, span) => {
                    let rhs = match value {
                        Some(e) => EcExpr::Some_(Box::new(self.translate_e(e, *span)?)),
                        None => EcExpr::Some_(Box::new(EcExpr::Unit)),
                    };
                    out.push(EcStmt::Assign {
                        lhs: EcLvalue::Var("ec_result".to_string()),
                        rhs,
                    });
                    return Ok(EcBlock(out));
                }

                Statement::IfThenElse(ite) => {
                    let cond = self.translate_e(&ite.cond, ite.full_span)?;
                    let then_block = self.translate_block(&ite.then_block.0)?;
                    let else_block = self.translate_block(&ite.else_block.0)?;
                    out.push(EcStmt::If {
                        cond,
                        then_block,
                        else_block: Some(else_block),
                    });
                    return Ok(EcBlock(out));
                }

                Statement::For(_, _, _, _, span) => {
                    return Err(EcExportError::UnsupportedStatement {
                        construct: "For (loopunroll leaves only unbounded loops, which have no EasyCrypt translation)",
                        span: *span,
                    });
                }

                Statement::Assignment(Assignment { pattern, rhs }, span) => {
                    let span = *span;
                    match rhs {
                        AssignmentRhs::Expression(expr) => {
                            if let (Pattern::Ident(id), ExpressionKind::Unwrap(inner)) =
                                (pattern, expr.kind())
                            {
                                let inner_ec = self.translate_e(inner, span)?;
                                let inner_ty = self.maybe_inner_ec_type(inner, span)?;
                                let name = self.resolve_name(id)?;
                                let cond = EcExpr::Binop {
                                    op: super::ast::EcBinop::Eq,
                                    lhs: Box::new(inner_ec.clone()),
                                    rhs: Box::new(EcExpr::None_(inner_ty)),
                                };
                                let mut rest = self.translate_block(&stmts[i + 1..])?;
                                let mut else_stmts = vec![EcStmt::Assign {
                                    lhs: EcLvalue::Var(name),
                                    rhs: EcExpr::Oget(Box::new(inner_ec)),
                                }];
                                else_stmts.append(&mut rest.0);
                                out.push(EcStmt::If {
                                    cond,
                                    then_block: EcBlock(vec![]),
                                    else_block: Some(EcBlock(else_stmts)),
                                });
                                return Ok(EcBlock(out));
                            }

                            match pattern {
                                Pattern::Ident(id) => {
                                    let name = self.resolve_name(id)?;
                                    let value = self.translate_e(expr, span)?;
                                    out.push(EcStmt::Assign {
                                        lhs: EcLvalue::Var(name),
                                        rhs: value,
                                    });
                                }
                                Pattern::Tuple(ids) => {
                                    let names = ids
                                        .iter()
                                        .map(|id| self.resolve_name(id))
                                        .collect::<Result<Vec<_>, _>>()?;
                                    let value = self.translate_e(expr, span)?;
                                    out.push(EcStmt::Assign {
                                        lhs: EcLvalue::Tuple(names),
                                        rhs: value,
                                    });
                                }
                                Pattern::Table { ident, index } => {
                                    out.extend(self.translate_table_write(ident, index, expr, span)?);
                                }
                            }
                            i += 1;
                        }

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
                                    let tmp = self.declare_temp(sample_ty);
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
                            i += 1;
                        }

                        AssignmentRhs::Invoke { args, edge, return_type, .. } => {
                            return self.translate_invoke(
                                Some(pattern),
                                args,
                                edge,
                                return_type.as_ref(),
                                span,
                                &stmts[i + 1..],
                            );
                        }
                    }
                }

                Statement::InvokeOracle(InvokeOracle { args, edge, file_pos, .. }) => {
                    return self.translate_invoke(None, args, edge, None, *file_pos, &stmts[i + 1..]);
                }
            }
        }
        Ok(EcBlock(out))
    }

    /// `T[k] <- rhs` (§3.4). `rhs` is never `Unwrap`-headed here:
    /// `unwrapify` hoists every `Unwrap` — including one that is a table
    /// assignment's entire right-hand side — into its own preceding
    /// `Ident`-pattern statement.
    fn translate_table_write(
        &mut self,
        ident: &Identifier,
        index: &Expression,
        rhs_expr: &Expression,
        span: SourceSpan,
    ) -> Result<Vec<EcStmt>, EcExportError> {
        let map = self.resolve_name(ident)?;
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
                lhs: EcLvalue::Var(map.clone()),
                rhs: EcExpr::MapRem {
                    map: Box::new(EcExpr::Var(map)),
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
                    map: Box::new(EcExpr::Var(map.clone())),
                    key: Box::new(key.clone()),
                    value: Box::new(EcExpr::Oget(Box::new(rhs))),
                };
                let then_expr = EcExpr::MapRem {
                    map: Box::new(EcExpr::Var(map.clone())),
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

    /// `y <- invoke O(args)` / bare `invoke O(args)` (§3.5). `pattern` is
    /// `None` for a bare `InvokeOracle` (the return value is discarded, but
    /// the abort still has to propagate).
    fn translate_invoke(
        &mut self,
        pattern: Option<&Pattern>,
        args: &[Expression],
        edge: &Option<Edge>,
        explicit_return_type: Option<&Type>,
        span: SourceSpan,
        rest: &[Statement],
    ) -> Result<EcBlock, EcExportError> {
        let edge = edge
            .as_ref()
            .expect("resolveoracles attaches a resolved Edge to every invoke reaching export");

        let module = self
            .scope
            .functor_params
            .get(&edge.to())
            .expect("every edge's callee has a precomputed functor parameter")
            .clone();
        // A fresh registry is correct (not a collision-detection gap) here:
        // this reproduces the callee's own `Proc`-namespace mangling of one
        // name, and that namespace's actual collision-freedom was already
        // validated when the callee itself was rendered — `compute_key`
        // always discovers a callee before its caller (`ordered_pkgs_idx`),
        // so `compute_package_variants` would already have propagated a
        // `NameError::Collision` from the callee's own `build_proc` before
        // this call site is ever reached.
        let proc = Names::new().mangle(NameKind::Proc, &edge.sig().name)?;

        let translated_args = args
            .iter()
            .map(|a| self.translate_e(a, span))
            .collect::<Result<Vec<_>, _>>()?;

        let result_ec_ty = match explicit_return_type {
            Some(t) => translate_type(t, span)?,
            None => translate_type(&edge.sig().ty, span)?,
        };

        let tmp = self.declare_temp(EcType::Option(Box::new(result_ec_ty.clone())));
        let mut out = vec![EcStmt::Call {
            lhs: Some(EcLvalue::Var(tmp.clone())),
            module,
            proc,
            args: translated_args,
        }];
        let cond = EcExpr::Binop {
            op: super::ast::EcBinop::Eq,
            lhs: Box::new(EcExpr::Var(tmp.clone())),
            rhs: Box::new(EcExpr::None_(result_ec_ty)),
        };

        let mut else_stmts = Vec::new();
        if let Some(pattern) = pattern {
            let unwrapped = EcExpr::Oget(Box::new(EcExpr::Var(tmp)));
            match pattern {
                Pattern::Ident(id) => {
                    let name = self.resolve_name(id)?;
                    else_stmts.push(EcStmt::Assign {
                        lhs: EcLvalue::Var(name),
                        rhs: unwrapped,
                    });
                }
                Pattern::Tuple(ids) => {
                    let names = ids
                        .iter()
                        .map(|id| self.resolve_name(id))
                        .collect::<Result<Vec<_>, _>>()?;
                    else_stmts.push(EcStmt::Assign {
                        lhs: EcLvalue::Tuple(names),
                        rhs: unwrapped,
                    });
                }
                Pattern::Table { ident, index } => {
                    let map = self.resolve_name(ident)?;
                    let key = self.translate_e(index, span)?;
                    else_stmts.push(EcStmt::Assign {
                        lhs: EcLvalue::MapSet { map, key },
                        rhs: unwrapped,
                    });
                }
            }
        }

        let mut rest_translated = self.translate_block(rest)?;
        else_stmts.append(&mut rest_translated.0);

        out.push(EcStmt::If {
            cond,
            then_block: EcBlock(vec![]),
            else_block: Some(EcBlock(else_stmts)),
        });
        Ok(EcBlock(out))
    }
}

#[cfg(test)]
mod tests {
    use std::path::{Path, PathBuf};

    use crate::identifier::pkg_ident::PackageConstIdentifier;
    use crate::package::OracleSig;
    use crate::packageinstance::PackageInstance;
    use crate::project::{DirectoryFiles, DirectoryProject, Project};
    use crate::transforms::theorem_transforms::EquivalenceTransform;
    use crate::transforms::TheoremTransform;

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
        let keys = compute_all_keys(&comp);
        let name_map: HashMap<VariantKey, String> =
            HashMap::from([(keys[0].clone(), "Test".to_string())]);
        render_variant(&comp, 0, "Test", &keys, &name_map)
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
        let (theorem, _auxs) = EquivalenceTransform.transform_theorem(theorem).unwrap();
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
    fn hello_world_variant_names_show_fwd_fwd2_split() {
        // Acceptance criteria says "fwd and fwd2 produce one variant
        // (identical parameters)". Empirically they do not: in
        // `BigComposition`, `fwd` imports its `UsefulOracle` from a
        // Rand-shaped callee (`rand`) while `fwd2` imports it from a
        // Fwd-shaped callee (`fwd`), so by §3.1's own rule ("two instances
        // of one package wired to differently-shaped callees are different
        // variants") they get different functor signatures and cannot share
        // a module. `fwd` *does* dedup across `medium_composition`,
        // `medium_composition_more_oracles` and `big_composition` (all wired
        // to Rand) into one shared key -- see
        // `hello_world_fwd_shares_a_key_across_compositions_but_not_with_fwd2`
        // below for the proof, and the implementation report.
        let variants = load_variants("example-projects/hello-world", "Proof");
        let names: Vec<&str> = variants.iter().map(|v| v.name.as_str()).collect();
        assert_eq!(names, vec!["Rand", "Fwd_v1", "Fwd_v2"]);
    }

    #[test]
    fn hello_world_fwd_shares_a_key_across_compositions_but_not_with_fwd2() {
        let dir = "example-projects/hello-world";
        let files: &'static DirectoryFiles =
            Box::leak(Box::new(DirectoryFiles::load(Path::new(dir)).unwrap()));
        let project: &'static DirectoryProject =
            Box::leak(Box::new(DirectoryProject::load(PathBuf::from(dir), files).unwrap()));
        let theorem = project.get_theorem("Proof").unwrap();
        let (theorem, _auxs) = EquivalenceTransform.transform_theorem(theorem).unwrap();

        let medium = theorem.find_game_instance("medium_composition").unwrap().game();
        let big = theorem.find_game_instance("big_composition").unwrap().game();

        let medium_keys = compute_all_keys(medium);
        let big_keys = compute_all_keys(big);

        let medium_fwd_idx = medium.pkgs.iter().position(|p| p.name == "fwd").unwrap();
        let big_fwd_idx = big.pkgs.iter().position(|p| p.name == "fwd").unwrap();
        let big_fwd2_idx = big.pkgs.iter().position(|p| p.name == "fwd2").unwrap();

        assert_eq!(
            medium_keys[medium_fwd_idx], big_keys[big_fwd_idx],
            "medium_composition's `fwd` and big_composition's `fwd` are both wired to a \
             Rand-shaped callee and must dedup to one key"
        );
        assert_ne!(
            big_keys[big_fwd_idx], big_keys[big_fwd2_idx],
            "big_composition's `fwd` (wired to rand) and `fwd2` (wired to fwd) are wired to \
             differently-shaped callees and must NOT share a key"
        );
    }

    #[test]
    fn hello_world_variants_match_golden() {
        let variants = load_variants("example-projects/hello-world", "Proof");
        for v in &variants {
            assert_golden(
                v,
                &format!("testdata/easycrypt/story03/hello-world/{}.ec", v.name),
            );
        }
    }

    #[test]
    fn hello_world_rand_compiles_standalone() {
        assert_compiles("testdata/easycrypt/story03/hello-world", "Rand.ec");
    }

    #[test]
    fn simple_4whs_variant_names() {
        let variants = load_variants("example-projects/4WHS", "Simple4WHS");
        let names: Vec<&str> = variants.iter().map(|v| v.name.as_str()).collect();
        assert_eq!(
            names,
            // `PRF` mangles to `M_PRF`: it collides with EasyCrypt's own
            // `theories/crypto/PRF.eca` (`names.rs`'s
            // `RESERVED_STDLIB_THEORY_NAMES`, found in story 04).
            vec!["Prot", "KX", "Prot_NoKey", "KX_NoKeys", "M_PRF", "Prot_NoPrf", "KX_NoPrf"],
            "each of these packages must dedup to exactly one variant across the whole theorem \
             (Real/Ideal/Hybrid0 share one boolean-parametrised KX, etc.)"
        );
    }

    #[test]
    fn simple_4whs_variants_match_golden() {
        let variants = load_variants("example-projects/4WHS", "Simple4WHS");
        for v in &variants {
            assert_golden(v, &format!("testdata/easycrypt/story03/4WHS/{}.ec", v.name));
        }
    }

    #[test]
    fn simple_4whs_prot_and_prf_compile_standalone() {
        // Prot and PRF import no oracles, so they don't need story 04's
        // Interfaces.ec to typecheck. Every other 4WHS variant here
        // (KX/KX_NoKeys/Prot_NoPrf/KX_NoPrf) imports at least one oracle and
        // so references `Interfaces.*_i`; they are golden-file-only checked
        // until story 04 provides Interfaces.ec. `PRF` mangles to `M_PRF`
        // (`names.rs`'s `RESERVED_STDLIB_THEORY_NAMES`, found in story 04).
        assert_compiles("testdata/easycrypt/story03/4WHS", "Prot.ec");
        assert_compiles("testdata/easycrypt/story03/4WHS", "M_PRF.ec");
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
    /// project.
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

    fn instance_with_n(pkg_name: &str, inst_name: &str, n_value: i64) -> PackageInstance {
        PackageInstance {
            name: inst_name.to_string(),
            params: vec![param_ident(pkg_name, "n", Type::integer(), Expression::integer(n_value))],
            types: vec![],
            pkg: param_pkg(pkg_name),
        }
    }

    #[test]
    fn distinct_int_param_literals_produce_distinct_variants() {
        let comp = Composition {
            pkgs: vec![instance_with_n("P", "a", 1), instance_with_n("P", "b", 2)],
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
            pkgs: vec![instance_with_n("P", "a", 7), instance_with_n("P", "b", 7)],
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
