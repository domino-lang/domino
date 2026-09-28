// SPDX-License-Identifier: MIT OR Apache-2.0

//! A readable, fully-inlined listing of one exported oracle, for read-only
//! views (`domino html`).
//!
//! [`super::ir`]'s listing gives every IR statement its own labelled line for
//! the debugger, so it keeps each `invoke` and the frame it opens. This one is
//! written for a person reading the code instead:
//!
//! - **No `invoke`.** A call becomes a `// inlined Instance.Oracle` comment
//!   followed by the callee's body, indented one level; the callee's
//!   `return e` becomes `<bind> <- e`. `returnify` only guarantees a return at
//!   the end of every path, so a return the callee can run before its last
//!   statement is followed by `goto end_Instance_Oracle;`, a jump to a label
//!   printed right after the inlined body.
//! - **Scoping.** A callee's locals (arguments, body locals, loop variables)
//!   are renamed (`r` → `r_2`) when an enclosing frame already uses the name,
//!   so reading the flattened code never mixes up the caller's and the
//!   callee's variables. Package state needs no renaming: it is printed as
//!   `Instance.field`.
//! - **Less noise.** A parameter the callee never assigns, called with an
//!   identifier or a literal, is replaced by that argument in the callee's
//!   body instead of getting a `param <- arg` line; the argument cannot change
//!   while the callee runs (caller locals are out of the callee's reach, and a
//!   composition is acyclic, so the callee cannot reach the caller's state
//!   either). Self-assignments `x <- x` are dropped.
//! - **Proof parameters.** The theorem constants the proof path fixes
//!   (`[b ↦ false]`) are substituted, and a branch or assert whose condition
//!   becomes a literal is resolved to the side that runs.
//!
//! The game instance must have been run through
//! [`crate::transforms::theorem_transforms::ViewTransform`] (for resolved
//! oracle edges). Loops `loopunroll` could not unroll are printed as `for`
//! blocks.

use std::cell::OnceCell;
use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;

use crate::{
    expressions::{Expression, ExpressionKind},
    identifier::{pkg_ident::PackageIdentifier, theorem_ident::TheoremIdentifier, Identifier},
    package::{Composition, Edge, OracleDef, PackageInstance},
    statement::{Assignment, AssignmentRhs, InvokeOracle, Pattern, Statement},
    theorem::GameInstance,
};

use super::ir::{
    render_expr_with, render_pattern, render_signature, render_type, resolve_const, InlineError,
    MAX_INLINE_DEPTH,
};

/// Render `oracle_name` (an *exported* name) of `game_inst` inlined across
/// package boundaries. `consts` maps theorem constants to the literal the
/// proof path assigns them. `lossy` is as in
/// [`super::ir::inline_oracle_rendered`].
pub fn render_oracle_view(
    game_inst: &GameInstance,
    oracle_name: &str,
    lossy: bool,
    consts: &[(String, Expression)],
) -> Result<String, InlineError> {
    let comp = game_inst.game();
    let export = comp
        .exports
        .iter()
        .find(|export| export.name() == oracle_name)
        .ok_or_else(|| InlineError::OracleNotExported {
            oracle: oracle_name.to_string(),
            game_inst: game_inst.name().to_string(),
        })?;
    let entry_inst = &comp.pkgs[export.to()];
    let odef = find_oracle(entry_inst, &export.sig().name)?;

    let mut view = View {
        comp,
        consts,
        lossy,
        labels: HashSet::new(),
        text: String::new(),
    };
    let frame = Frame::new(
        entry_inst,
        odef,
        &odef.code.0,
        &HashSet::new(),
        HashMap::new(),
        HashMap::new(),
        Ret::Top,
        0,
    );
    view.emit(0, &format!("{} {{", render_signature(export.sig())));
    view.block(&odef.code.0, &frame, 1, true)?;
    view.emit(0, "}");
    Ok(view.text)
}

fn find_oracle<'p>(inst: &'p PackageInstance, name: &str) -> Result<&'p OracleDef, InlineError> {
    inst.pkg
        .oracles
        .iter()
        .find(|odef| odef.sig.name == name)
        .ok_or_else(|| InlineError::CalleeNotFound {
            oracle: name.to_string(),
            pkg_inst: inst.name.clone(),
        })
}

/// One oracle being rendered: the entry oracle or an inlined callee.
struct Frame {
    inst: String,
    /// `Instance.Oracle`, for comments.
    name: String,
    /// Display name of every local of this frame.
    names: HashMap<String, String>,
    /// Parameters replaced by the caller's argument.
    aliases: HashMap<String, Expression>,
    /// Every name visible here: the enclosing frames' and this frame's. A
    /// callee's locals must not reuse any of them.
    scope: HashSet<String>,
    ret: Ret,
    depth: usize,
    /// The label after the inlined body, set by the first early return.
    end: OnceCell<String>,
}

/// What `return` means in a frame.
enum Ret {
    /// The entry oracle: `return` really returns.
    Top,
    /// An inlined callee: `return e` assigns `e` to the caller's bind, if any.
    Bind(Option<String>),
}

impl Frame {
    /// `outer` is the enclosing frames' scope; `aliases` the parameters the
    /// caller substitutes; `fixed` the locals that take a caller's name (see
    /// [`return_names`]). `body` is the code that will be rendered.
    #[allow(clippy::too_many_arguments)]
    fn new(
        inst: &PackageInstance,
        odef: &OracleDef,
        body: &[Statement],
        outer: &HashSet<String>,
        aliases: HashMap<String, Expression>,
        fixed: HashMap<String, String>,
        ret: Ret,
        depth: usize,
    ) -> Self {
        let mut own: Vec<String> = odef.sig.args.iter().map(|(n, _)| n.clone()).collect();
        collect_locals(body, &mut own);
        own.retain(|n| !aliases.contains_key(n));

        // Names that don't clash keep their spelling; clashing ones get a
        // fresh name that avoids both the enclosing scope and this frame.
        let mut scope = outer.clone();
        scope.extend(
            own.iter()
                .filter(|n| !outer.contains(*n) && !fixed.contains_key(*n))
                .cloned(),
        );
        let mut names = HashMap::new();
        for name in own {
            let display = if let Some(display) = fixed.get(&name) {
                display.clone()
            } else if outer.contains(&name) {
                let fresh = fresh_name(&name, &scope);
                scope.insert(fresh.clone());
                fresh
            } else {
                name.clone()
            };
            names.insert(name, display);
        }

        Frame {
            inst: inst.name.clone(),
            name: format!("{}.{}", inst.name, odef.sig.name),
            names,
            aliases,
            scope,
            ret,
            depth,
            end: OnceCell::new(),
        }
    }

    /// `id` as it is spelled in this frame, or `None` if it is not a local.
    fn local(&self, id: &Identifier) -> Option<Expression> {
        let name = local_name(id)?;
        if let Some(arg) = self.aliases.get(name) {
            return Some(arg.clone());
        }
        let display = self.names.get(name).map_or(name, String::as_str);
        Some(Identifier::Generated(display.to_string(), id.get_type()).into())
    }

    /// Like [`Self::local`], for places that need an identifier (patterns,
    /// table bases); non-locals are returned unchanged.
    fn ident(&self, id: &Identifier) -> Identifier {
        match self.local(id).map(Expression::into_identifier) {
            Some(Some(renamed)) => renamed,
            _ => id.clone(),
        }
    }
}

/// When every `return` of the callee returns the same local `x` (or tuple of
/// locals) and the caller binds the result to a local `y` (or tuple of
/// locals), `x` can simply be spelled `y`: the final `y <- x` disappears.
/// Writing `y` early is invisible, because the callee cannot read the caller's
/// locals except through a parameter alias, which is ruled out here.
///
/// Returns the callee locals to rename, mapped to the caller's display names.
fn return_names(
    body: &[Statement],
    odef: &OracleDef,
    bind: &Pattern,
    caller: &Frame,
    aliases: &HashMap<String, Expression>,
) -> HashMap<String, String> {
    fn returns<'b>(block: &'b [Statement], out: &mut Vec<Option<&'b Expression>>) {
        for stmt in block {
            match stmt {
                Statement::Return(value, _) => out.push(value.as_ref()),
                Statement::IfThenElse(ite) => {
                    returns(&ite.then_block.0, out);
                    returns(&ite.else_block.0, out);
                }
                Statement::For(_, _, _, body, _) => returns(&body.0, out),
                _ => {}
            }
        }
    }

    let targets: Option<Vec<&String>> = match bind {
        Pattern::Ident(id) => Some(vec![id]),
        Pattern::Tuple(ids) => Some(ids.iter().collect()),
        Pattern::Table { .. } => None,
    }
    .and_then(|ids| {
        ids.into_iter()
            .map(|id| caller.names.get(local_name(id)?))
            .collect()
    });

    let mut values = Vec::new();
    returns(body, &mut values);
    let sources: Option<Vec<&str>> = match values.split_first() {
        Some((Some(first), rest)) if rest.iter().all(|v| *v == Some(*first)) => {
            let ids: Vec<&Expression> = match first.kind() {
                ExpressionKind::Tuple(items) => items.iter().collect(),
                _ => vec![first],
            };
            ids.into_iter()
                .map(|e| local_name(e.as_identifier()?))
                .collect()
        }
        _ => None,
    };

    let (Some(targets), Some(sources)) = (targets, sources) else {
        return HashMap::new();
    };
    let distinct = |names: &[&str]| names.iter().collect::<HashSet<_>>().len() == names.len();
    let targets: Vec<&str> = targets.into_iter().map(String::as_str).collect();
    let is_param = |name: &str| odef.sig.args.iter().any(|(arg, _)| arg == name);
    let aliased_target = aliases.values().any(|arg| {
        arg.as_identifier()
            .and_then(local_name)
            .is_some_and(|name| targets.contains(&name))
    });
    if targets.len() != sources.len()
        || !distinct(&targets)
        || !distinct(&sources)
        || sources.iter().any(|name| is_param(name))
        || aliased_target
    {
        return HashMap::new();
    }
    sources
        .into_iter()
        .zip(targets)
        .map(|(source, target)| (source.to_string(), target.to_string()))
        .collect()
}

/// `name_2`, `name_3`, … (`pk_2` for `pk_`), the first one not in `taken`.
fn fresh_name(name: &str, taken: &HashSet<String>) -> String {
    let sep = if name.ends_with('_') { "" } else { "_" };
    (2..)
        .map(|k| format!("{name}{sep}{k}"))
        .find(|n| !taken.contains(n))
        .expect("an unbounded range has a fresh name")
}

/// The name of a frame-local identifier; `None` for state, constants and `_`.
fn local_name(id: &Identifier) -> Option<&str> {
    let name = match id {
        Identifier::Generated(name, _) => name,
        Identifier::PackageIdentifier(PackageIdentifier::Local(l)) => &l.name,
        Identifier::PackageIdentifier(PackageIdentifier::OracleArg(a)) => &a.name,
        Identifier::PackageIdentifier(PackageIdentifier::CodeLoopVar(l)) => &l.name,
        _ => return None,
    };
    (name != "_").then_some(name.as_str())
}

/// Appends every local mentioned in `block` to `out`, in order of first
/// appearance.
fn collect_locals(block: &[Statement], out: &mut Vec<String>) {
    let mut add = |id: &Identifier| {
        if let Some(name) = local_name(id) {
            if !out.iter().any(|n| n == name) {
                out.push(name.to_string());
            }
        }
    };
    for_each_ident(block, &mut add);
}

/// Calls `f` on every identifier in `block`: patterns, expressions, loop
/// variables.
fn for_each_ident(block: &[Statement], f: &mut impl FnMut(&Identifier)) {
    fn expr(e: &Expression, f: &mut impl FnMut(&Identifier)) {
        let (ids, _) = e.mapfold(Vec::new(), |mut acc, sub| {
            match sub.kind() {
                ExpressionKind::Identifier(id) | ExpressionKind::TableAccess(id, _) => {
                    acc.push(id.clone())
                }
                _ => {}
            }
            (acc, sub)
        });
        ids.iter().for_each(f);
    }
    fn pattern(p: &Pattern, f: &mut impl FnMut(&Identifier)) {
        match p {
            Pattern::Ident(id) => f(id),
            Pattern::Table { ident, index } => {
                f(ident);
                expr(index, f);
            }
            Pattern::Tuple(ids) => ids.iter().for_each(f),
        }
    }
    for stmt in block {
        match stmt {
            Statement::Abort(_) | Statement::Return(None, _) => {}
            Statement::Return(Some(e), _) => expr(e, f),
            Statement::Assignment(Assignment { pattern: p, rhs }, _) => {
                pattern(p, f);
                match rhs {
                    AssignmentRhs::Expression(e) => expr(e, f),
                    AssignmentRhs::Invoke { args, .. } => args.iter().for_each(|a| expr(a, f)),
                    AssignmentRhs::Sample { .. } => {}
                }
            }
            Statement::InvokeOracle(InvokeOracle { args, .. }) => {
                args.iter().for_each(|a| expr(a, f))
            }
            Statement::IfThenElse(ite) => {
                expr(&ite.cond, f);
                for_each_ident(&ite.then_block.0, f);
                for_each_ident(&ite.else_block.0, f);
            }
            Statement::For(var, lower, upper, body, _) => {
                f(var);
                expr(lower, f);
                expr(upper, f);
                for_each_ident(&body.0, f);
            }
        }
    }
}

/// Names of the locals `block` assigns to (including loop variables).
fn assigned_locals(block: &[Statement]) -> HashSet<String> {
    fn add(id: &Identifier, out: &mut HashSet<String>) {
        if let Some(name) = local_name(id) {
            out.insert(name.to_string());
        }
    }
    fn walk(block: &[Statement], out: &mut HashSet<String>) {
        for stmt in block {
            match stmt {
                Statement::Assignment(Assignment { pattern, .. }, _) => match pattern {
                    Pattern::Ident(id) | Pattern::Table { ident: id, .. } => add(id, out),
                    Pattern::Tuple(ids) => ids.iter().for_each(|id| add(id, out)),
                },
                Statement::IfThenElse(ite) => {
                    walk(&ite.then_block.0, out);
                    walk(&ite.else_block.0, out);
                }
                Statement::For(var, _, _, body, _) => {
                    add(var, out);
                    walk(&body.0, out);
                }
                Statement::Abort(_) | Statement::Return(..) | Statement::InvokeOracle(_) => {}
            }
        }
    }
    let mut out = HashSet::new();
    walk(block, &mut out);
    out
}

fn as_bool(e: &Expression) -> Option<bool> {
    match e.kind() {
        ExpressionKind::BooleanLiteral(b) => Some(b == "true"),
        _ => None,
    }
}

fn is_literal(e: &Expression) -> bool {
    matches!(
        e.kind(),
        ExpressionKind::BooleanLiteral(_)
            | ExpressionKind::IntegerLiteral(_)
            | ExpressionKind::StringLiteral(_)
            | ExpressionKind::BitsLiteral(..)
            | ExpressionKind::None(_)
            | ExpressionKind::Bot
    )
}

/// An argument that can stand in for a parameter without changing meaning or
/// hurting readability.
fn is_atom(e: &Expression) -> bool {
    matches!(e.kind(), ExpressionKind::Identifier(_)) || is_literal(e)
}

fn contains_unwrap(e: &Expression) -> bool {
    e.mapfold(false, |found, sub| {
        (
            found || matches!(sub.kind(), ExpressionKind::Unwrap(_)),
            sub,
        )
    })
    .0
}

/// Evaluates the Boolean structure of `e` as far as literals allow.
fn fold(e: &Expression) -> Expression {
    use ExpressionKind as K;
    e.map(|sub| {
        let folded = match sub.kind() {
            K::Not(x) => as_bool(x).map(|b| Expression::boolean(!b)),
            K::And(xs) | K::Or(xs) => {
                // `absorbing` decides the result; `neutral` operands drop out.
                let absorbing = !matches!(sub.kind(), K::And(_));
                if xs.iter().any(|x| as_bool(x) == Some(absorbing)) {
                    Some(Expression::boolean(absorbing))
                } else {
                    let rest: Vec<_> = xs
                        .iter()
                        .filter(|x| as_bool(x).is_none())
                        .cloned()
                        .collect();
                    match rest.len() {
                        0 => Some(Expression::boolean(!absorbing)),
                        1 => rest.into_iter().next(),
                        n if n == xs.len() => None,
                        _ if absorbing => Some(Expression::from_kind(K::Or(rest))),
                        _ => Some(Expression::from_kind(K::And(rest))),
                    }
                }
            }
            K::Equals(xs) if xs.len() == 2 && xs.iter().all(is_literal) => {
                Some(Expression::boolean(xs[0] == xs[1]))
            }
            K::LessThen(l, r)
            | K::GreaterThen(l, r)
            | K::LessThenEq(l, r)
            | K::GreaterThenEq(l, r) => match (l.kind(), r.kind()) {
                (K::IntegerLiteral(l), K::IntegerLiteral(r)) => {
                    Some(Expression::boolean(match sub.kind() {
                        K::LessThen(..) => l < r,
                        K::GreaterThen(..) => l > r,
                        K::LessThenEq(..) => l <= r,
                        _ => l >= r,
                    }))
                }
                _ => None,
            },
            _ => None,
        };
        folded.unwrap_or(sub)
    })
}

/// `s` wrapped in parentheses unless one pair already encloses all of it.
fn parenthesized(s: &str) -> String {
    let mut depth = 0usize;
    let enclosed = s.starts_with('(')
        && s.char_indices().all(|(i, c)| {
            match c {
                '(' => depth += 1,
                ')' => depth -= 1,
                _ => {}
            }
            depth > 0 || i == s.len() - 1
        });
    if enclosed {
        s.to_string()
    } else {
        format!("({s})")
    }
}

struct View<'a> {
    comp: &'a Composition,
    consts: &'a [(String, Expression)],
    lossy: bool,
    /// Every `goto` label handed out so far.
    labels: HashSet<String>,
    text: String,
}

impl View<'_> {
    fn emit(&mut self, indent: usize, line: &str) {
        for _ in 0..indent {
            self.text.push_str("    ");
        }
        let _ = writeln!(self.text, "{line}");
    }

    /// A fresh label for the end of `frame`: `end_Instance_Oracle`, or
    /// `end_Instance_Oracle_2`, … when the oracle is inlined more than once.
    fn end_label(&mut self, frame: &Frame) -> String {
        let base: String = format!("end_{}", frame.name)
            .chars()
            .map(|c| if c.is_alphanumeric() { c } else { '_' })
            .collect();
        let label = if self.labels.contains(&base) {
            fresh_name(&base, &self.labels)
        } else {
            base
        };
        self.labels.insert(label.clone());
        label
    }

    /// `e` in `frame`'s names, with constants resolved, the proof path's
    /// assignments substituted, and Boolean structure folded.
    fn expr(&self, e: &Expression, frame: &Frame) -> Expression {
        let e = e.map(|sub| match sub.kind() {
            ExpressionKind::Identifier(id) => frame.local(id).unwrap_or_else(|| self.constant(sub)),
            ExpressionKind::TableAccess(id, index) => {
                Expression::from_kind(ExpressionKind::TableAccess(frame.ident(id), index.clone()))
            }
            _ => sub,
        });
        fold(&e)
    }

    /// A constant identifier, replaced by its literal value when the game or
    /// the proof path gives it one.
    fn constant(&self, e: Expression) -> Expression {
        let resolved = resolve_const(&e);
        match resolved.kind() {
            ExpressionKind::Identifier(Identifier::TheoremIdentifier(
                TheoremIdentifier::Const(c),
            )) => self
                .consts
                .iter()
                .find(|(name, _)| *name == c.name)
                .map_or(e, |(_, value)| value.clone()),
            _ if is_literal(resolved) => resolved.clone(),
            _ => e,
        }
    }

    fn text_of(&self, e: &Expression) -> String {
        render_expr_with(e, self.lossy)
    }

    fn pattern(&self, p: &Pattern, frame: &Frame) -> String {
        let p = match p {
            Pattern::Ident(id) => Pattern::Ident(frame.ident(id)),
            Pattern::Table { ident, index } => Pattern::Table {
                ident: frame.ident(ident),
                index: self.expr(index, frame),
            },
            Pattern::Tuple(ids) => Pattern::Tuple(ids.iter().map(|id| frame.ident(id)).collect()),
        };
        render_pattern(&p, self.lossy)
    }

    /// `tail`: `block` ends the frame, so a `return` in it is the last thing
    /// the frame runs. Code after a statement that always exits is dead and
    /// is not printed; that statement ends the block instead.
    fn block(
        &mut self,
        block: &[Statement],
        frame: &Frame,
        indent: usize,
        tail: bool,
    ) -> Result<(), InlineError> {
        for (i, stmt) in block.iter().enumerate() {
            let exits = self.exits(std::slice::from_ref(stmt), frame);
            self.stmt(stmt, frame, indent, tail && (exits || i + 1 == block.len()))?;
            if exits {
                break;
            }
        }
        Ok(())
    }

    /// Every path through `block` returns or aborts, counting only the
    /// branches that run once the proof path's constants are substituted.
    fn exits(&self, block: &[Statement], frame: &Frame) -> bool {
        block.iter().any(|stmt| match stmt {
            Statement::Return(..) | Statement::Abort(_) => true,
            Statement::IfThenElse(ite) => match as_bool(&self.expr(&ite.cond, frame)) {
                Some(true) => self.exits(&ite.then_block.0, frame),
                Some(false) => self.exits(&ite.else_block.0, frame),
                None => {
                    self.exits(&ite.then_block.0, frame) && self.exits(&ite.else_block.0, frame)
                }
            },
            _ => false,
        })
    }

    fn stmt(
        &mut self,
        stmt: &Statement,
        frame: &Frame,
        indent: usize,
        tail: bool,
    ) -> Result<(), InlineError> {
        match stmt {
            Statement::Abort(_) => self.emit(indent, "abort;"),

            Statement::Return(value, _) => {
                let value = value.as_ref().map(|e| self.expr(e, frame));
                let line = match (&frame.ret, &value) {
                    (Ret::Top, Some(e)) => Some(format!("return {};", self.text_of(e))),
                    (Ret::Top, None) => Some("return;".to_string()),
                    (Ret::Bind(Some(bind)), Some(e)) => {
                        let e = self.text_of(e);
                        (*bind != e).then(|| format!("{bind} <- {e};"))
                    }
                    // A discarded result still aborts if an unwrap in it fails.
                    (Ret::Bind(None), Some(e)) if contains_unwrap(e) => {
                        Some(format!("_ <- {};", self.text_of(e)))
                    }
                    (Ret::Bind(_), _) => None,
                };
                if let Some(line) = line {
                    self.emit(indent, &line);
                }
                // An early return of an inlined callee jumps past the rest of it.
                if matches!(frame.ret, Ret::Bind(_)) && !tail {
                    let label = frame.end.get_or_init(|| self.end_label(frame));
                    let line = format!("goto {label};  // returns from {}", frame.name);
                    self.emit(indent, &line);
                }
            }

            Statement::Assignment(Assignment { pattern, rhs }, _) => match rhs {
                AssignmentRhs::Invoke {
                    oracle_name,
                    args,
                    edge,
                    ..
                } => self.call(
                    Some(pattern),
                    oracle_name,
                    args,
                    edge.as_ref(),
                    frame,
                    indent,
                )?,
                AssignmentRhs::Sample {
                    ty, sample_name, ..
                } => {
                    let name = match sample_name {
                        Some(n) if !self.lossy => format!(" sample-name {n}"),
                        _ => String::new(),
                    };
                    let line = format!(
                        "{} <-$ {}{name};",
                        self.pattern(pattern, frame),
                        render_type(ty)
                    );
                    self.emit(indent, &line);
                }
                AssignmentRhs::Expression(e) => {
                    let (lhs, rhs) = (
                        self.pattern(pattern, frame),
                        self.text_of(&self.expr(e, frame)),
                    );
                    if lhs != rhs {
                        self.emit(indent, &format!("{lhs} <- {rhs};"));
                    }
                }
            },

            Statement::InvokeOracle(InvokeOracle {
                oracle_name,
                args,
                edge,
                ..
            }) => self.call(None, oracle_name, args, edge.as_ref(), frame, indent)?,

            Statement::IfThenElse(ite) => {
                let cond = self.expr(&ite.cond, frame);
                let is_assert = ite.then_block.0.is_empty()
                    && matches!(ite.else_block.0.as_slice(), [Statement::Abort(_)]);
                match (as_bool(&cond), is_assert) {
                    (Some(true), true) => {}
                    (Some(false), true) => self.emit(indent, "abort;"),
                    (None, true) => self.emit(
                        indent,
                        &format!("assert {};", parenthesized(&self.text_of(&cond))),
                    ),
                    (Some(taken), false) => {
                        let block = if taken {
                            &ite.then_block
                        } else {
                            &ite.else_block
                        };
                        self.block(&block.0, frame, indent, tail)?;
                    }
                    (None, false) => {
                        self.emit(
                            indent,
                            &format!("if {} {{", parenthesized(&self.text_of(&cond))),
                        );
                        self.block(&ite.then_block.0, frame, indent + 1, tail)?;
                        if !ite.else_block.0.is_empty() {
                            self.emit(indent, "} else {");
                            self.block(&ite.else_block.0, frame, indent + 1, tail)?;
                        }
                        self.emit(indent, "}");
                    }
                }
            }

            Statement::For(var, lower, upper, body, _) => {
                let var = self.text_of(&Expression::from(frame.ident(var)));
                let header = format!(
                    "for {var}: {} <= {var} <= {} {{",
                    self.text_of(&self.expr(lower, frame)),
                    self.text_of(&self.expr(upper, frame)),
                );
                self.emit(indent, &header);
                self.block(&body.0, frame, indent + 1, false)?;
                self.emit(indent, "}");
            }
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn call(
        &mut self,
        bind: Option<&Pattern>,
        oracle_name: &str,
        args: &[Expression],
        edge: Option<&Edge>,
        caller: &Frame,
        indent: usize,
    ) -> Result<(), InlineError> {
        let edge = edge.ok_or_else(|| InlineError::UnresolvedEdge {
            oracle: oracle_name.to_string(),
            pkg_inst: caller.inst.clone(),
        })?;
        let sig = edge.sig();
        let inst = &self.comp.pkgs[edge.to()];
        let odef = find_oracle(inst, &sig.name)?;
        if caller.depth + 1 > MAX_INLINE_DEPTH {
            return Err(InlineError::MaxDepthExceeded {
                oracle: sig.name.clone(),
                max: MAX_INLINE_DEPTH,
            });
        }

        let body = &odef.code.0;
        let assigned = assigned_locals(body);
        let mut aliases = HashMap::new();
        let mut bindings = Vec::new();
        for ((param, _), arg) in sig.args.iter().zip(args) {
            let arg = self.expr(arg, caller);
            if !assigned.contains(param) && is_atom(&arg) {
                aliases.insert(param.clone(), arg);
            } else {
                bindings.push((param, arg));
            }
        }
        let fixed = bind.map_or_else(HashMap::new, |bind| {
            return_names(body, odef, bind, caller, &aliases)
        });
        let bind = bind.map(|p| self.pattern(p, caller));
        let callee = Frame::new(
            inst,
            odef,
            body,
            &caller.scope,
            aliases,
            fixed,
            Ret::Bind(bind),
            caller.depth + 1,
        );

        self.emit(indent, &format!("// inlined {}", callee.name));
        for (param, arg) in bindings {
            let (param, arg) = (&callee.names[param.as_str()], self.text_of(&arg));
            if *param != arg {
                self.emit(indent + 1, &format!("{param} <- {arg};"));
            }
        }
        self.block(body, &callee, indent + 1, true)?;
        if let Some(label) = callee.end.get() {
            self.emit(indent, &format!("{label}:"));
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::project::Project as _;
    use crate::transforms::{theorem_transforms::ViewTransform, TheoremTransform};

    /// Renders `oracle` of game instance `game` in the project at `dir`, run
    /// through [`ViewTransform`].
    fn view(
        dir: &str,
        theorem_name: &str,
        game: &str,
        oracle: &str,
        consts: &[(&str, Expression)],
    ) -> String {
        let files = crate::project::DirectoryFiles::load(std::path::Path::new(dir)).unwrap();
        let project =
            crate::project::DirectoryProject::load(std::path::PathBuf::from(dir), &files).unwrap();
        let theorem = project.get_theorem(theorem_name).unwrap();
        let (theorem, _aux) = ViewTransform.transform_theorem(theorem).unwrap();
        let consts: Vec<_> = consts
            .iter()
            .map(|(name, value)| (name.to_string(), value.clone()))
            .collect();
        render_oracle_view(
            theorem.find_game_instance(game).unwrap(),
            oracle,
            false,
            &consts,
        )
        .unwrap()
    }

    const KEM_DEM: &str = "example-projects/kem-dem/kem-dem-cca-ssp";

    /// No `invoke`; a callee's returned locals take the caller's names
    /// (`(pk_, sk_) <- kem_gen(r)` instead of a temporary and a copy).
    #[test]
    fn snapshot_kem_dem_pkgen() {
        let text = view(
            KEM_DEM,
            "kem_dem_cca_ssp",
            "Game_MOD_CCA_PKE_Real_KEM",
            "PKGEN",
            &[],
        );
        let expected = "\
PKGEN() -> Bits(pkeyl) {
    assert (MOD_CCA_PKE.pk == None);
    // inlined KEM.KEMGEN
        assert (KEM.sk == None);
        // inlined Scheme_KEM.KEM_GEN
            r <-$ Bits(kgenr) sample-name kem_gen;
            (pk_, sk_) <- kem_gen(r);
        KEM.pk <- Some(pk_);
        KEM.sk <- Some(sk_);
    MOD_CCA_PKE.pk <- Some(pk_);
    return pk_;
}
";
        assert_eq!(text, expected);
    }

    /// `dem_idealization: b` stays a branch on the theorem constant `b` until
    /// the proof path fixes it; `key_idealization: false` is always resolved.
    #[test]
    fn kem_dem_pkenc_applies_proof_parameters() {
        let generic = view(
            KEM_DEM,
            "kem_dem_cca_ssp",
            "Game_MOD_CCA_PKE_Real_KEM",
            "PKENC",
            &[],
        );
        assert!(generic.contains("if (b) {"), "{generic}");
        assert!(generic.contains("dem_enc(k, m0)") && generic.contains("dem_enc(k, m1)"));

        let real = view(
            KEM_DEM,
            "kem_dem_cca_ssp",
            "Game_MOD_CCA_PKE_Real_KEM",
            "PKENC",
            &[("b", Expression::boolean(false))],
        );
        let expected = "\
PKENC(m0: Bits(ptl), m1: Bits(ptl)) -> (Bits(kctl), Bits(dctl)) {
    assert (not ((MOD_CCA_PKE.pk == None)));
    assert (MOD_CCA_PKE.c == None);
    // inlined KEM.ENCAPS
        assert (not ((KEM.pk == None)));
        assert (KEM.c == None);
        // inlined Scheme_KEM.KEM_ENCAPS
            pk <- Unwrap(KEM.pk);
            r <-$ Bits(kencr) sample-name kem_encaps;
            (k, c_kem) <- kem_encaps(r, pk);
        KEM.c <- Some(c_kem);
        // inlined Key.SET
            assert (Key.k == None);
            Key.k <- Some(k);
    // inlined DEM.ENC
        assert (DEM.c == None);
        // inlined Key.GET
            assert (not ((Key.k == None)));
            k <- Unwrap(Key.k);
        // inlined Scheme_DEM.DEM_ENC
            c_dem <- dem_enc(k, m0);
        DEM.c <- Some(c_dem);
    c_ <- (c_kem, c_dem);
    MOD_CCA_PKE.c <- Some(c_);
    return c_;
}
";
        assert_eq!(real, expected);
    }

    /// Callee locals that an enclosing frame already uses are renamed: `r` in
    /// `Enc.LENCN` (the caller has `(l, r, op)`), the loop variable `j` of
    /// `MODGB.GBL` (inside `GARBLE`'s `for j`), and the rebound parameter `i`
    /// of `Keys.LGETKEYSOUT`. Loops with symbolic bounds are printed as-is.
    #[test]
    fn yao_garble_respects_scoping() {
        let text = view("example-projects/yao", "Yao", "YaoReal", "GARBLE", &[]);
        for line in [
            "for j: 1 <= j <= w {",
            "for j_2: 1 <= j_2 <= w {",
            "(l, r, op) <- Unwrap(Ci[j_2]);",
            "i_2 <- (i + 1);",
            "r_2 <-$ Bits(n) sample-name r;",
            "Keys.flag[(i, r)]",
        ] {
            assert!(text.contains(line), "missing `{line}` in:\n{text}");
        }
        assert!(!text.contains("invoke"), "{text}");
    }

    const KEM_DEM_BLENDED: &str = "example-projects/kem-dem/kem-dem-cca-blended-parallel";

    /// `Scheme_KEMDEM.DEC` returns early when decapsulation fails: the return
    /// jumps to a label after the inlined body instead of falling through.
    #[test]
    fn early_return_jumps_past_the_callee() {
        let text = view(
            KEM_DEM_BLENDED,
            "kem_dem_cca_blended_parallel",
            "CCA_PKE_0",
            "PKDEC",
            &[],
        );
        let expected = "\
PKDEC(c_: (Bits(kctl), Bits(dctl))) -> Maybe(Bits(ptl)) {
    assert (not ((CCA_PKE.sk == None)));
    assert (not ((c_ == Unwrap(CCA_PKE.c))));
    // inlined Scheme_KEMDEM.DEC
        sk <- Unwrap(CCA_PKE.sk);
        (c_kem, c_dem) <- c_;
        // inlined Scheme_KEM.KEM_DECAPS
            (Scheme_KEM.st, k) <- kem_decaps(Scheme_KEM.st, sk, c_kem);
        if (k == None) {
            m <- None;
            goto end_Scheme_KEMDEM_DEC;  // returns from Scheme_KEMDEM.DEC
        }
        // inlined Scheme_DEM.DEM_DEC
            k_2 <- Unwrap(k);
            m_2 <- dem_dec(k_2, c_dem);
        m <- Some(m_2);
    end_Scheme_KEMDEM_DEC:
    return m;
}
";
        assert_eq!(text, expected);
    }

    /// `Prf.Eval` returns early when `(H[kid] == Some(false)) or not b`. With
    /// `b: false` the return always runs: the code after it is dead and is
    /// dropped, and no `goto` is needed. With `b: true` the return is early.
    #[test]
    fn return_under_a_resolved_branch_ends_the_callee() {
        let dir = "example-projects/4WHS";
        let resolved = view(dir, "Simple4WHS", "Hybrid2", "Send2", &[]);
        assert!(resolved.contains("kmac <- prf(k, x);"), "{resolved}");
        assert!(!resolved.contains("goto"), "{resolved}");
        assert!(!resolved.contains("Prf.PRF"), "{resolved}");

        let early = view(dir, "Simple4WHS", "Hybrid3", "Send2", &[]);
        assert!(
            early.contains("goto end_Prf_Eval;  // returns from Prf.Eval"),
            "{early}"
        );
        assert!(early.contains("\n        end_Prf_Eval:\n"), "{early}");
    }
}
