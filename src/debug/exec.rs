// SPDX-License-Identifier: MIT OR Apache-2.0

//! Solver-free symbolic execution of one inlined oracle.
//!
//! [`execute`] walks an [`InlinedOracle`] (produced by [`crate::debug::ir`]) to
//! every syntactic terminal — a `return` at the entry frame or an `abort` at any
//! depth — and hands back one [`TerminalPath`] per terminal. Each path carries a
//! **flat** SMT encoding: a `declare-const` for every dynamic-single-assignment
//! (DSA) variable it introduces, the definitional `(assert (= <ssa> <rhs>))` and
//! path-condition assertions in order, and a single `return_constraint` that
//! fills the `<return-{GI}-{O}>` slot story 04 left unconstrained
//! (`emit_constant_declarations(Some(O))`).
//!
//! No solver is involved: every branch is explored, `abort` and `unwrap`-none
//! terminate the path, and a callee `return` resumes the caller after the
//! [`crate::debug::ir::InlStmt::Call`]. Story 06 layers solver-guided pruning on
//! top of [`execute_streaming`] without changing anything here.
//!
//! # Mirroring the prover
//!
//! The SMT each path produces must be *semantically identical* to what
//! `src/writers/smt/writer.rs` emits for the same execution, or the debugger
//! disagrees with `domino prove`. The correspondence:
//!
//! | executor | writer |
//! |---|---|
//! | [`SymState::locals`] rebind on `Assign` | `smt_build_assign` `let` |
//! | [`SymState::pkg_state`] keyed `(inst, field)` | package-state `let` bindings, global |
//! | `Sample` → `(__sample-rand-<gi>-<ty> <pos> <ctr>)`, `ctr += 1` | `smt_build_sample` |
//! | `Unwrap` none-child → `Abort` at the unwrap label | `smt_build_assign` unwrap `ite` |
//! | terminal: fold pkg states + advanced counters into the old state | `smt_write_back_state` + `smt_increment_gamestate_rand` |
//!
//! The single biggest correctness risk is the terminal game-state reconstruction
//! ([`Executor::emit_terminal`]); see the story-05 implementation report.

use std::collections::{BTreeSet, HashMap};
use std::ops::ControlFlow;

use crate::debug::ir::{InlBlock, InlStmt, InlinedOracle, Label, Place, VarKey};
use crate::expressions::{Expression, ExpressionKind};
use crate::identifier::pkg_ident::PackageIdentifier;
use crate::identifier::Identifier;
use crate::theorem::GameInstance;
use crate::transforms::samplify::SampleInfo;
use crate::types::{Type, TypeKind};
use crate::writers::smt::contexts::{
    GameInstanceContext, GenericOracleContext, OracleContext, PackageInstanceContext,
};
use crate::writers::smt::declare::declare_const;
use crate::writers::smt::exprs::{SmtAs, SmtAssert, SmtEq2, SmtExpr, SmtNot};
use crate::writers::smt::names;
use crate::writers::smt::patterns::oracle_args::{
    GameStateOracleArgPattern, OracleArgPattern, UnitOracleArgPattern,
};
use crate::writers::smt::patterns::pkg_consts::PackageConstsSelector;
use crate::writers::smt::patterns::{DatastructurePattern, FunctionPattern, PackageStateSelector};
use crate::writers::smt::sorts::Sort;

/// Which game instance is being executed. Only namespaces SSA names and picks
/// which `SampleInfo` / contexts to use.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Side {
    Left,
    Right,
}

impl Side {
    fn as_str(self) -> &'static str {
        match self {
            Side::Left => "left",
            Side::Right => "right",
        }
    }
}

/// One decision taken at a branching point, in execution order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Step {
    pub label: Label,
    pub decision: Decision,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Decision {
    /// `Branch { is_assert: false }` taken / not taken.
    Then,
    Else,
    /// `Branch { is_assert: true }` — the guard held / failed (the latter aborts).
    AssertHolds,
    AssertFails,
    /// `Unwrap` — the value was `Some` / `None` (the latter aborts).
    UnwrapSome,
    UnwrapNone,
}

impl Decision {
    /// The label story 06/07 render: `then` / `else` / `assert-holds` /
    /// `assert-fails` / `unwrap-some` / `unwrap-none`.
    pub fn as_str(self) -> &'static str {
        match self {
            Decision::Then => "then",
            Decision::Else => "else",
            Decision::AssertHolds => "assert-holds",
            Decision::AssertFails => "assert-fails",
            Decision::UnwrapSome => "unwrap-some",
            Decision::UnwrapNone => "unwrap-none",
        }
    }
}

#[allow(clippy::large_enum_variant)] // matches `ir::Place`; `Terminal` is a public leaf type
#[derive(Clone, Debug)]
pub enum Terminal {
    Return {
        label: Label,
        value: Option<Expression>,
    },
    Abort {
        label: Label,
    },
}

impl Terminal {
    pub fn label(&self) -> Label {
        match self {
            Terminal::Return { label, .. } | Terminal::Abort { label } => *label,
        }
    }

    pub fn is_abort(&self) -> bool {
        matches!(self, Terminal::Abort { .. })
    }
}

/// A complete path from oracle entry to one terminal, with its flat SMT.
#[derive(Clone, Debug)]
pub struct TerminalPath {
    /// Assigned by the driver (story 06), e.g. `"L3"` or `"L3.R2"`. Empty here.
    pub id: String,
    pub steps: Vec<Step>,
    /// `declare-const` for every SSA variable introduced on this path, in order.
    pub decls: Vec<SmtExpr>,
    /// Definitional `(assert (= <ssa> <rhs>))` and path conditions, in order.
    pub constraints: Vec<SmtExpr>,
    /// `(assert (= <return-{GI}-{O}> <constructed return/abort>))`.
    pub return_constraint: SmtExpr,
    pub terminal: Terminal,
}

#[derive(Debug, thiserror::Error, miette::Diagnostic)]
pub enum ExecError {
    #[error("oracle `{oracle}` is not exported by game instance `{game_inst}`")]
    OracleNotExported { oracle: String, game_inst: String },

    #[error("path limit of {limit} exceeded (explored {explored} complete paths)")]
    MaxPathsExceeded { explored: usize, limit: usize },
}

/// The symbolic store for one in-progress path. Cloned at every fork.
#[derive(Clone, Default)]
struct SymState {
    /// Frame-local → its current SSA constant (an [`Identifier::Generated`],
    /// rendered `<name>` in SMT).
    locals: HashMap<VarKey, Identifier>,
    /// `(pkg_inst, field)` → its current SSA constant. Not frame-scoped, exactly
    /// like the prover's global package-state encoding.
    pkg_state: HashMap<(String, String), Identifier>,
    /// `(pkg_inst, const_name)` → the SSA constant it was seeded to. Package
    /// consts are read once out of the global game-consts constant, mirroring the
    /// `let` binding the prover wraps every oracle body in
    /// (`bind_pkg_consts` in `smt_define_nonsplit_oracle_fn`).
    pkg_consts: HashMap<(String, String), Identifier>,
    /// `sample_id` → how many times it has been drawn so far. Starts at 0 and
    /// only increments; materialised into the game state at the terminal.
    rand_ctr: HashMap<usize, usize>,
    steps: Vec<Step>,
    decls: Vec<SmtExpr>,
    constraints: Vec<SmtExpr>,
}

impl SymState {
    /// The current store value of an identifier, or `None` for anything that is
    /// not a tracked local / package-state field (constants, theorem params,
    /// literals — left untouched so they convert exactly as the prover's
    /// `From<&Expression> for SmtExpr` would).
    fn lookup(&self, id: &Identifier) -> Option<Identifier> {
        match id {
            Identifier::Generated(key, _) => self.locals.get(key).cloned(),
            Identifier::PackageIdentifier(PackageIdentifier::State(s)) => {
                let inst = s
                    .pkg_inst_name
                    .clone()
                    .unwrap_or_else(|| s.pkg_name.clone());
                self.pkg_state.get(&(inst, s.name.clone())).cloned()
            }
            Identifier::PackageIdentifier(PackageIdentifier::Const(c)) => {
                let inst = c
                    .pkg_inst_name
                    .clone()
                    .unwrap_or_else(|| c.pkg_name.clone());
                self.pkg_consts.get(&(inst, c.name.clone())).cloned()
            }
            _ => None,
        }
    }

    /// The current SSA constant bound to a place, if any.
    fn place_ident(&self, place: &Place) -> Option<Identifier> {
        match place {
            Place::Local { key, .. } => self.locals.get(key).cloned(),
            Place::State {
                pkg_inst, field, ..
            } => self
                .pkg_state
                .get(&(pkg_inst.clone(), field.clone()))
                .cloned(),
            Place::Index { base, .. } => self.place_ident(base),
            Place::Tuple(_) | Place::Discard => None,
        }
    }

    /// Rebind a place (or, for a table write, its base) to a fresh SSA constant.
    fn rebind(&mut self, place: &Place, id: Identifier) {
        match place {
            Place::Local { key, .. } => {
                self.locals.insert(key.clone(), id);
            }
            Place::State {
                pkg_inst, field, ..
            } => {
                self.pkg_state.insert((pkg_inst.clone(), field.clone()), id);
            }
            Place::Index { base, .. } => self.rebind(base, id),
            Place::Tuple(_) | Place::Discard => {}
        }
    }
}

/// Substitute every tracked identifier in `e` with its current store value.
/// Uses [`Expression::map`] like `unwrapify` / the inliner, so unhandled
/// operators panic there the same way they do for the prover (pre-existing
/// `borrow_map` gap — see story 02 report §5).
fn subst(st: &SymState, e: &Expression) -> Expression {
    e.map(|sub| match sub.kind() {
        ExpressionKind::Identifier(id) => match st.lookup(id) {
            Some(rep) => Expression::from(rep),
            None => sub,
        },
        ExpressionKind::TableAccess(id, idx) => match st.lookup(id) {
            Some(rep) => Expression::from_kind(ExpressionKind::TableAccess(rep, idx.clone())),
            None => sub,
        },
        _ => sub,
    })
}

/// Substitute and lower to SMT in one step.
fn to_smt(st: &SymState, e: &Expression) -> SmtExpr {
    SmtExpr::from(&subst(st, e))
}

fn base_of_key(key: &str) -> &str {
    key.rsplit("::").next().unwrap_or(key)
}

fn place_basename(place: &Place) -> &str {
    match place {
        Place::Local { key, .. } => base_of_key(key),
        Place::State { field, .. } => field,
        Place::Index { base, .. } => place_basename(base),
        Place::Tuple(_) => "tuple",
        Place::Discard => "_",
    }
}

fn place_ty(place: &Place) -> Type {
    match place {
        Place::Local { ty, .. } | Place::State { ty, .. } => ty.clone(),
        Place::Index { base, .. } => place_ty(base),
        Place::Tuple(_) | Place::Discard => Type::empty(),
    }
}

/// Every package instance that appears as a `Call` callee anywhere in `block`
/// (recursively). Combined with the entry instance, this is exactly the set the
/// prover writes package state back for (`smt_build_invoke` writes the caller
/// back unconditionally, and every caller is either the entry instance or another
/// callee).
fn collect_call_pkg_insts(block: &InlBlock, out: &mut BTreeSet<String>) {
    for stmt in &block.0 {
        match stmt {
            InlStmt::Branch { then, els, .. } => {
                collect_call_pkg_insts(then, out);
                collect_call_pkg_insts(els, out);
            }
            InlStmt::Call { frame, body, .. } => {
                out.insert(frame.pkg_inst_name.clone());
                collect_call_pkg_insts(body, out);
            }
            _ => {}
        }
    }
}

/// Every `(pkg_inst, const_name)` a `PackageIdentifier::Const` in any expression
/// of `block` refers to (recursively). Only these need seeding into the store —
/// seeding all of a package's consts would bloat every path with unused decls.
fn collect_referenced_pkg_consts(block: &InlBlock, out: &mut BTreeSet<(String, String)>) {
    fn visit_expr(e: &Expression, out: &mut BTreeSet<(String, String)>) {
        let found = std::cell::RefCell::new(Vec::new());
        e.map(|sub| {
            if let ExpressionKind::Identifier(Identifier::PackageIdentifier(
                PackageIdentifier::Const(c),
            )) = sub.kind()
            {
                let inst = c
                    .pkg_inst_name
                    .clone()
                    .unwrap_or_else(|| c.pkg_name.clone());
                found.borrow_mut().push((inst, c.name.clone()));
            }
            sub
        });
        out.extend(found.into_inner());
    }
    for stmt in &block.0 {
        match stmt {
            InlStmt::Assign { rhs, .. } => visit_expr(rhs, out),
            InlStmt::Unwrap { inner, .. } => visit_expr(inner, out),
            InlStmt::Return { value: Some(e), .. } => visit_expr(e, out),
            InlStmt::Branch {
                cond, then, els, ..
            } => {
                visit_expr(cond, out);
                collect_referenced_pkg_consts(then, out);
                collect_referenced_pkg_consts(els, out);
            }
            InlStmt::Call { frame, body, .. } => {
                for (_, _, e) in &frame.arg_bindings {
                    visit_expr(e, out);
                }
                collect_referenced_pkg_consts(body, out);
            }
            InlStmt::Sample { .. } | InlStmt::Return { value: None, .. } | InlStmt::Abort { .. } => {}
        }
    }
}

/// A position in the walk: a block plus how far into it we are. `kind` records
/// whether a `Return` here resumes a caller.
#[derive(Clone)]
struct Cursor<'a> {
    block: &'a InlBlock,
    ip: usize,
    kind: FrameKind,
}

#[allow(clippy::large_enum_variant)] // `Place` is large; a Cursor stack is short
#[derive(Clone)]
enum FrameKind {
    /// The entry body or an `if`/`else` sub-block — a `Return` propagates.
    Sub,
    /// An inlined `Call` body — a `Return` binds `bind` and resumes the caller.
    Call { bind: Option<Place> },
}

struct Executor<'a> {
    inlined: &'a InlinedOracle,
    gctx: GameInstanceContext<'a>,
    octx: OracleContext<'a>,
    sample_info: &'a SampleInfo,
    side: Side,
    game_inst_name: &'a str,
    old_state_const: String,
    return_const_name: String,
    /// Package instances whose state is reconstructed and folded back at each
    /// terminal, in `game().pkgs` order.
    fold_pkgs: Vec<String>,
    /// `(pkg_inst, const_name)` pairs actually referenced by an oracle-body
    /// expression — the only package consts seeded into the store.
    referenced_consts: BTreeSet<(String, String)>,
    ssa: usize,
    path_count: usize,
    max_paths: Option<usize>,
}

impl<'a> Executor<'a> {
    fn new(
        inlined: &'a InlinedOracle,
        game_inst: &'a GameInstance,
        sample_info: &'a SampleInfo,
        side: Side,
        max_paths: Option<usize>,
    ) -> Result<Self, ExecError> {
        let gctx = GameInstanceContext::new(game_inst);

        let export = game_inst
            .game()
            .exports
            .iter()
            .find(|e| e.name() == inlined.oracle_name)
            .ok_or_else(|| ExecError::OracleNotExported {
                oracle: inlined.oracle_name.clone(),
                game_inst: game_inst.name().to_string(),
            })?;

        let mut octx = gctx
            .exported_oracle_ctx_by_name(&inlined.oracle_name)
            .expect("export resolved above");
        octx.set_renamed(export.alias());

        let old_state_const = octx
            .oracle_arg_game_state_pattern()
            .old_global_const_name(game_inst.name());
        let return_const_name =
            format!("<return-{}-{}>", game_inst.name(), inlined.oracle_name);

        let mut wanted = BTreeSet::new();
        wanted.insert(inlined.entry_pkg_inst.clone());
        collect_call_pkg_insts(&inlined.body, &mut wanted);
        let fold_pkgs = game_inst
            .game()
            .pkgs
            .iter()
            .map(|p| p.name.clone())
            .filter(|n| wanted.contains(n))
            .collect();

        let mut referenced_consts = BTreeSet::new();
        collect_referenced_pkg_consts(&inlined.body, &mut referenced_consts);

        Ok(Executor {
            inlined,
            referenced_consts,
            gctx,
            octx,
            sample_info,
            side,
            game_inst_name: game_inst.name(),
            old_state_const,
            return_const_name,
            fold_pkgs,
            ssa: 0,
            path_count: 0,
            max_paths,
        })
    }

    /// Declare a fresh SSA constant of type `ty` and return its identifier.
    fn fresh(&mut self, st: &mut SymState, basename: &str, ty: &Type) -> Identifier {
        let n = self.ssa;
        self.ssa += 1;
        let id = Identifier::Generated(
            format!("v!{}!{}!{}", self.side.as_str(), n, basename),
            ty.clone(),
        );
        st.decls
            .push(declare_const(id.smt_identifier_string(), ty.clone().into()));
        id
    }

    fn define(&mut self, st: &mut SymState, id: &Identifier, rhs: SmtExpr) {
        st.constraints.push(
            SmtAssert(SmtEq2 {
                lhs: id.smt_identifier_string(),
                rhs,
            })
            .into(),
        );
    }

    /// Bind `value` into `place` through a fresh SSA constant. Handles table
    /// writes (`store`) and the `_` discard; tuple patterns are handled by the
    /// caller.
    fn bind_fresh(&mut self, st: &mut SymState, place: &Place, value: SmtExpr) {
        match place {
            Place::Discard => {}
            Place::Local { .. } | Place::State { .. } => {
                let id = self.fresh(st, place_basename(place), &place_ty(place));
                self.define(st, &id, value);
                st.rebind(place, id);
            }
            Place::Index { base, index } => {
                let base_id = st
                    .place_ident(base)
                    .expect("table base must already be bound");
                let stored = SmtExpr::List(vec![
                    "store".into(),
                    (&base_id).into(),
                    to_smt(st, index),
                    value,
                ]);
                let id = self.fresh(st, place_basename(base), &place_ty(base));
                self.define(st, &id, stored);
                st.rebind(base, id);
            }
            Place::Tuple(_) => unreachable!("tuple places are destructured by the caller"),
        }
    }

    fn do_assign(&mut self, st: &mut SymState, target: &Place, rhs: &Expression) {
        match target {
            Place::Tuple(places) => {
                let rhs_smt = to_smt(st, rhs);
                let n = places.len();
                for (i, p) in places.iter().enumerate() {
                    if matches!(p, Place::Discard) {
                        continue;
                    }
                    let elem = SmtExpr::List(vec![
                        SmtExpr::Atom(format!("el{}-{}", n, i + 1)),
                        rhs_smt.clone(),
                    ]);
                    self.bind_fresh(st, p, elem);
                }
            }
            other => {
                let value = to_smt(st, rhs);
                self.bind_fresh(st, other, value);
            }
        }
    }

    fn do_sample(&mut self, st: &mut SymState, target: &Place, sample_id: usize, ty: &Type) {
        let pos = &self.sample_info.positions[sample_id];
        let ctr = *st.rand_ctr.get(&sample_id).unwrap_or(&0);
        let rand_fn = names::fn_sample_rand_name(self.game_inst_name, ty.clone());
        let rand_val = SmtExpr::from((rand_fn, pos, ctr));
        *st.rand_ctr.entry(sample_id).or_insert(0) += 1;
        self.bind_fresh(st, target, rand_val);
    }

    /// Walk one continuation stack to a terminal, forking at every branch.
    /// `on_path` sees each completed [`TerminalPath`]; returning
    /// [`ControlFlow::Break`] stops the whole walk.
    fn walk(
        &mut self,
        mut frames: Vec<Cursor<'a>>,
        mut st: SymState,
        on_path: &mut dyn FnMut(&TerminalPath) -> ControlFlow<()>,
    ) -> Result<ControlFlow<()>, ExecError> {
        loop {
            let (block, ip): (&'a InlBlock, usize) = {
                let Some(cur) = frames.last_mut() else {
                    unreachable!(
                        "execution fell off the end of the oracle without a terminal — \
                         `returnify` should guarantee every path ends in return/abort"
                    );
                };
                if cur.ip >= cur.block.0.len() {
                    frames.pop();
                    continue;
                }
                let ip = cur.ip;
                cur.ip += 1;
                (cur.block, ip)
            };

            match &block.0[ip] {
                InlStmt::Assign { target, rhs, .. } => self.do_assign(&mut st, target, rhs),

                InlStmt::Sample {
                    target,
                    sample_id,
                    ty,
                    ..
                } => self.do_sample(&mut st, target, *sample_id, ty),

                InlStmt::Unwrap {
                    label,
                    target,
                    inner,
                } => {
                    let inner_smt = to_smt(&st, inner);
                    let maybe_sort: Sort = inner.get_type().into();
                    let is_none: SmtExpr = SmtEq2 {
                        lhs: inner_smt.clone(),
                        rhs: SmtAs {
                            term: "mk-none",
                            sort: maybe_sort,
                        },
                    }
                    .into();

                    // none-child: aborts at the unwrap's own label
                    let mut st_none = st.clone();
                    st_none.steps.push(Step {
                        label: *label,
                        decision: Decision::UnwrapNone,
                    });
                    st_none.constraints.push(SmtAssert(is_none.clone()).into());
                    if self
                        .emit_terminal(st_none, Terminal::Abort { label: *label }, on_path)?
                        .is_break()
                    {
                        return Ok(ControlFlow::Break(()));
                    }

                    // some-child: continue in place
                    st.steps.push(Step {
                        label: *label,
                        decision: Decision::UnwrapSome,
                    });
                    st.constraints.push(SmtAssert(SmtNot(is_none)).into());
                    let getter = SmtExpr::List(vec!["maybe-get".into(), inner_smt]);
                    self.bind_fresh(&mut st, target, getter);
                }

                InlStmt::Branch {
                    label,
                    cond,
                    then,
                    els,
                    is_assert,
                } => {
                    let cond_smt = to_smt(&st, cond);
                    let (d_then, d_else) = if *is_assert {
                        (Decision::AssertHolds, Decision::AssertFails)
                    } else {
                        (Decision::Then, Decision::Else)
                    };

                    // then-child: recurse to completion
                    let mut st_then = st.clone();
                    let mut frames_then = frames.clone();
                    st_then.steps.push(Step {
                        label: *label,
                        decision: d_then,
                    });
                    st_then
                        .constraints
                        .push(SmtAssert(cond_smt.clone()).into());
                    frames_then.push(Cursor {
                        block: then,
                        ip: 0,
                        kind: FrameKind::Sub,
                    });
                    if self.walk(frames_then, st_then, on_path)?.is_break() {
                        return Ok(ControlFlow::Break(()));
                    }

                    // else-child: continue in place
                    st.steps.push(Step {
                        label: *label,
                        decision: d_else,
                    });
                    st.constraints.push(SmtAssert(SmtNot(cond_smt)).into());
                    frames.push(Cursor {
                        block: els,
                        ip: 0,
                        kind: FrameKind::Sub,
                    });
                }

                InlStmt::Call {
                    frame, bind, body, ..
                } => {
                    for (key, ty, expr) in &frame.arg_bindings {
                        let value = to_smt(&st, expr);
                        let id = self.fresh(&mut st, base_of_key(key), ty);
                        self.define(&mut st, &id, value);
                        st.locals.insert(key.clone(), id);
                    }
                    frames.push(Cursor {
                        block: body,
                        ip: 0,
                        kind: FrameKind::Call {
                            bind: bind.clone(),
                        },
                    });
                }

                InlStmt::Return { label, value } => {
                    let in_call = frames
                        .iter()
                        .any(|f| matches!(f.kind, FrameKind::Call { .. }));
                    if !in_call {
                        return self.emit_terminal(
                            st,
                            Terminal::Return {
                                label: *label,
                                value: value.clone(),
                            },
                            on_path,
                        );
                    }
                    // resume the nearest enclosing call
                    let ret_val = value.as_ref().map(|e| to_smt(&st, e));
                    loop {
                        let popped = frames.pop().expect("a Call frame is on the stack");
                        if let FrameKind::Call { bind } = popped.kind {
                            if let Some(place) = bind {
                                let value = ret_val
                                    .clone()
                                    .unwrap_or_else(|| SmtExpr::Atom("mk-empty".to_string()));
                                self.bind_fresh(&mut st, &place, value);
                            }
                            break;
                        }
                    }
                }

                InlStmt::Abort { label } => {
                    return self.emit_terminal(st, Terminal::Abort { label: *label }, on_path);
                }
            }
        }
    }

    /// Build the `return_constraint` for a terminal and hand the finished path to
    /// `on_path`.
    fn emit_terminal(
        &mut self,
        mut st: SymState,
        terminal: Terminal,
        on_path: &mut dyn FnMut(&TerminalPath) -> ControlFlow<()>,
    ) -> Result<ControlFlow<()>, ExecError> {
        self.path_count += 1;
        if let Some(limit) = self.max_paths {
            if self.path_count > limit {
                return Err(ExecError::MaxPathsExceeded {
                    explored: self.path_count - 1,
                    limit,
                });
            }
        }

        // Reconstruct the game state, threading it through a fresh SSA constant
        // after every step so the term stays flat (`smt_increment_gamestate_rand`
        // / `smt_update_gamestate_pkgstate` each re-read the whole accumulator).
        let gs_sort = self.octx.oracle_arg_game_state_pattern().sort();
        let mut game_state = SmtExpr::Atom(self.old_state_const.clone());
        let rebind_gs = |exec: &mut Self, st: &mut SymState, term: SmtExpr| -> SmtExpr {
            let id = Identifier::Generated(
                format!("v!{}!{}!gamestate", exec.side.as_str(), exec.ssa),
                Type::empty(),
            );
            exec.ssa += 1;
            st.decls
                .push(declare_const(id.smt_identifier_string(), gs_sort.clone()));
            st.constraints.push(
                SmtAssert(SmtEq2 {
                    lhs: id.smt_identifier_string(),
                    rhs: term,
                })
                .into(),
            );
            SmtExpr::Atom(id.smt_identifier_string())
        };

        // 1. advance the randomness counters (sorted for determinism), exactly
        //    as the prover threads `smt_increment_gamestate_rand` during sampling.
        let mut ctrs: Vec<(usize, usize)> = st
            .rand_ctr
            .iter()
            .filter(|&(_, &n)| n > 0)
            .map(|(&k, &n)| (k, n))
            .collect();
        ctrs.sort_unstable();
        for (sample_id, n) in ctrs {
            for _ in 0..n {
                let next = self
                    .gctx
                    .smt_increment_gamestate_rand(game_state, self.sample_info, sample_id)
                    .expect("sample id is in range");
                game_state = rebind_gs(self, &mut st, next);
            }
        }

        // 2. fold each touched package instance's reconstructed state back in.
        for name in self.fold_pkgs.clone() {
            let pctx = self
                .gctx
                .pkg_inst_ctx_by_name(&name)
                .expect("fold_pkgs came from game().pkgs");
            let pkg_state_term = reconstruct_pkg_state(&pctx, &st);
            let next = self
                .gctx
                .smt_update_gamestate_pkgstate(
                    game_state,
                    self.sample_info,
                    &name,
                    pkg_state_term,
                )
                .expect("package instance exists");
            game_state = rebind_gs(self, &mut st, next);
        }

        // 4. build the return / abort term and the constraint that fills
        //    `<return-{GI}-{O}>`.
        let return_term = match &terminal {
            Terminal::Return {
                value: Some(e), ..
            } => self.octx.smt_construct_return(game_state, to_smt(&st, e)),
            Terminal::Return { value: None, .. } => {
                self.octx.smt_construct_return(game_state, "mk-empty")
            }
            Terminal::Abort { .. } => self.octx.smt_construct_abort(game_state),
        };
        let return_constraint = SmtAssert(SmtEq2 {
            lhs: SmtExpr::Atom(self.return_const_name.clone()),
            rhs: return_term,
        })
        .into();

        let path = TerminalPath {
            id: String::new(),
            steps: st.steps,
            decls: st.decls,
            constraints: st.constraints,
            return_constraint,
            terminal,
        };
        Ok(on_path(&path))
    }

    /// Seed argument constants and the package state of every folded instance.
    fn initial_state(&mut self) -> SymState {
        let mut st = SymState::default();

        // exported-oracle arguments live under the entry frame's keys.
        let args: Vec<(String, Type)> = self.inlined.args.clone();
        for (name, ty) in &args {
            let id = self.fresh(&mut st, name, ty);
            let arg_smt = self.octx.smt_arg_name(name);
            self.define(&mut st, &id, arg_smt);
            st.locals
                .insert(format!("{}#0::{}", self.inlined.entry_pkg_inst, name), id);
        }

        // The global game-consts constant (`<<game-consts-{GI}>>`), the same
        // term the prover passes as the oracle function's consts argument.
        let game_consts_const = self
            .octx
            .oracle_arg_game_consts_pattern()
            .unit_global_const_name(self.game_inst_name);

        // package state fields, read out of the old game state; and package
        // consts, read out of the global game-consts constant.
        let fold_pkgs = self.fold_pkgs.clone();
        for name in &fold_pkgs {
            let pctx = self
                .gctx
                .pkg_inst_ctx_by_name(name)
                .expect("fold_pkgs came from game().pkgs");
            let pkg_state = self
                .gctx
                .smt_access_gamestate_pkgstate(self.old_state_const.clone(), name)
                .expect("package instance exists");
            let fields: Vec<(String, Type)> = pctx
                .pkg()
                .state
                .iter()
                .map(|(f, ty, _)| (f.clone(), ty.clone()))
                .collect();
            for (field, ty) in &fields {
                let access = pctx
                    .smt_access_pkgstate(pkg_state.clone(), field)
                    .expect("field exists");
                let id = self.fresh(&mut st, field, ty);
                self.define(&mut st, &id, access);
                st.pkg_state.insert((name.clone(), field.clone()), id);
            }

            // package consts: `(<pkg-consts-{Pkg}-{c}> (<pkgconsts-{game}-{inst}>
            // <<game-consts-{GI}>>))`, matching `bind_pkg_consts`.
            let consts_pattern = pctx.datastructure_pkg_consts_pattern();
            let mapped = pctx
                .function_pkg_const_pattern()
                .call(&[SmtExpr::Atom(game_consts_const.clone())])
                .expect("package const mapping fn takes exactly one argument");
            let params: Vec<(String, Type)> = pctx
                .pkg()
                .params
                .iter()
                .filter(|(_, ty, _)| !matches!(ty.kind(), TypeKind::Fn(_, _)))
                .filter(|(n, _, _)| self.referenced_consts.contains(&(name.clone(), n.clone())))
                .map(|(n, ty, _)| (n.clone(), ty.clone()))
                .collect();
            for (cname, cty) in &params {
                let selector = PackageConstsSelector {
                    name: cname,
                    ty: cty,
                };
                let access = consts_pattern.access_unchecked(&selector, mapped.clone());
                let id = self.fresh(&mut st, cname, cty);
                self.define(&mut st, &id, access);
                st.pkg_consts.insert((name.clone(), cname.clone()), id);
            }
        }

        st
    }
}

/// Reconstruct one package instance's state datatype from the symbolic store —
/// the same shape as `smt_update_pkgstate_from_locals`, reading our store instead
/// of identifier names.
fn reconstruct_pkg_state(pctx: &PackageInstanceContext, st: &SymState) -> SmtExpr {
    let pkg = pctx.pkg();
    let pattern = pctx.pkg_state_pattern();
    let spec = pattern.datastructure_spec(pkg);
    pattern
        .call_constructor(&spec, vec![], &(), |sel: &PackageStateSelector| {
            let key = (pctx.pkg_inst_name().to_string(), sel.name.to_string());
            Some(SmtExpr::from(
                st.pkg_state
                    .get(&key)
                    .expect("every package-state field was seeded"),
            ))
        })
        .expect("package state has a single constructor")
}

/// Symbolically execute `inlined` to every terminal, returning one
/// [`TerminalPath`] per terminal.
///
/// `game_inst` must be the post-[`crate::transforms::theorem_transforms::DebugTransform`]
/// instance `inlined` was produced from; `sample_info` its matching
/// `GameInstAux::sample_info`.
pub fn execute(
    inlined: &InlinedOracle,
    game_inst: &GameInstance,
    sample_info: &SampleInfo,
    side: Side,
    max_paths: Option<usize>,
) -> Result<Vec<TerminalPath>, ExecError> {
    let mut out = Vec::new();
    execute_streaming(inlined, game_inst, sample_info, side, max_paths, &mut |p| {
        out.push(p.clone());
        ControlFlow::Continue(())
    })?;
    Ok(out)
}

/// Streaming variant of [`execute`]: `on_path` is called with each terminal path
/// as it is discovered and can return [`ControlFlow::Break`] to stop early
/// (story 06 interleaves solver queries this way). `max_paths` counts *completed*
/// paths and errors with [`ExecError::MaxPathsExceeded`] rather than truncating.
pub fn execute_streaming(
    inlined: &InlinedOracle,
    game_inst: &GameInstance,
    sample_info: &SampleInfo,
    side: Side,
    max_paths: Option<usize>,
    on_path: &mut dyn FnMut(&TerminalPath) -> ControlFlow<()>,
) -> Result<(), ExecError> {
    let mut exec = Executor::new(inlined, game_inst, sample_info, side, max_paths)?;
    let st = exec.initial_state();
    let frames = vec![Cursor {
        block: &inlined.body,
        ip: 0,
        kind: FrameKind::Sub,
    }];
    let _ = exec.walk(frames, st, on_path)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::project::Project as _;
    use crate::transforms::theorem_transforms::{DebugTransform, GameInstAux};
    use crate::transforms::TheoremTransform;

    fn with_debug<F>(dir: &str, theorem_name: &str, f: F)
    where
        F: FnOnce(&crate::theorem::Theorem, &[(String, GameInstAux)]),
    {
        let files =
            crate::project::DirectoryFiles::load(std::path::Path::new(dir)).unwrap();
        let project =
            crate::project::DirectoryProject::load(std::path::PathBuf::from(dir), &files)
                .unwrap();
        let theorem = project.get_theorem(theorem_name).unwrap();
        let (theorem, auxs) = DebugTransform.transform_theorem(theorem).unwrap();
        f(&theorem, &auxs);
    }

    fn sample_info_for<'a>(
        auxs: &'a [(String, GameInstAux)],
        game_inst: &str,
    ) -> &'a SampleInfo {
        &auxs
            .iter()
            .find(|(n, _)| n == game_inst)
            .unwrap_or_else(|| panic!("no aux for {game_inst}"))
            .1
            .sample_info
    }

    fn run(
        dir: &str,
        theorem: &str,
        game_inst: &str,
        oracle: &str,
    ) -> Vec<TerminalPath> {
        let mut result = None;
        with_debug(dir, theorem, |th, auxs| {
            let gi = th.find_game_instance(game_inst).unwrap();
            let inl = crate::debug::ir::inline_oracle(gi, oracle).unwrap();
            let si = sample_info_for(auxs, game_inst);
            result = Some(execute(&inl, gi, si, Side::Left, None).unwrap());
        });
        result.unwrap()
    }

    /// No SSA constant name is reused within a path.
    fn assert_ssa_unique(path: &TerminalPath) {
        let mut names = Vec::new();
        for d in &path.decls {
            if let SmtExpr::List(items) = d {
                if let [SmtExpr::Atom(kw), SmtExpr::Atom(name), ..] = items.as_slice() {
                    assert_eq!(kw, "declare-const");
                    names.push(name.clone());
                }
            }
        }
        let mut sorted = names.clone();
        sorted.sort();
        sorted.dedup();
        assert_eq!(sorted.len(), names.len(), "duplicate SSA decl: {names:?}");
    }

    #[test]
    fn hello_world_small_is_one_straightline_path() {
        let paths = run(
            "example-projects/hello-world",
            "Proof",
            "small_composition",
            "UsefulOracle",
        );
        assert_eq!(paths.len(), 1);
        let p = &paths[0];
        assert!(matches!(p.terminal, Terminal::Return { .. }));
        assert!(p.steps.is_empty(), "no branches in UsefulOracle");
        assert_ssa_unique(p);
        // ctr <- ctr + 1 ; rand <-$ Bits(n) ; return (ctr, rand)
        // seed state field `ctr` (1) + the assign (1) + the sample (1), plus the
        // game-state SSA constants threaded at the terminal.
        let non_gamestate = p
            .decls
            .iter()
            .filter(|d| !d.to_string().contains("!gamestate>"))
            .count();
        assert_eq!(non_gamestate, 3, "one seed + one assign + one sample");
        // return_constraint fills <return-small_composition-UsefulOracle>
        let rc = p.return_constraint.to_string();
        assert!(
            rc.contains("<return-small_composition-UsefulOracle>"),
            "{rc}"
        );
    }

    #[test]
    fn hello_world_medium_inlines_a_call_and_resumes() {
        // Fwd.UsefulOracle: `y <- invoke UsefulOracle(); return y;`
        // Rand.UsefulOracle: `ctr <- ctr+1; rand <-$; return (ctr,rand)`
        let paths = run(
            "example-projects/hello-world",
            "Proof",
            "medium_composition",
            "UsefulOracle",
        );
        assert_eq!(paths.len(), 1, "no branches");
        let p = &paths[0];
        assert!(matches!(p.terminal, Terminal::Return { .. }));
        assert_ssa_unique(p);
        // the callee's `return (ctr, rand)` must bind `y` and the entry frame
        // then returns `y` — i.e. the continuation after the Call ran.
        let rc = p.return_constraint.to_string();
        assert!(rc.contains("mk-return"), "{rc}");
    }

    #[test]
    fn hello_world_useless_assert_forks_into_hold_and_fail() {
        // Fwd.UselessOracle(x): `assert (x == 1); return 1;`
        let paths = run(
            "example-projects/hello-world",
            "Proof",
            "medium_composition_more_oracles",
            "UselessOracle",
        );
        assert_eq!(paths.len(), 2);
        let mut aborts = 0;
        let mut returns = 0;
        for p in &paths {
            assert_ssa_unique(p);
            match &p.terminal {
                Terminal::Abort { .. } => {
                    aborts += 1;
                    assert_eq!(p.steps.last().unwrap().decision, Decision::AssertFails);
                }
                Terminal::Return { .. } => {
                    returns += 1;
                    assert_eq!(p.steps.last().unwrap().decision, Decision::AssertHolds);
                }
            }
        }
        assert_eq!((aborts, returns), (1, 1));
    }

    #[test]
    fn simple_kem_test_branch_assert_unwrap_enumeration() {
        // Prot.TestSender(id):
        //   assert (SENTCTXT[id] != None);
        //   assert (TESTED[id]   != Some(true));
        //   TESTED[id] <- Some(true);
        //   k <- Unwrap(SENTKEY[id]);
        //   if isideal_kem_cpa_security { k <-$ Bits(256) }
        //   return k;
        let paths = run(
            "example-projects/simple-KEM-example",
            "KEM_Proof",
            "Prot",
            "TestSender",
        );

        // a1-fail -> abort ; a1-hold,a2-fail -> abort ; hold,hold,unwrap-none ->
        // abort ; hold,hold,some,if-then -> return ; hold,hold,some,if-else -> return
        assert_eq!(paths.len(), 5, "{:#?}", paths.iter().map(|p| &p.steps).collect::<Vec<_>>());
        let aborts = paths.iter().filter(|p| p.terminal.is_abort()).count();
        assert_eq!(aborts, 3);

        // the unwrap-none path aborts at the unwrap's own label.
        let unwrap_none = paths
            .iter()
            .find(|p| {
                p.steps
                    .iter()
                    .any(|s| s.decision == Decision::UnwrapNone)
            })
            .expect("one path takes the unwrap-none branch");
        assert!(unwrap_none.terminal.is_abort());
        let none_step = unwrap_none
            .steps
            .iter()
            .find(|s| s.decision == Decision::UnwrapNone)
            .unwrap();
        assert_eq!(unwrap_none.terminal.label(), none_step.label);

        for p in &paths {
            assert_ssa_unique(p);
        }
    }

    #[test]
    fn splitinvoke_continues_after_call_with_tuple_bind() {
        // Client.Query: `(x, y) <- invoke GetPair(); return x;`
        // Pair.GetPair: `return (false, b);`
        let paths = run(
            "test-projects/test-splitinvoke",
            "SplitInvokeProof",
            "game_split",
            "Query",
        );
        assert_eq!(paths.len(), 1);
        let p = &paths[0];
        assert!(matches!(p.terminal, Terminal::Return { .. }));
        assert_ssa_unique(p);
        // the tuple destructure produced `el2-1` / `el2-2` projections.
        let joined = p
            .constraints
            .iter()
            .map(|c| c.to_string())
            .collect::<String>();
        assert!(joined.contains("el2-1"), "{joined}");
    }

    #[test]
    fn max_paths_errors_with_progress() {
        let err = {
            let mut out = Err(ExecError::MaxPathsExceeded {
                explored: 0,
                limit: 0,
            });
            with_debug(
                "example-projects/simple-KEM-example",
                "KEM_Proof",
                |th, auxs| {
                    let gi = th.find_game_instance("Prot").unwrap();
                    let inl =
                        crate::debug::ir::inline_oracle(gi, "TestSender").unwrap();
                    let si = sample_info_for(auxs, "Prot");
                    out = execute(&inl, gi, si, Side::Left, Some(2));
                },
            );
            out.unwrap_err()
        };
        match err {
            ExecError::MaxPathsExceeded { explored, limit } => {
                assert_eq!(limit, 2);
                assert_eq!(explored, 2);
            }
            other => panic!("wrong error: {other:?}"),
        }
    }

    #[test]
    fn kem_dem_pkenc_path_count_is_small() {
        // The epic's primary target. PKENC has sampling + cross-package invokes;
        // the path count must be in the tens, not the thousands.
        let paths = run(
            "example-projects/kem-dem/kem-dem-cca-ssp",
            "kem_dem_cca_ssp",
            "Game_MON_CCA_PKE",
            "PKENC",
        );
        assert!(
            (1..=64).contains(&paths.len()),
            "unexpected path count: {}",
            paths.len()
        );
        for p in &paths {
            assert_ssa_unique(p);
        }
    }

    #[test]
    fn golden_hello_world_medium() {
        let paths = run(
            "example-projects/hello-world",
            "Proof",
            "medium_composition",
            "UsefulOracle",
        );
        assert_eq!(paths.len(), 1);
        let p = &paths[0];
        let render = |v: &[SmtExpr]| {
            v.iter().map(|e| e.to_string()).collect::<Vec<_>>().join("\n")
        };
        let actual = format!(
            "; decls\n{}\n; constraints\n{}\n; return\n{}\n",
            render(&p.decls),
            render(&p.constraints),
            p.return_constraint,
        );
        let golden_path =
            std::path::Path::new("testdata/story05/hello_world_medium.smt2");
        if !golden_path.exists() {
            std::fs::create_dir_all(golden_path.parent().unwrap()).unwrap();
            std::fs::write(golden_path, &actual).unwrap();
            panic!("wrote missing golden {golden_path:?} — re-run the test");
        }
        let expected = std::fs::read_to_string(golden_path).unwrap();
        assert_eq!(actual, expected, "golden mismatch for {golden_path:?}");
    }
}
