// SPDX-License-Identifier: MIT OR Apache-2.0

//! An AST-level, fully-inlined representation of one exported oracle.
//!
//! [`inline_oracle`] takes a game instance that has already been run through
//! [`crate::transforms::theorem_transforms::DebugTransform`] and the *exported*
//! name of one of its oracles, and resolves every `invoke` across package
//! boundaries into the callee's body — but, unlike the textual inliner on branch
//! `amir/ty-params-features`, it produces a structure the symbolic executor can
//! walk rather than a string.
//!
//! # The crux: `Call` stays nested
//!
//! A callee can `return` from inside a branch. Flattening it into the caller
//! would require duplicating the caller's continuation into every callee leaf —
//! exactly the blow-up `treeify` causes and the debugger avoids. So the IR keeps
//! a [`InlStmt::Call`] node with the callee body **nested** inside it. The
//! executor (story 05) treats a [`InlStmt::Return`] inside a frame as "bind the
//! call's result and continue after the `Call` node", using a frame stack.
//!
//! `abort` is different — it propagates. A callee abort aborts the *whole*
//! oracle, so [`InlStmt::Abort`] is always a global terminal, no matter how deep
//! the frame.
//!
//! # Labelling and rendering are one pass
//!
//! A [`Label`] is a 1-based line number in [`Listing::text`], which is the single
//! source of truth. The code is walked once: every [`InlStmt`] gets its own line
//! and records `label = current_line_number` plus a [`SiteInfo`] in
//! [`Listing::sites`]; structural lines (braces, the frame header) get no label.
//!
//! # Locals vs. state
//!
//! - **Locals** (oracle arguments and body-local variables) are alpha-renamed
//!   per frame to `"{pkg_inst}#{frame_id}::{name}"` ([`VarKey`]) so two frames of
//!   the same package instance never collide. They become
//!   [`Place::Local`] / [`Identifier::Generated`].
//! - **Package state fields** are *not* renamed and *not* frame-scoped; they
//!   become [`Place::State`], keyed by `(pkg_inst, field)` globally. This is how
//!   the existing SMT encoding gets re-entrant-call semantics for free, and
//!   story 05's symbolic store mirrors it exactly.
//! - **Package/game/theorem constants** are left completely alone so the SMT they
//!   generate keeps matching the prover's.

use std::collections::BTreeMap;

use miette::SourceSpan;

use crate::{
    expressions::{Expression, ExpressionKind},
    identifier::{
        game_ident::GameIdentifier, pkg_ident::PackageIdentifier, theorem_ident::TheoremIdentifier,
        Identifier,
    },
    package::Edge,
    statement::{Assignment, AssignmentRhs, CodeBlock, InvokeOracle, Pattern, Statement},
    theorem::GameInstance,
    types::{CountSpec, Type, TypeKind},
};

/// Recursion is bounded so a malformed (cyclic) composition can't loop forever.
/// Same value the textual inliner on `amir/ty-params-features` used.
pub const MAX_INLINE_DEPTH: usize = 128;

/// 1-based line number in the rendered listing. The listing is the single source
/// of truth for labels.
pub type Label = usize;

/// Unique key for a frame-local. `format!("{pkg_inst}#{frame_id}::{name}")`.
pub type VarKey = String;

/// One exported oracle, fully inlined.
#[derive(Debug, Clone)]
pub struct InlinedOracle {
    pub game_inst_name: String,
    /// The *exported* name.
    pub oracle_name: String,
    pub entry_pkg_inst: String,
    /// The exported signature's arguments. In the body these are referenced under
    /// the entry frame's keys: `"{entry_pkg_inst}#0::{arg_name}"`.
    pub args: Vec<(String, Type)>,
    pub return_type: Type,
    pub body: InlBlock,
    pub listing: Listing,
}

#[derive(Debug, Clone)]
pub struct InlBlock(pub Vec<InlStmt>);

#[derive(Debug, Clone)]
pub enum InlStmt {
    Assign {
        label: Label,
        target: Place,
        rhs: Expression,
    },
    Sample {
        label: Label,
        target: Place,
        sample_id: usize,
        ty: Type,
        sample_name: String,
    },
    /// Branch point: aborts when `inner` is none, otherwise binds
    /// `(maybe-get inner)` into `target`. Decisions are `some` / `none`.
    Unwrap {
        label: Label,
        target: Place,
        inner: Expression,
    },
    /// A conditional. For `is_assert` branches the decisions are `holds` /
    /// `fails` and `els` is always a single [`InlStmt::Abort`].
    Branch {
        label: Label,
        cond: Expression,
        then: InlBlock,
        els: InlBlock,
        is_assert: bool,
        /// Lines the *then* block occupies, inclusive, excluding the `if` line
        /// itself: `(first, last)` where `last` is the `}` or `} else {` row.
        /// `None` for a synthetic `assert` (one line, no block).
        then_lines: Option<(Label, Label)>,
        /// Likewise for the *else* block, `None` when there is no `else`.
        else_lines: Option<(Label, Label)>,
    },
    /// An inlined `invoke`. The callee body is NESTED, not flattened. A
    /// [`InlStmt::Return`] inside `body` binds its value into `bind` and
    /// continues after this node.
    Call {
        label: Label,
        frame: FrameInfo,
        bind: Option<Place>,
        body: InlBlock,
        /// `{`, the `param <- arg;` bindings and the closing `}` of the
        /// inlined frame: `(first, last)` — `first` is the `{`, `last` the `}`.
        frame_lines: (Label, Label),
        /// The argument-binding rows, `(first, last)`; `None` for a 0-arg
        /// oracle.
        arg_lines: Option<(Label, Label)>,
    },
    /// Return from the current frame. At the entry frame this is a global
    /// terminal; inside a [`InlStmt::Call`] frame it resumes the caller.
    Return {
        label: Label,
        value: Option<Expression>,
    },
    /// Global terminal — aborts the whole oracle regardless of frame depth.
    Abort { label: Label },
}

#[allow(clippy::large_enum_variant)]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Place {
    /// A frame-local variable (already alpha-renamed).
    Local { key: VarKey, ty: Type },
    /// A package state field. Shared across all frames of the same package
    /// instance, keyed by `(pkg_inst, field)` globally.
    State {
        pkg_inst: String,
        field: String,
        ty: Type,
    },
    /// Table write: `base[index] <- ...` against either of the above.
    Index { base: Box<Place>, index: Expression },
    /// Destructuring bind, e.g. `(a, b) <- ...`. Never produced for an `invoke`
    /// bind (`deconstructinvoke` rules that out); only for plain expression
    /// assignments. Story 05 evaluates the RHS to a tuple and binds
    /// component-wise.
    Tuple(Vec<Place>),
    /// The `_` discard.
    Discard,
}

#[derive(Debug, Clone)]
pub struct FrameInfo {
    pub frame_id: usize,
    pub pkg_inst_name: String,
    pub oracle_name: String,
    /// callee parameter key -> caller-side argument expression, already rewritten
    /// into the caller's namespace. Bound as locals of the new frame on entry.
    pub arg_bindings: Vec<(VarKey, Type, Expression)>,
    pub return_type: Type,
}

#[derive(Debug, Clone)]
pub struct Listing {
    /// The rendered code, one label per line. Story 03 re-uses this verbatim.
    pub text: String,
    pub sites: BTreeMap<Label, SiteInfo>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SiteKind {
    Assign,
    Sample,
    Unwrap,
    Branch,
    Assert,
    Call,
    Return,
    Abort,
}

#[derive(Debug, Clone)]
pub struct SiteInfo {
    pub kind: SiteKind,
    /// The rendered line, trimmed.
    pub line: String,
    /// Back-reference into the original source.
    pub span: SourceSpan,
    pub pkg_inst_name: String,
    pub oracle_name: String,
    /// Frame depth: 0 for the entry oracle's own body, 1 for a directly inlined
    /// callee, and so on.
    pub depth: usize,
}

#[derive(Debug, thiserror::Error, miette::Diagnostic)]
pub enum InlineError {
    #[error("oracle `{oracle}` is not exported by game instance `{game_inst}`")]
    OracleNotExported { oracle: String, game_inst: String },

    #[error("could not find the definition of oracle `{oracle}` in package instance `{pkg_inst}`")]
    CalleeNotFound { oracle: String, pkg_inst: String },

    #[error(
        "maximum inline depth ({max}) exceeded while inlining `{oracle}` \
         (the composition is probably recursive)"
    )]
    MaxDepthExceeded { oracle: String, max: usize },

    #[error(
        "BUG: unresolved oracle edge for `{oracle}` in package instance `{pkg_inst}` — \
         `resolveoracles` should have filled this in before `inline_oracle` runs"
    )]
    UnresolvedEdge { oracle: String, pkg_inst: String },
}

/// Inline `oracle_name` (an *exported* name) of `game_inst`, which must already
/// have been run through
/// [`crate::transforms::theorem_transforms::DebugTransform`].
pub fn inline_oracle(
    game_inst: &GameInstance,
    oracle_name: &str,
) -> Result<InlinedOracle, InlineError> {
    let comp = game_inst.game();

    let export = comp
        .exports
        .iter()
        .find(|export| export.name() == oracle_name)
        .ok_or_else(|| InlineError::OracleNotExported {
            oracle: oracle_name.to_string(),
            game_inst: game_inst.name().to_string(),
        })?;

    let entry_pkg_inst = &comp.pkgs[export.to()];
    let odef = entry_pkg_inst
        .pkg
        .oracles
        .iter()
        .find(|odef| odef.sig.name == export.sig().name)
        .ok_or_else(|| InlineError::CalleeNotFound {
            oracle: export.sig().name.clone(),
            pkg_inst: entry_pkg_inst.name.clone(),
        })?;

    let mut inliner = Inliner {
        comp,
        game_inst_name: game_inst.name().to_string(),
        next_frame_id: 0,
        text: String::new(),
        line: 0,
        sites: BTreeMap::new(),
    };

    let entry_frame = Frame {
        frame_id: inliner.alloc_frame(),
        pkg_inst_name: entry_pkg_inst.name.clone(),
        oracle_name: export.sig().name.clone(),
        ret: Ret::Top,
    };

    inliner.emit(
        0,
        &format!(
            "// game instance: {}   (package instance: {}, package: {})",
            game_inst.name(),
            entry_pkg_inst.name,
            entry_pkg_inst.pkg.name,
        ),
    );
    inliner.emit(0, &format!("{} {{", render_signature(export.sig())));
    let body = inliner.render_block(&odef.code, &entry_frame, 0, 1)?;
    inliner.emit(0, "}");

    Ok(InlinedOracle {
        game_inst_name: game_inst.name().to_string(),
        oracle_name: export.name().to_string(),
        entry_pkg_inst: entry_pkg_inst.name.clone(),
        args: export.sig().args.clone(),
        return_type: export.sig().ty.clone(),
        body,
        listing: Listing {
            text: inliner.text,
            sites: inliner.sites,
        },
    })
}

/// Number of syntactic terminals reachable through this oracle's IR: every
/// `return` at the entry frame, every `abort`, and the implicit abort of every
/// `unwrap` (its `none` child).
///
/// Purely structural and solver-free — an **upper bound** on the paths a
/// `domino debug` run explores, since branch pruning (story 08) and
/// `--check-left` cut infeasible branches. `loopunroll` has already run, so the
/// IR has no loops and this is a finite fold over the statement tree. Saturating,
/// so a pathological composition cannot overflow it.
///
/// With no [`BranchOracle`] the symbolic executor walks exactly these paths, so
/// `count_terminals(inl) == exec::execute(inl, …).len()` exactly.
pub fn count_terminals(inlined: &InlinedOracle) -> u64 {
    /// `k_fall`: terminals reachable if control falls off the end of `stmts`
    /// (resuming whatever encloses this block). `k_ret`: terminals reachable
    /// from a `return` in `stmts` — the caller's continuation for a `Call` body,
    /// `1` (the oracle really returns) at the entry frame.
    fn f(stmts: &[InlStmt], k_fall: u64, k_ret: u64) -> u64 {
        let Some((head, rest)) = stmts.split_first() else {
            return k_fall;
        };
        match head {
            InlStmt::Assign { .. } | InlStmt::Sample { .. } => f(rest, k_fall, k_ret),
            InlStmt::Unwrap { .. } => 1u64.saturating_add(f(rest, k_fall, k_ret)),
            InlStmt::Branch { then, els, .. } => {
                let k = f(rest, k_fall, k_ret);
                f(&then.0, k, k_ret).saturating_add(f(&els.0, k, k_ret))
            }
            InlStmt::Call { body, .. } => {
                let k = f(rest, k_fall, k_ret);
                f(&body.0, k, k)
            }
            InlStmt::Return { .. } => k_ret,
            InlStmt::Abort { .. } => 1,
        }
    }
    f(&inlined.body.0, 1, 1)
}

/// Rendering context for one stack frame.
struct Frame {
    frame_id: usize,
    pkg_inst_name: String,
    oracle_name: String,
    ret: Ret,
}

/// How a `return` inside this frame is rendered / interpreted.
enum Ret {
    /// The entry oracle: `return` really returns.
    Top,
    /// An inlined callee: `return e` becomes `<bind> <- e` and resumes the
    /// caller.
    Inlined { bind_text: String, from: String },
}

impl Frame {
    fn key(&self, name: &str) -> VarKey {
        format!("{}#{}::{}", self.pkg_inst_name, self.frame_id, name)
    }
}

struct Inliner<'c> {
    comp: &'c crate::package::Composition,
    game_inst_name: String,
    next_frame_id: usize,
    text: String,
    line: Label,
    sites: BTreeMap<Label, SiteInfo>,
}

impl<'c> Inliner<'c> {
    fn alloc_frame(&mut self) -> usize {
        let id = self.next_frame_id;
        self.next_frame_id += 1;
        id
    }

    /// Appends one line (with `indent` levels of 4-space indentation) and returns
    /// its 1-based line number.
    fn emit(&mut self, indent: usize, content: &str) -> Label {
        for _ in 0..indent {
            self.text.push_str("    ");
        }
        self.text.push_str(content);
        self.text.push('\n');
        self.line += 1;
        self.line
    }

    #[allow(clippy::too_many_arguments)]
    fn record_site(
        &mut self,
        label: Label,
        kind: SiteKind,
        content: &str,
        span: SourceSpan,
        frame: &Frame,
        depth: usize,
    ) {
        self.sites.insert(
            label,
            SiteInfo {
                kind,
                line: content.trim().to_string(),
                span,
                pkg_inst_name: frame.pkg_inst_name.clone(),
                oracle_name: frame.oracle_name.clone(),
                depth,
            },
        );
    }

    fn render_block(
        &mut self,
        block: &CodeBlock,
        frame: &Frame,
        depth: usize,
        indent: usize,
    ) -> Result<InlBlock, InlineError> {
        let mut stmts = Vec::with_capacity(block.0.len());
        for stmt in &block.0 {
            stmts.push(self.render_stmt(stmt, frame, depth, indent)?);
        }
        Ok(InlBlock(stmts))
    }

    fn render_stmt(
        &mut self,
        stmt: &Statement,
        frame: &Frame,
        depth: usize,
        indent: usize,
    ) -> Result<InlStmt, InlineError> {
        match stmt {
            Statement::Abort(span) => {
                let label = self.emit(indent, "abort;");
                self.record_site(label, SiteKind::Abort, "abort;", *span, frame, depth);
                Ok(InlStmt::Abort { label })
            }

            Statement::Return(value, span) => {
                let value_ir = value.as_ref().map(|e| rewrite_expr(e, frame));
                let content = match &frame.ret {
                    Ret::Top => match value {
                        Some(e) => format!("return {};", render_expr(e)),
                        None => "return;".to_string(),
                    },
                    Ret::Inlined { bind_text, from } => match value {
                        Some(e) => {
                            format!("{bind_text} <- {};  // return from {from}", render_expr(e))
                        }
                        None => format!("{bind_text} <- ();  // return from {from}"),
                    },
                };
                let label = self.emit(indent, &content);
                self.record_site(label, SiteKind::Return, &content, *span, frame, depth);
                Ok(InlStmt::Return {
                    label,
                    value: value_ir,
                })
            }

            Statement::Assignment(Assignment { pattern, rhs }, span) => match rhs {
                AssignmentRhs::Invoke {
                    oracle_name,
                    args,
                    edge,
                    ..
                } => self.render_call(
                    Some(pattern),
                    oracle_name,
                    args,
                    edge.as_ref(),
                    *span,
                    frame,
                    depth,
                    indent,
                ),

                AssignmentRhs::Sample {
                    ty,
                    sample_name,
                    sample_id,
                } => {
                    let target = self.place_from_pattern(pattern, frame);
                    let name_part = match sample_name {
                        Some(n) => format!(" sample-name {n}"),
                        None => String::new(),
                    };
                    let content = format!(
                        "{} <-$ {}{name_part};",
                        render_pattern(pattern),
                        render_type(ty),
                    );
                    let label = self.emit(indent, &content);
                    self.record_site(label, SiteKind::Sample, &content, *span, frame, depth);
                    Ok(InlStmt::Sample {
                        label,
                        target,
                        sample_id: sample_id
                            .expect("samplify assigns a sample_id to every sampling point"),
                        ty: ty.clone(),
                        sample_name: sample_name.clone().unwrap_or_default(),
                    })
                }

                AssignmentRhs::Expression(e) => {
                    let target = self.place_from_pattern(pattern, frame);
                    if let ExpressionKind::Unwrap(inner) = e.kind() {
                        let content = format!(
                            "{} <- unwrap({});",
                            render_pattern(pattern),
                            render_expr(inner),
                        );
                        let label = self.emit(indent, &content);
                        self.record_site(label, SiteKind::Unwrap, &content, *span, frame, depth);
                        Ok(InlStmt::Unwrap {
                            label,
                            target,
                            inner: rewrite_expr(inner, frame),
                        })
                    } else {
                        let content = format!("{} <- {};", render_pattern(pattern), render_expr(e));
                        let label = self.emit(indent, &content);
                        self.record_site(label, SiteKind::Assign, &content, *span, frame, depth);
                        Ok(InlStmt::Assign {
                            label,
                            target,
                            rhs: rewrite_expr(e, frame),
                        })
                    }
                }
            },

            Statement::InvokeOracle(InvokeOracle {
                oracle_name,
                args,
                edge,
                file_pos,
            }) => self.render_call(
                None,
                oracle_name,
                args,
                edge.as_ref(),
                *file_pos,
                frame,
                depth,
                indent,
            ),

            Statement::IfThenElse(ite) => {
                let is_assert = ite.then_block.0.is_empty()
                    && ite.else_block.0.len() == 1
                    && matches!(ite.else_block.0[0], Statement::Abort(_));

                let cond_ir = rewrite_expr(&ite.cond, frame);

                if is_assert {
                    let content = format!("assert ({});", render_expr(&ite.cond));
                    let label = self.emit(indent, &content);
                    self.record_site(
                        label,
                        SiteKind::Assert,
                        &content,
                        ite.full_span,
                        frame,
                        depth,
                    );
                    // The synthetic abort re-uses the assert's line: `assert` is
                    // rendered as one line, so there is no separate line for it.
                    Ok(InlStmt::Branch {
                        label,
                        cond: cond_ir,
                        then: InlBlock(vec![]),
                        els: InlBlock(vec![InlStmt::Abort { label }]),
                        is_assert: true,
                        then_lines: None,
                        else_lines: None,
                    })
                } else {
                    let content = format!("if ({}) {{", render_expr(&ite.cond));
                    let label = self.emit(indent, &content);
                    self.record_site(
                        label,
                        SiteKind::Branch,
                        &content,
                        ite.full_span,
                        frame,
                        depth,
                    );
                    let then_first = label + 1;
                    let then = self.render_block(&ite.then_block, frame, depth, indent + 1)?;
                    let (then_close, els, else_lines) = if ite.else_block.0.is_empty() {
                        let close = self.emit(indent, "}");
                        (close, InlBlock(vec![]), None)
                    } else {
                        let close = self.emit(indent, "} else {");
                        let els_first = close + 1;
                        let els = self.render_block(&ite.else_block, frame, depth, indent + 1)?;
                        let els_close = self.emit(indent, "}");
                        (close, els, Some((els_first, els_close)))
                    };
                    Ok(InlStmt::Branch {
                        label,
                        cond: cond_ir,
                        then,
                        els,
                        is_assert: false,
                        then_lines: Some((then_first, then_close)),
                        else_lines,
                    })
                }
            }

            Statement::For(_, _, _, _, _) => unreachable!(
                "a `for` statement survived into the debug IR — `loopunroll` runs before \
                 `inline_oracle` and must have eliminated it. \
                 game instance: {}, package instance: {}, oracle: {}",
                self.game_inst_name, frame.pkg_inst_name, frame.oracle_name,
            ),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn render_call(
        &mut self,
        bind_pattern: Option<&Pattern>,
        oracle_name: &str,
        args: &[Expression],
        edge: Option<&Edge>,
        span: SourceSpan,
        caller: &Frame,
        depth: usize,
        indent: usize,
    ) -> Result<InlStmt, InlineError> {
        let edge = edge.ok_or_else(|| InlineError::UnresolvedEdge {
            oracle: oracle_name.to_string(),
            pkg_inst: caller.pkg_inst_name.clone(),
        })?;

        let target_pkg_inst = &self.comp.pkgs[edge.to()];
        let target_sig = edge.sig();
        let target_odef = target_pkg_inst
            .pkg
            .oracles
            .iter()
            .find(|odef| odef.sig.name == target_sig.name)
            .ok_or_else(|| InlineError::CalleeNotFound {
                oracle: target_sig.name.clone(),
                pkg_inst: target_pkg_inst.name.clone(),
            })?;

        if depth + 1 > MAX_INLINE_DEPTH {
            return Err(InlineError::MaxDepthExceeded {
                oracle: oracle_name.to_string(),
                max: MAX_INLINE_DEPTH,
            });
        }

        let frame_id = self.alloc_frame();

        let bind_text = match bind_pattern {
            None => "_".to_string(),
            Some(p) => {
                assert!(
                    !matches!(p, Pattern::Tuple(_)),
                    "`deconstructinvoke` guarantees an invoke's bind is never a tuple pattern",
                );
                render_pattern(p)
            }
        };
        let bind = bind_pattern.map(|p| self.place_from_pattern(p, caller));

        let from = format!("{}.{}", target_pkg_inst.name, target_sig.name);
        let args_txt = args.iter().map(render_expr).collect::<Vec<_>>().join(", ");
        let content = match bind_pattern {
            Some(_) => format!("{bind_text} <- invoke {oracle_name}({args_txt})      // {from}"),
            None => format!("invoke {oracle_name}({args_txt})      // {from}"),
        };
        let label = self.emit(indent, &content);
        self.record_site(label, SiteKind::Call, &content, span, caller, depth);

        let open_label = self.emit(indent, "{");

        let callee_frame = Frame {
            frame_id,
            pkg_inst_name: target_pkg_inst.name.clone(),
            oracle_name: target_sig.name.clone(),
            ret: Ret::Inlined {
                bind_text,
                from: from.clone(),
            },
        };

        let mut arg_bindings = Vec::with_capacity(target_sig.args.len());
        let mut arg_lines: Option<(Label, Label)> = None;
        for ((param_name, param_ty), arg_expr) in target_sig.args.iter().zip(args) {
            let arg_label = self.emit(
                indent + 1,
                &format!("{param_name} <- {};", render_expr(arg_expr)),
            );
            arg_lines = Some(match arg_lines {
                None => (arg_label, arg_label),
                Some((first, _)) => (first, arg_label),
            });
            arg_bindings.push((
                callee_frame.key(param_name),
                param_ty.clone(),
                // argument expressions live in the *caller's* namespace
                rewrite_expr(arg_expr, caller),
            ));
        }

        let body = self.render_block(&target_odef.code, &callee_frame, depth + 1, indent + 1)?;
        let close_label = self.emit(indent, "}");

        Ok(InlStmt::Call {
            label,
            frame: FrameInfo {
                frame_id,
                pkg_inst_name: target_pkg_inst.name.clone(),
                oracle_name: target_sig.name.clone(),
                arg_bindings,
                return_type: target_sig.ty.clone(),
            },
            bind,
            body,
            frame_lines: (open_label, close_label),
            arg_lines,
        })
    }

    fn place_from_pattern(&self, pattern: &Pattern, frame: &Frame) -> Place {
        match pattern {
            Pattern::Ident(id) => place_from_ident(id, frame),
            Pattern::Table { ident, index } => Place::Index {
                base: Box::new(place_from_ident(ident, frame)),
                index: rewrite_expr(index, frame),
            },
            Pattern::Tuple(ids) => {
                Place::Tuple(ids.iter().map(|id| place_from_ident(id, frame)).collect())
            }
        }
    }
}

fn place_from_ident(id: &Identifier, frame: &Frame) -> Place {
    if id.ident_ref() == "_" {
        return Place::Discard;
    }
    match id {
        Identifier::PackageIdentifier(PackageIdentifier::State(s)) => Place::State {
            pkg_inst: s
                .pkg_inst_name
                .clone()
                .unwrap_or_else(|| s.pkg_name.clone()),
            field: s.name.clone(),
            ty: s.ty.clone(),
        },
        Identifier::Generated(name, ty) => Place::Local {
            key: frame.key(name),
            ty: ty.clone(),
        },
        Identifier::PackageIdentifier(PackageIdentifier::Local(l)) => Place::Local {
            key: frame.key(&l.name),
            ty: l.ty.clone(),
        },
        Identifier::PackageIdentifier(PackageIdentifier::OracleArg(a)) => Place::Local {
            key: frame.key(&a.name),
            ty: a.ty.clone(),
        },
        other => unreachable!("unexpected identifier as an assignment target: {other:?}"),
    }
}

/// Alpha-renames frame-local identifiers in `e` into the frame's namespace and
/// leaves package state / constants untouched. Uses [`Expression::map`], like
/// `unwrapify`.
fn rewrite_expr(e: &Expression, frame: &Frame) -> Expression {
    e.map(|sub| match sub.kind() {
        ExpressionKind::Identifier(id) => Expression::from(rewrite_ident(id, frame)),
        ExpressionKind::TableAccess(id, index) => Expression::from_kind(
            ExpressionKind::TableAccess(rewrite_ident(id, frame), index.clone()),
        ),
        _ => sub,
    })
}

fn rewrite_ident(id: &Identifier, frame: &Frame) -> Identifier {
    match id {
        Identifier::Generated(name, ty) => Identifier::Generated(frame.key(name), ty.clone()),
        Identifier::PackageIdentifier(PackageIdentifier::Local(l)) => {
            Identifier::Generated(frame.key(&l.name), l.ty.clone())
        }
        Identifier::PackageIdentifier(PackageIdentifier::OracleArg(a)) => {
            Identifier::Generated(frame.key(&a.name), a.ty.clone())
        }
        // package state (keyed globally), and package/game/theorem constants
        // (resolved through the existing const machinery) are left alone.
        other => other.clone(),
    }
}

//
// -------- textual rendering (ported from `amir/ty-params-features:src/inline.rs`) --------
//
// These render the *original* (un-alpha-renamed) AST, so the listing stays
// readable: bare local names, `Instance.field` for state, constants followed
// down to a literal or a theorem constant.
//

fn render_signature(sig: &crate::package::OracleSig) -> String {
    let args = sig
        .args
        .iter()
        .map(|(name, ty)| format!("{name}: {}", render_type(ty)))
        .collect::<Vec<_>>()
        .join(", ");
    format!("{}({args}) -> {}", sig.name, render_type(&sig.ty))
}

fn render_pattern(pattern: &Pattern) -> String {
    match pattern {
        Pattern::Ident(id) => ident_repr(id),
        Pattern::Table { ident, index } => format!("{}[{}]", ident_repr(ident), render_expr(index)),
        Pattern::Tuple(ids) => format!(
            "({})",
            ids.iter().map(ident_repr).collect::<Vec<_>>().join(", ")
        ),
    }
}

fn render_expr(expr: &Expression) -> String {
    // Follow package/game constants down to a literal or a theorem constant.
    let expr = resolve_const(expr);

    let joined = |exprs: &[Expression], sep: &str| {
        exprs.iter().map(render_expr).collect::<Vec<_>>().join(sep)
    };

    match expr.kind() {
        ExpressionKind::Bot => "\u{22a5}".to_string(),
        ExpressionKind::Sample(ty) => format!("Sample({})", render_type(ty)),
        ExpressionKind::StringLiteral(s) => format!("{s:?}"),
        ExpressionKind::IntegerLiteral(i) => format!("{i}"),
        ExpressionKind::BooleanLiteral(s) => s.clone(),
        ExpressionKind::BitsLiteral(s, _) => s.clone(),
        ExpressionKind::Identifier(ident) => ident_repr(ident),
        ExpressionKind::EmptyTable(ty) => format!("EmptyTable({})", render_type(ty)),
        ExpressionKind::TableAccess(ident, index) => {
            format!("{}[{}]", ident_repr(ident), render_expr(index))
        }
        ExpressionKind::Tuple(exprs) => format!("({})", joined(exprs, ", ")),
        ExpressionKind::List(exprs) => format!("[{}]", joined(exprs, ", ")),
        ExpressionKind::Set(exprs) => format!("{{{}}}", joined(exprs, ", ")),
        ExpressionKind::Concat(exprs) => format!("concat({})", joined(exprs, ", ")),
        ExpressionKind::FnCall(ident, args) => {
            format!("{}({})", ident_repr(ident), joined(args, ", "))
        }
        ExpressionKind::None(_) => "None".to_string(),
        ExpressionKind::Some(e) => format!("Some({})", render_expr(e)),
        ExpressionKind::Unwrap(e) => format!("Unwrap({})", render_expr(e)),
        ExpressionKind::Not(e) => format!("not ({})", render_expr(e)),
        ExpressionKind::Neg(e) => format!("-({})", render_expr(e)),
        ExpressionKind::Inv(e) => format!("(1 / {})", render_expr(e)),
        ExpressionKind::Sum(e) => format!("sum({})", render_expr(e)),
        ExpressionKind::Prod(e) => format!("prod({})", render_expr(e)),
        ExpressionKind::Any(e) => format!("any({})", render_expr(e)),
        ExpressionKind::All(e) => format!("all({})", render_expr(e)),
        ExpressionKind::Union(e) => format!("union({})", render_expr(e)),
        ExpressionKind::Cut(e) => format!("cut({})", render_expr(e)),
        ExpressionKind::SetDiff(e) => format!("setdiff({})", render_expr(e)),
        ExpressionKind::Add(l, r) => format!("({} + {})", render_expr(l), render_expr(r)),
        ExpressionKind::Sub(l, r) => format!("({} - {})", render_expr(l), render_expr(r)),
        ExpressionKind::Mul(l, r) => format!("({} * {})", render_expr(l), render_expr(r)),
        ExpressionKind::Div(l, r) => format!("({} / {})", render_expr(l), render_expr(r)),
        ExpressionKind::Pow(l, r) => format!("({} ^ {})", render_expr(l), render_expr(r)),
        ExpressionKind::Mod(l, r) => format!("({} % {})", render_expr(l), render_expr(r)),
        ExpressionKind::LessThen(l, r) => format!("({} < {})", render_expr(l), render_expr(r)),
        ExpressionKind::GreaterThen(l, r) => format!("({} > {})", render_expr(l), render_expr(r)),
        ExpressionKind::LessThenEq(l, r) => format!("({} <= {})", render_expr(l), render_expr(r)),
        ExpressionKind::GreaterThenEq(l, r) => {
            format!("({} >= {})", render_expr(l), render_expr(r))
        }
        ExpressionKind::Equals(exprs) => format!("({})", joined(exprs, " == ")),
        ExpressionKind::And(exprs) => format!("({})", joined(exprs, " and ")),
        ExpressionKind::Or(exprs) => format!("({})", joined(exprs, " or ")),
        ExpressionKind::Xor(exprs) => format!("({})", joined(exprs, " xor ")),
    }
}

fn render_type(ty: &Type) -> String {
    match ty.kind() {
        TypeKind::Boolean => "Bool".to_string(),
        TypeKind::Bits(cs) => format!("Bits({})", render_countspec(cs)),
        TypeKind::Maybe(t) => format!("Maybe({})", render_type(t)),
        TypeKind::Tuple(types) => format!(
            "({})",
            types.iter().map(render_type).collect::<Vec<_>>().join(", ")
        ),
        TypeKind::Table(key, value) => {
            format!("Table({}, {})", render_type(key), render_type(value))
        }
        TypeKind::Fn(args, ret) => format!(
            "fn {} -> {}",
            args.iter().map(render_type).collect::<Vec<_>>().join(", "),
            render_type(ret),
        ),
        _ => ty.to_string(),
    }
}

fn render_countspec(cs: &CountSpec) -> String {
    match cs {
        CountSpec::Any | CountSpec::Literal(_) => format!("{cs}"),
        CountSpec::Identifier(ident) => render_bare_ident(ident),
    }
}

/// A bare [`Identifier`] that is not wrapped in an [`ExpressionKind::Identifier`]
/// (a `Bits(n)` length, a `FnCall` callee): follow a const assignment if there
/// is one, otherwise print the name.
fn render_bare_ident(ident: &Identifier) -> String {
    let assignment = match ident {
        Identifier::PackageIdentifier(PackageIdentifier::Const(c)) => c.game_assignment.as_deref(),
        Identifier::GameIdentifier(GameIdentifier::Const(c)) => c.assigned_value.as_deref(),
        _ => None,
    };
    match assignment {
        Some(expr) => render_expr(expr),
        None => ident_repr(ident),
    }
}

/// Follows the chain of const-identifier assignments down to either a non-const
/// expression (usually a literal) or an identifier with no further assignment (a
/// theorem constant).
fn resolve_const(expr: &Expression) -> &Expression {
    match expr.kind() {
        ExpressionKind::Identifier(Identifier::PackageIdentifier(PackageIdentifier::Const(c))) => {
            match &c.game_assignment {
                Some(inner) => resolve_const(inner),
                None => expr,
            }
        }
        ExpressionKind::Identifier(Identifier::GameIdentifier(GameIdentifier::Const(c))) => {
            match &c.assigned_value {
                Some(inner) => resolve_const(inner),
                None => expr,
            }
        }
        _ => expr,
    }
}

/// The display name of an identifier. Package state is qualified with its owning
/// package instance (`Instance.field`) since inlining brings identically-named
/// state from several instances into one block.
fn ident_repr(ident: &Identifier) -> String {
    match ident {
        Identifier::Generated(name, _) => name.clone(),

        Identifier::PackageIdentifier(PackageIdentifier::Const(c)) => c.name.clone(),
        Identifier::PackageIdentifier(PackageIdentifier::State(s)) => format!(
            "{}.{}",
            s.pkg_inst_name.as_deref().unwrap_or(&s.pkg_name),
            s.name
        ),
        Identifier::PackageIdentifier(PackageIdentifier::Local(l)) => l.name.clone(),
        Identifier::PackageIdentifier(PackageIdentifier::OracleArg(a)) => a.name.clone(),
        Identifier::PackageIdentifier(PackageIdentifier::OracleImport(o)) => o.name.clone(),
        Identifier::PackageIdentifier(PackageIdentifier::ImportsLoopVar(l)) => l.name.clone(),
        Identifier::PackageIdentifier(PackageIdentifier::CodeLoopVar(l)) => l.name.clone(),

        Identifier::GameIdentifier(GameIdentifier::Const(c)) => c.name.clone(),
        Identifier::GameIdentifier(GameIdentifier::LoopVar(l)) => l.name.clone(),

        Identifier::TheoremIdentifier(TheoremIdentifier::Const(c)) => c.name.clone(),
        Identifier::TheoremIdentifier(TheoremIdentifier::LoopVar(l)) => l.name.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::project::Project as _;
    use crate::transforms::{theorem_transforms::DebugTransform, TheoremTransform};

    /// Loads `dir`, runs [`DebugTransform`], and hands `f` the transformed
    /// theorem.
    fn with_debug_theorem(dir: &str, theorem_name: &str, f: impl FnOnce(&crate::theorem::Theorem)) {
        let files = crate::project::DirectoryFiles::load(std::path::Path::new(dir)).unwrap();
        let project =
            crate::project::DirectoryProject::load(std::path::PathBuf::from(dir), &files).unwrap();
        let theorem = project.get_theorem(theorem_name).unwrap();
        let (theorem, _aux) = DebugTransform.transform_theorem(theorem).unwrap();
        f(&theorem);
    }

    /// Every `InlStmt`'s label, in traversal order (asserts contribute only their
    /// `Branch` label; the synthetic abort under an assert is skipped).
    fn collect_labels(block: &InlBlock, out: &mut Vec<Label>) {
        for stmt in &block.0 {
            match stmt {
                InlStmt::Assign { label, .. }
                | InlStmt::Sample { label, .. }
                | InlStmt::Unwrap { label, .. }
                | InlStmt::Return { label, .. }
                | InlStmt::Abort { label } => out.push(*label),
                InlStmt::Branch {
                    label,
                    then,
                    els,
                    is_assert,
                    ..
                } => {
                    out.push(*label);
                    if !is_assert {
                        collect_labels(then, out);
                        collect_labels(els, out);
                    }
                }
                InlStmt::Call { label, body, .. } => {
                    out.push(*label);
                    collect_labels(body, out);
                }
            }
        }
    }

    fn find_call(block: &InlBlock) -> Option<&InlStmt> {
        for stmt in &block.0 {
            match stmt {
                InlStmt::Call { .. } => return Some(stmt),
                InlStmt::Branch { then, els, .. } => {
                    if let Some(c) = find_call(then).or_else(|| find_call(els)) {
                        return Some(c);
                    }
                }
                _ => {}
            }
        }
        None
    }

    #[test]
    fn hello_world_labels_are_distinct_lines_and_sites_are_1to1() {
        with_debug_theorem("example-projects/hello-world", "Proof", |theorem| {
            let gi = theorem.find_game_instance("small_composition").unwrap();
            let inl = inline_oracle(gi, "UsefulOracle").unwrap();

            let n_lines = inl.listing.text.lines().count();
            let mut labels = Vec::new();
            collect_labels(&inl.body, &mut labels);

            // every label indexes a real, distinct line
            let mut sorted = labels.clone();
            sorted.sort_unstable();
            sorted.dedup();
            assert_eq!(
                sorted.len(),
                labels.len(),
                "labels are not distinct: {labels:?}"
            );
            for l in &labels {
                assert!(
                    *l >= 1 && *l <= n_lines,
                    "label {l} out of range 1..={n_lines}"
                );
            }

            // every site key is used by exactly one InlStmt (no asserts here)
            let site_keys: Vec<Label> = inl.listing.sites.keys().copied().collect();
            let mut label_set = labels.clone();
            label_set.sort_unstable();
            assert_eq!(
                site_keys, label_set,
                "sites keys and InlStmt labels disagree"
            );
        });
    }

    #[test]
    fn hello_world_medium_inlines_a_nested_call() {
        with_debug_theorem("example-projects/hello-world", "Proof", |theorem| {
            let gi = theorem.find_game_instance("medium_composition").unwrap();
            let inl = inline_oracle(gi, "UsefulOracle").unwrap();
            let call = find_call(&inl.body).expect("Fwd.UsefulOracle invokes Rand.UsefulOracle");
            match call {
                InlStmt::Call { frame, body, .. } => {
                    assert!(!body.0.is_empty());
                    assert_eq!(frame.pkg_inst_name, "rand");
                }
                _ => unreachable!(),
            }
        });
    }

    #[test]
    fn splitinvoke_call_body_is_nested_and_in_callee_instance() {
        with_debug_theorem(
            "test-projects/test-splitinvoke",
            "SplitInvokeProof",
            |theorem| {
                let gi = theorem.find_game_instance("game_split").unwrap();
                let inl = inline_oracle(gi, "Query").unwrap();
                let call = find_call(&inl.body).expect("Client.Query invokes Pair.GetPair");
                match call {
                    InlStmt::Call {
                        frame, body, bind, ..
                    } => {
                        assert!(
                            !body.0.is_empty(),
                            "callee body must be nested and non-empty"
                        );
                        assert_eq!(frame.pkg_inst_name, "pair");
                        assert!(bind.is_some());
                    }
                    _ => unreachable!(),
                }
            },
        );
    }

    #[test]
    fn loopunroll_has_no_loops_and_is_stable() {
        with_debug_theorem("test-projects/test-loopunroll", "Eq", |theorem| {
            let gi = theorem.find_game_instance("B").unwrap();
            let a = inline_oracle(gi, "Test").unwrap();
            let b = inline_oracle(gi, "Test").unwrap();
            // The IR has no loop construct at all, so "no loops" is structural;
            // what we check is that the unrolled body rendered stably.
            assert_eq!(
                a.listing.text, b.listing.text,
                "listing must be byte-stable"
            );
            assert!(a.listing.text.contains("result"));
        });
    }

    #[test]
    fn kem_dem_pkenc_has_assert_and_unwrap() {
        with_debug_theorem(
            "example-projects/kem-dem/kem-dem-cca-ssp",
            "kem_dem_cca_ssp",
            |theorem| {
                let gi = theorem.find_game_instance("Game_MON_CCA_PKE").unwrap();
                let inl = inline_oracle(gi, "PKENC").unwrap();

                let mut asserts = 0usize;
                let mut unwraps = 0usize;
                fn walk(block: &InlBlock, asserts: &mut usize, unwraps: &mut usize) {
                    for stmt in &block.0 {
                        match stmt {
                            InlStmt::Branch {
                                then,
                                els,
                                is_assert,
                                ..
                            } => {
                                if *is_assert {
                                    *asserts += 1;
                                    assert_eq!(els.0.len(), 1);
                                    assert!(matches!(els.0[0], InlStmt::Abort { .. }));
                                }
                                walk(then, asserts, unwraps);
                                walk(els, asserts, unwraps);
                            }
                            InlStmt::Unwrap { .. } => *unwraps += 1,
                            InlStmt::Call { body, .. } => walk(body, asserts, unwraps),
                            _ => {}
                        }
                    }
                }
                walk(&inl.body, &mut asserts, &mut unwraps);
                assert!(asserts >= 2, "PKENC has two `assert`s at the top");
                assert!(unwraps >= 1, "PKENC unwraps `pk` before invoking ENC");
            },
        );
    }

    #[test]
    fn snapshot_hello_world_small_useful_oracle() {
        with_debug_theorem("example-projects/hello-world", "Proof", |theorem| {
            let gi = theorem.find_game_instance("small_composition").unwrap();
            let inl = inline_oracle(gi, "UsefulOracle").unwrap();
            let expected = "\
// game instance: small_composition   (package instance: rand, package: Rand)
UsefulOracle() -> (Integer, Bits(n)) {
    rand.ctr <- (rand.ctr + 1);
    rand <-$ Bits(n) sample-name samplepoint;
    return (rand.ctr, rand);
}
";
            assert_eq!(inl.listing.text, expected);
        });
    }
}
