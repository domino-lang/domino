// SPDX-License-Identifier: MIT OR Apache-2.0

//! Lowering exported EasyCrypt code into the debugger IR
//! (`docs/stories/easycrypt/08-ec-ir-lowering.md`).
//!
//! [`inline_oracle_ec`] is the EasyCrypt counterpart of
//! [`crate::debug::ir::inline_oracle`]: it takes a game instance that has been
//! run through
//! [`crate::transforms::theorem_transforms::EasyCryptTransform`] — the exact
//! pipeline `domino easycrypt` exports — and produces an [`InlinedOracle`]
//! whose [`Listing::text`] is **EasyCrypt**: the router procedure with every
//! package procedure inlined in place, one row per line, rendered through
//! story 01's renderer. The executor, solver, claims and viewer run on it
//! unchanged.
//!
//! # Provenance: the IR says what the Domino game says
//!
//! The lowering walks the `easycryptify`-lowered **Domino** oracle bodies,
//! which the EasyCrypt writer translates statement for statement (story 16
//! §3.5), and emits each statement twice: the EasyCrypt line (through the
//! writer's own oracle translator, [`super::package::translate_oracle_stmt`])
//! and the IR node (from the Domino statement, alpha-renamed exactly as
//! [`crate::debug::ir`] does). Nothing is translated back from EasyCrypt.
//! So a module variable is a [`Place::State`] with the Domino instance and
//! field names, a local is a frame-keyed [`Place::Local`], and every
//! expression is the Domino expression — the mangled names exist only in
//! the text.
//!
//! # What is plumbing, and what it becomes
//!
//! `easycryptify`'s single-exit shape encodes control flow in three
//! variables that have no Domino counterpart. They never become places:
//!
//! - `ec_result <- Some e` is an [`InlStmt::Return`]. At the entry frame its
//!   value is `e`, exactly the Domino `return e` (a valueless `Some tt` is a
//!   valueless return). In an inlined callee it is the whole `Some e`, which
//!   is what the caller's `ec_r<N> : T option` receives.
//! - `ec_done <- true` on its own is an [`InlStmt::Abort`]: it is exactly
//!   where the Domino oracle aborted, but only where it survives.
//!   `easycryptify` deletes every write no `if (!ec_done)` guard can read
//!   (story 18); a path that aborted there runs to the end of its frame and
//!   aborts at the fall-through abort below instead. After an
//!   `ec_result <- Some e` it is unreachable in the IR (the `Return` already
//!   ended the frame) and is left unlabelled, as is `ec_done <- false` and
//!   `ec_result <- None`.
//! - an `if (!ec_done) { … }` guard is a *plumbing branch* (story 22):
//!   EasyCrypt shows a real `if` there and a proof has to step over it, so it
//!   is lowered to a labelled [`InlStmt::Branch`] marked
//!   [`Plumbing::DoneGuard`], with the literal `true` as its condition and no
//!   else side. Every path that set `ec_done` has already ended in a `Return`
//!   or `Abort`, so the guard holds on every path that reaches it; the
//!   literal says exactly that without inventing a place for the flag, and
//!   lockstep execution (story 23) is to take the branch on its side alone (`rcondt`). The
//!   `if (!(ec_rN = None))` call-result guards are marked
//!   [`Plumbing::CallResult`].
//! - a frame that falls off its end without returning has aborted
//!   (`ec_result` is still `None`). For an inlined callee that last line is
//!   `ec_r<N> <- ec_result;`; for the entry frame it is the router's
//!   `abort_flag <- true;` under `if (ec_result = None)`. Both are
//!   [`InlStmt::Abort`]s.
//! - the router's `abort_flag` is dropped from the IR entirely, and so is its
//!   `if (!abort_flag)` guard: the debugger already models "this oracle call
//!   happens".
//!   The router's prelude (`ec_result <- None; if (!abort_flag) { … }`) and
//!   tail (`if (ec_result = None) { abort_flag <- true; }`) stay out of the IR
//!   **by design**, since Domino has no abort flag to decide them with.
//!   Skeleton alignment and tactic generation (stories 26/27) know the
//!   router's shape because `game.rs` generates it, not because they match
//!   names in EasyCrypt's output. Anything after a terminal (guarded dead
//!   code, the router tail) is consumed by the proof's closing step:
//!   alignment treats a lockstep terminal as matching whatever EasyCrypt
//!   skeleton remains on that side.
//!
//! An `Unwrap` needs nothing of its own: since story 17 every `oget e` sits
//! under the `if (!(e = None))` guard `easycryptify` placed where the Domino
//! unwrap aborted, so the guard is the [`InlStmt::Branch`] that decides the
//! abort, and `x <- oget e` is a plain [`InlStmt::Assign`] (the executor
//! lowers the `Unwrap` to `maybe-get`, which is EasyCrypt's `oget`). This
//! is the one place the EasyCrypt IR has fewer forks than a Domino IR of the
//! same code would: `oget` has no failure branch in EasyCrypt.
//!
//! # Layout
//!
//! The listing is a complete EasyCrypt procedure: the router's signature,
//! one `var` line per local of every inlined frame, then the body. Frame
//! locals that would clash with a name already in the listing are renamed
//! `<name>_<frame id>`. An inlined call is laid out as
//!
//! ```text
//! (* ec_r1 <@ Pkg_Inst_KEM.d_ENCAPS(); *)   <- the Call's label; opens the frame
//!   pk_1 <- oget Pkg_Inst_MOD.pk;           <- argument bindings
//!   …callee body…
//! ec_r1 <- ec_result_1;                     <- closes the frame; the callee's fall-through Abort
//! ```
//!
//! so `frame_lines` is `(call line, closing line)`. The listing is valid
//! EasyCrypt: wrapped in a module next to the exported `Comp_*.ec` it
//! compiles (see the tests).

use std::collections::{BTreeMap, BTreeSet};

use miette::SourceSpan;

use crate::debug::ir::{
    place_from_pattern, rewrite_expr, FrameInfo, FrameScope, InlBlock, InlStmt, InlineError,
    InlinedOracle, Label, Listing, Plumbing, SiteInfo, SiteKind, MAX_INLINE_DEPTH,
};
use crate::expressions::{Expression, ExpressionKind};
use crate::identifier::{pkg_ident::PackageIdentifier, Identifier};
use crate::package::{Composition, Edge, OracleDef};
use crate::statement::{
    Assignment, AssignmentRhs, CodeBlock, IfThenElse, InvokeOracle, Pattern, Statement,
};
use crate::theorem::GameInstance;
use crate::transforms::easycryptify::{EC_DONE, EC_INVOKE_PREFIX, EC_RESULT};
use crate::types::{Type, TypeKind};

use super::ast::{EcBinop, EcExpr, EcLvalue, EcStmt, EcType, EcUnop};
use super::game::{instance_module_names, router_module_and_flag};
use super::names::{NameKind, Names};
use super::package::{
    ident_raw_name_and_type, translate_oracle_expr, translate_oracle_stmt, var_spelling,
    OracleNaming, SampleTemps,
};
use super::render::{
    render_block_close, render_else_open, render_expr, render_if_open, render_local_decl,
    render_proc_open, render_return, render_stmt,
};
use super::types::translate_type;
use super::EcExportError;

/// Inline `oracle_name` (an *exported* name) of `game_inst` as EasyCrypt.
/// `game_inst` must already have been run through
/// [`crate::transforms::theorem_transforms::EasyCryptTransform`].
///
/// [`InlinedOracle::return_type`] is the Domino return type `T`, not the
/// exported `T option`: an entry-frame [`InlStmt::Return`] carries a `T`,
/// and `None` is an [`InlStmt::Abort`].
pub fn inline_oracle_ec(
    game_inst: &GameInstance,
    oracle_name: &str,
) -> Result<InlinedOracle, EcExportError> {
    // The `var` block comes first in an EasyCrypt procedure, but which locals
    // it holds (and how clashing ones are renamed) is only known once every
    // frame has been inlined. The lowering is deterministic, so a first pass
    // collects the declarations and a second one lays the listing out with
    // them in place.
    let (_, decls) = lower_oracle(game_inst, oracle_name, None)?;
    let (inlined, _) = lower_oracle(game_inst, oracle_name, Some(&decls))?;
    Ok(inlined)
}

/// A `var` line: name, type, initializer.
type Decl = (String, EcType, Option<EcExpr>);

fn lower_oracle(
    game_inst: &GameInstance,
    oracle_name: &str,
    decls: Option<&[Decl]>,
) -> Result<(InlinedOracle, Vec<Decl>), EcExportError> {
    let comp = game_inst.game();
    let export = comp
        .exports
        .iter()
        .find(|export| export.name() == oracle_name)
        .ok_or_else(|| InlineError::OracleNotExported {
            oracle: oracle_name.to_string(),
            game_inst: game_inst.name().to_string(),
        })?;
    let entry_idx = export.to();
    let entry_inst = &comp.pkgs[entry_idx];
    let odef = entry_inst
        .pkg
        .oracles
        .iter()
        .find(|odef| odef.sig.name == export.sig().name)
        .ok_or_else(|| InlineError::CalleeNotFound {
            oracle: export.sig().name.clone(),
            pkg_inst: entry_inst.name.clone(),
        })?;
    let span = odef.file_pos;

    let TypeKind::Maybe(domino_ret) = export.sig().ty.kind() else {
        unreachable!("easycryptify makes every exported signature Maybe-typed")
    };
    let domino_ret = (**domino_ret).clone();
    let ret_ec = translate_type(&export.sig().ty, span)?;
    let ret_inner_ec = translate_type(&domino_ret, span)?;

    let (router_module, abort_flag) = router_module_and_flag(comp)?;
    let mut lw = Lowerer {
        comp,
        inst_modules: instance_module_names(comp)?,
        next_frame_id: 0,
        text: String::new(),
        line: 0,
        sites: BTreeMap::new(),
        locals: LocalNames::default(),
        temps: SampleTemps::default(),
    };

    let entry = lw.new_frame(entry_idx, odef, true)?;
    // The router's `var ec_result : T option <- None;` and the entry
    // procedure's own `ec_result` are one variable here: the router assigns
    // the procedure's result to it unchanged, so merging them is exact.
    let ec_result_name = lw.local_name(&entry, EC_RESULT, true, &export.sig().ty)?;
    lw.locals
        .set_init(&ec_result_name, EcExpr::None_(ret_inner_ec));

    let args_ec: Vec<(String, EcType)> = odef
        .sig
        .args
        .iter()
        .map(|(name, ty)| {
            Ok((
                lw.local_name(&entry, name, false, ty)?,
                translate_type(ty, span)?,
            ))
        })
        .collect::<Result<_, EcExportError>>()?;
    let router_proc = Names::new().mangle(NameKind::Proc, export.name())?;

    lw.emit_plain_line(&render_stmt(
        &EcStmt::Comment(format!(
            "game instance: {}   (package instance: {}, package: {})",
            game_inst.name(),
            entry_inst.name,
            entry_inst.pkg.name,
        )),
        0,
    ));
    lw.emit_plain_line(&render_proc_open(&router_proc, &args_ec, &ret_ec, 0));
    for (name, ty, init) in decls.unwrap_or_default() {
        lw.emit_plain_line(&render_local_decl(name, ty, init.as_ref(), 1));
    }

    let abort_flag_path = EcExpr::Qualified {
        path: vec![router_module, abort_flag],
        mem: None,
    };
    lw.emit_plain_line(&render_if_open(
        &EcExpr::Unop {
            op: EcUnop::Not,
            arg: Box::new(abort_flag_path.clone()),
        },
        1,
    ));
    let entry_call = EcStmt::Call {
        lhs: Some(EcLvalue::Var(ec_result_name.clone())),
        module: lw.inst_modules[entry_idx].clone(),
        proc: Names::new().mangle(NameKind::Proc, &odef.sig.name)?,
        args: args_ec
            .iter()
            .map(|(n, _)| EcExpr::Var(n.clone()))
            .collect(),
    };
    lw.emit_plain_line(&render_stmt(
        &EcStmt::Comment(render_stmt(&entry_call, 0)),
        2,
    ));

    let mut body = lw.lower_frame_body(&entry, 0, 2)?;

    // The router's `ec_result = None` branch: the entry procedure fell off
    // its end without returning, i.e. it aborted. Its flag assignment is
    // that abort.
    let ec_result_var = EcExpr::Var(ec_result_name);
    lw.emit_plain_line(&render_if_open(
        &EcExpr::Binop {
            op: EcBinop::Eq,
            lhs: Box::new(ec_result_var.clone()),
            rhs: Box::new(EcExpr::None_(translate_type(&domino_ret, span)?)),
        },
        2,
    ));
    let abort_line = render_stmt(
        &EcStmt::Assign {
            lhs: EcLvalue::Var(render_expr(&abort_flag_path)),
            rhs: EcExpr::Bool(true),
        },
        3,
    );
    let label = lw.emit_site(&abort_line, SiteKind::Abort, span, &entry, 0);
    body.0.push(InlStmt::Abort { label });
    lw.emit_plain_line(&render_block_close(2));
    lw.emit_plain_line(&render_block_close(1));
    lw.emit_plain_line(&render_return(&ec_result_var, 1));
    lw.emit_plain_line(&render_block_close(0));

    let mut all_decls = lw.locals.decls;
    all_decls.extend(lw.temps.decls.into_iter().map(|(n, ty)| (n, ty, None)));

    Ok((
        InlinedOracle {
            game_inst_name: game_inst.name().to_string(),
            oracle_name: export.name().to_string(),
            entry_pkg_inst: entry_inst.name.clone(),
            args: export.sig().args.clone(),
            return_type: domino_ret,
            body,
            listing: Listing {
                text: lw.text,
                sites: lw.sites,
            },
        },
        all_decls,
    ))
}

/// One inlined procedure.
struct EcFrame<'c> {
    frame_id: usize,
    pkg_idx: usize,
    pkg_inst_name: String,
    oracle: &'c OracleDef,
    is_entry: bool,
}

impl EcFrame<'_> {
    fn scope(&self) -> FrameScope<'_> {
        FrameScope {
            pkg_inst_name: &self.pkg_inst_name,
            frame_id: self.frame_id,
        }
    }
}

/// The EasyCrypt names of every frame's locals, unique across the listing,
/// and their `var` declarations in first-claimed order.
#[derive(Default)]
struct LocalNames {
    by_frame: BTreeMap<(usize, String), String>,
    taken: BTreeSet<String>,
    decls: Vec<Decl>,
}

impl LocalNames {
    /// The listing name of frame `frame_id`'s local `raw`, whose module
    /// spelling is `base`. The first frame to use a spelling keeps it; a
    /// later frame's clashing local becomes `<base>_<frame id>`. `declare`
    /// is false only for the listing procedure's own parameters, which get
    /// no `var` line.
    fn resolve(
        &mut self,
        frame_id: usize,
        raw: &str,
        base: String,
        ty: EcType,
        declare: bool,
    ) -> String {
        if let Some(name) = self.by_frame.get(&(frame_id, raw.to_string())) {
            return name.clone();
        }
        let mut name = base.clone();
        if self.taken.contains(&name) {
            name = format!("{base}_{frame_id}");
            while self.taken.contains(&name) {
                name.push('_');
            }
        }
        self.taken.insert(name.clone());
        self.by_frame
            .insert((frame_id, raw.to_string()), name.clone());
        if declare {
            self.decls.push((name.clone(), ty, None));
        }
        name
    }

    fn set_init(&mut self, name: &str, init: EcExpr) {
        if let Some(decl) = self.decls.iter_mut().find(|(n, _, _)| n == name) {
            decl.2 = Some(init);
        }
    }
}

/// [`OracleNaming`] for one inlined frame: state (and a parameter that is a
/// module variable) is qualified with its instance module; locals get their
/// listing-unique name.
struct FrameNaming<'l> {
    locals: &'l mut LocalNames,
    inst_module: &'l str,
    frame_id: usize,
    span: SourceSpan,
    /// Mangling is a pure function of the name; the package's own module
    /// has already been checked for collisions at export.
    names: Names,
}

impl<'l> FrameNaming<'l> {
    fn new(locals: &'l mut LocalNames, inst_module: &'l str, frame: &EcFrame<'_>) -> Self {
        FrameNaming {
            locals,
            inst_module,
            frame_id: frame.frame_id,
            span: frame.oracle.file_pos,
            names: Names::new(),
        }
    }

    fn local(&mut self, raw: &str, generated: bool, ty: &Type) -> Result<String, EcExportError> {
        self.claim(raw, generated, ty, true)
    }

    fn claim(
        &mut self,
        raw: &str,
        generated: bool,
        ty: &Type,
        declare: bool,
    ) -> Result<String, EcExportError> {
        let base = var_spelling(&mut self.names, raw, generated)?;
        let ty = translate_type(ty, self.span)?;
        Ok(self.locals.resolve(self.frame_id, raw, base, ty, declare))
    }

    fn module_var(&mut self, id: &Identifier) -> Result<EcExpr, EcExportError> {
        let (raw, _) = ident_raw_name_and_type(id);
        Ok(EcExpr::Qualified {
            path: vec![
                self.inst_module.to_string(),
                var_spelling(&mut self.names, &raw, false)?,
            ],
            mem: None,
        })
    }
}

impl OracleNaming for FrameNaming<'_> {
    fn expr(&mut self, id: &Identifier) -> Result<EcExpr, EcExportError> {
        match id {
            Identifier::PackageIdentifier(
                PackageIdentifier::State(_) | PackageIdentifier::Const(_),
            ) => self.module_var(id),
            Identifier::Generated(name, ty) => Ok(EcExpr::Var(self.local(name, true, ty)?)),
            Identifier::PackageIdentifier(PackageIdentifier::Local(l)) => {
                Ok(EcExpr::Var(self.local(&l.name, false, &l.ty)?))
            }
            Identifier::PackageIdentifier(PackageIdentifier::OracleArg(a)) => {
                Ok(EcExpr::Var(self.local(&a.name, false, &a.ty)?))
            }
            other => unreachable!(
                "identifier kind not expected in easycrypt-exported oracle code: {other:?}"
            ),
        }
    }

    fn target(&mut self, id: &Identifier) -> Result<String, EcExportError> {
        // A qualified module variable is a legal EasyCrypt assignment
        // target; its path is spelled by the renderer.
        Ok(render_expr(&self.expr(id)?))
    }
}

/// The `easycryptify` plumbing statements (module doc) a statement may be.
enum Shape<'s> {
    /// `ec_result <- None`, `ec_done <- false`: unlabelled.
    Plumbing,
    /// `ec_result <- v`, `v = Some e`.
    SetResult(&'s Expression),
    /// `ec_done <- true`.
    SetDone,
    /// `if (!ec_done) { … }`: a labelled [`Plumbing::DoneGuard`] branch.
    DoneGuard(&'s IfThenElse),
    Other,
}

fn is_generated(id: &Identifier, name: &str) -> bool {
    matches!(id, Identifier::Generated(n, _) if n == name)
}

fn shape(stmt: &Statement) -> Shape<'_> {
    match stmt {
        Statement::Assignment(
            Assignment {
                pattern: Pattern::Ident(id),
                rhs: AssignmentRhs::Expression(value),
            },
            _,
        ) if is_generated(id, EC_RESULT) => match value.kind() {
            ExpressionKind::None(_) => Shape::Plumbing,
            _ => Shape::SetResult(value),
        },
        Statement::Assignment(
            Assignment {
                pattern: Pattern::Ident(id),
                rhs: AssignmentRhs::Expression(value),
            },
            _,
        ) if is_generated(id, EC_DONE) => match value.kind() {
            ExpressionKind::BooleanLiteral(b) if b == "true" => Shape::SetDone,
            _ => Shape::Plumbing,
        },
        Statement::IfThenElse(ite)
            if ite.else_block.0.is_empty()
                && matches!(ite.cond.kind(), ExpressionKind::Not(inner)
                    if matches!(inner.kind(), ExpressionKind::Identifier(id) if is_generated(id, EC_DONE))) =>
        {
            Shape::DoneGuard(ite)
        }
        _ => Shape::Other,
    }
}

/// `!(ec_rN = None)`: the guard `easycryptify` puts on the use of an inlined
/// call's result.
fn call_result_guard(cond: &Expression) -> bool {
    let ExpressionKind::Not(inner) = cond.kind() else {
        return false;
    };
    matches!(inner.kind(), ExpressionKind::Equals(es)
    if es.len() == 2
        && matches!(es[1].kind(), ExpressionKind::None(_))
        && matches!(es[0].kind(), ExpressionKind::Identifier(Identifier::Generated(n, _))
            if n.strip_prefix(EC_INVOKE_PREFIX).is_some_and(|k| {
                !k.is_empty() && k.bytes().all(|b| b.is_ascii_digit())
            })))
}

fn stmt_span(stmt: &Statement) -> SourceSpan {
    match stmt {
        Statement::Abort(span)
        | Statement::Return(_, span)
        | Statement::Assignment(_, span)
        | Statement::For(_, _, _, _, span) => *span,
        Statement::InvokeOracle(InvokeOracle { file_pos, .. }) => *file_pos,
        Statement::IfThenElse(ite) => ite.full_span,
    }
}

struct Lowerer<'c> {
    comp: &'c Composition,
    /// `Pkg_Inst_<inst>`, by index into `comp.pkgs`.
    inst_modules: Vec<String>,
    next_frame_id: usize,
    text: String,
    line: Label,
    sites: BTreeMap<Label, SiteInfo>,
    locals: LocalNames,
    temps: SampleTemps,
}

impl<'c> Lowerer<'c> {
    /// Allocates a frame and claims listing names for its arguments and
    /// every local its body assigns, in that order — so a caller's names
    /// are always settled before a callee's, and only the callee's are ever
    /// renamed.
    fn new_frame(
        &mut self,
        pkg_idx: usize,
        oracle: &'c OracleDef,
        is_entry: bool,
    ) -> Result<EcFrame<'c>, EcExportError> {
        let frame = EcFrame {
            frame_id: self.next_frame_id,
            pkg_idx,
            pkg_inst_name: self.comp.pkgs[pkg_idx].name.clone(),
            oracle,
            is_entry,
        };
        self.next_frame_id += 1;

        let mut naming = FrameNaming::new(&mut self.locals, &self.inst_modules[pkg_idx], &frame);
        // The entry procedure's arguments are the listing procedure's own
        // parameters; an inlined callee's are ordinary locals, bound on entry.
        for (name, ty) in &oracle.sig.args {
            naming.claim(name, false, ty, !is_entry)?;
        }
        claim_block_locals(&oracle.code, &mut naming)?;
        Ok(frame)
    }

    fn local_name(
        &mut self,
        frame: &EcFrame<'_>,
        raw: &str,
        generated: bool,
        ty: &Type,
    ) -> Result<String, EcExportError> {
        FrameNaming::new(&mut self.locals, &self.inst_modules[frame.pkg_idx], frame)
            .local(raw, generated, ty)
    }

    fn translate_expr(
        &mut self,
        frame: &EcFrame<'_>,
        expr: &Expression,
        span: SourceSpan,
    ) -> Result<EcExpr, EcExportError> {
        let mut naming =
            FrameNaming::new(&mut self.locals, &self.inst_modules[frame.pkg_idx], frame);
        translate_oracle_expr(&mut naming, expr, span)
    }

    fn translate_stmt(
        &mut self,
        frame: &EcFrame<'_>,
        stmt: &Statement,
    ) -> Result<Vec<EcStmt>, EcExportError> {
        let mut naming =
            FrameNaming::new(&mut self.locals, &self.inst_modules[frame.pkg_idx], frame);
        translate_oracle_stmt(&mut naming, &mut self.temps, stmt)
    }

    fn alloc_line(&mut self, content: &str) -> Label {
        self.text.push_str(content);
        self.text.push('\n');
        self.line += 1;
        self.line
    }

    /// Emits already-rendered text (possibly several lines) with no label.
    fn emit_plain_line(&mut self, rendered: &str) {
        for line in rendered.lines() {
            self.alloc_line(line);
        }
    }

    /// Emits one rendered line as a labelled site and returns its label.
    fn emit_site(
        &mut self,
        rendered: &str,
        kind: SiteKind,
        span: SourceSpan,
        frame: &EcFrame<'_>,
        depth: usize,
    ) -> Label {
        debug_assert!(!rendered.contains('\n'), "a site is one line: {rendered}");
        let label = self.alloc_line(rendered);
        self.sites.insert(
            label,
            SiteInfo {
                kind,
                line: rendered.trim().to_string(),
                span,
                pkg_inst_name: frame.pkg_inst_name.clone(),
                oracle_name: frame.oracle.sig.name.clone(),
                depth,
            },
        );
        label
    }

    /// Translates `stmt` and emits it unlabelled.
    fn emit_plain(
        &mut self,
        stmt: &Statement,
        frame: &EcFrame<'_>,
        level: usize,
    ) -> Result<(), EcExportError> {
        for ec in self.translate_stmt(frame, stmt)? {
            self.emit_plain_line(&render_stmt(&ec, level));
        }
        Ok(())
    }

    /// Translates `stmt` and emits it with its first line as the labelled
    /// site. Only a sample into a table entry has a second line (the write of
    /// its `ec_s<N>` temporary), which stays unlabelled.
    fn emit_labelled(
        &mut self,
        stmt: &Statement,
        kind: SiteKind,
        frame: &EcFrame<'_>,
        depth: usize,
        level: usize,
    ) -> Result<Label, EcExportError> {
        let ecs = self.translate_stmt(frame, stmt)?;
        let (first, rest) = ecs
            .split_first()
            .expect("every lowered statement translates to at least one EasyCrypt statement");
        let label = self.emit_site(
            &render_stmt(first, level),
            kind,
            stmt_span(stmt),
            frame,
            depth,
        );
        for ec in rest {
            self.emit_plain_line(&render_stmt(ec, level));
        }
        Ok(label)
    }

    /// A frame's body, less the single trailing `return ec_result` that
    /// `easycryptify` ends it with — the caller lays that line out, since
    /// how control leaves the frame depends on who called it.
    fn lower_frame_body(
        &mut self,
        frame: &EcFrame<'c>,
        depth: usize,
        level: usize,
    ) -> Result<InlBlock, EcExportError> {
        let code: &'c CodeBlock = &frame.oracle.code;
        let Some((Statement::Return(Some(_), _), body)) = code.0.split_last() else {
            unreachable!(
                "easycryptify ends every oracle body in a single `return ec_result` \
                 (oracle `{}`)",
                frame.oracle.sig.name
            )
        };
        self.lower_block(body, frame, depth, level)
    }

    fn lower_block(
        &mut self,
        stmts: &'c [Statement],
        frame: &EcFrame<'c>,
        depth: usize,
        level: usize,
    ) -> Result<InlBlock, EcExportError> {
        let mut out = Vec::new();
        // Set once this block has ended in a `Return`/`Abort`: whatever
        // follows (only ever the `ec_done <- true` after an `ec_result`
        // assignment) is unreachable in the IR.
        let mut ended = false;
        for stmt in stmts {
            if ended {
                self.emit_plain(stmt, frame, level)?;
                continue;
            }
            match shape(stmt) {
                Shape::Plumbing => self.emit_plain(stmt, frame, level)?,
                Shape::SetDone => {
                    let label = self.emit_labelled(stmt, SiteKind::Abort, frame, depth, level)?;
                    out.push(InlStmt::Abort { label });
                    ended = true;
                }
                Shape::SetResult(rhs) => {
                    let value = if frame.is_entry {
                        match rhs.kind() {
                            ExpressionKind::Some(inner) => match inner.kind() {
                                ExpressionKind::Bot => None,
                                _ => Some(rewrite_expr(inner, frame.scope())),
                            },
                            _ => unreachable!(
                                "easycryptify only ever assigns `Some(v)` to ec_result: {rhs:?}"
                            ),
                        }
                    } else {
                        Some(rewrite_expr(rhs, frame.scope()))
                    };
                    let label = self.emit_labelled(stmt, SiteKind::Return, frame, depth, level)?;
                    out.push(InlStmt::Return { label, value });
                    ended = true;
                }
                Shape::DoneGuard(ite) => {
                    out.push(self.lower_if(
                        ite,
                        Expression::boolean(true),
                        Some(Plumbing::DoneGuard),
                        frame,
                        depth,
                        level,
                    )?);
                }
                Shape::Other => out.push(self.lower_stmt(stmt, frame, depth, level)?),
            }
        }
        Ok(InlBlock(out))
    }

    fn lower_stmt(
        &mut self,
        stmt: &'c Statement,
        frame: &EcFrame<'c>,
        depth: usize,
        level: usize,
    ) -> Result<InlStmt, EcExportError> {
        match stmt {
            Statement::Assignment(Assignment { pattern, rhs }, span) => match rhs {
                AssignmentRhs::Expression(e) => {
                    let target = place_from_pattern(pattern, frame.scope());
                    let label = self.emit_labelled(stmt, SiteKind::Assign, frame, depth, level)?;
                    Ok(InlStmt::Assign {
                        label,
                        target,
                        rhs: rewrite_expr(e, frame.scope()),
                    })
                }
                AssignmentRhs::Sample {
                    ty,
                    sample_name,
                    sample_id,
                } => {
                    let target = place_from_pattern(pattern, frame.scope());
                    let label = self.emit_labelled(stmt, SiteKind::Sample, frame, depth, level)?;
                    Ok(InlStmt::Sample {
                        label,
                        target,
                        sample_id: sample_id
                            .expect("samplify assigns a sample_id to every sampling point"),
                        ty: ty.clone(),
                        sample_name: sample_name.clone().unwrap_or_default(),
                    })
                }
                AssignmentRhs::Invoke {
                    oracle_name,
                    args,
                    edge,
                    ..
                } => self.lower_call(
                    Some(pattern),
                    oracle_name,
                    args,
                    edge.as_ref(),
                    *span,
                    frame,
                    depth,
                    level,
                ),
            },

            // `easycryptify` binds even a bare invoke, to check its abort;
            // kept for completeness.
            Statement::InvokeOracle(InvokeOracle {
                oracle_name,
                args,
                edge,
                file_pos,
            }) => self.lower_call(
                None,
                oracle_name,
                args,
                edge.as_ref(),
                *file_pos,
                frame,
                depth,
                level,
            ),

            Statement::IfThenElse(ite) => {
                let plumbing = call_result_guard(&ite.cond).then_some(Plumbing::CallResult);
                let cond_ir = rewrite_expr(&ite.cond, frame.scope());
                self.lower_if(ite, cond_ir, plumbing, frame, depth, level)
            }

            Statement::Abort(_) => unreachable!("easycryptify leaves no `abort` in an oracle body"),
            Statement::Return(..) => unreachable!(
                "easycryptify leaves a single `return`, as the last statement of the body"
            ),
            Statement::For(..) => unreachable!("easycryptify rejects every surviving `for` loop"),
        }
    }

    /// A labelled `if`. `cond_ir` is the condition the IR decides on: the
    /// statement's own, except for a done guard (see [`Plumbing::DoneGuard`]).
    fn lower_if(
        &mut self,
        ite: &'c IfThenElse,
        cond_ir: Expression,
        plumbing: Option<Plumbing>,
        frame: &EcFrame<'c>,
        depth: usize,
        level: usize,
    ) -> Result<InlStmt, EcExportError> {
        let cond = self.translate_expr(frame, &ite.cond, ite.full_span)?;
        let label = self.emit_site(
            &render_if_open(&cond, level),
            SiteKind::Branch,
            ite.full_span,
            frame,
            depth,
        );
        let then_first = label + 1;
        let then = self.lower_block(&ite.then_block.0, frame, depth, level + 1)?;
        let (then_close, els, else_lines) = if ite.else_block.0.is_empty() {
            let close = self.alloc_line(&render_block_close(level));
            (close, InlBlock(vec![]), None)
        } else {
            let close = self.alloc_line(&render_else_open(level));
            let els = self.lower_block(&ite.else_block.0, frame, depth, level + 1)?;
            let els_close = self.alloc_line(&render_block_close(level));
            (close, els, Some((close + 1, els_close)))
        };
        Ok(InlStmt::Branch {
            label,
            cond: cond_ir,
            then,
            els,
            is_assert: false,
            then_lines: Some((then_first, then_close)),
            else_lines,
            plumbing,
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_call(
        &mut self,
        bind_pattern: Option<&Pattern>,
        oracle_name: &str,
        args: &[Expression],
        edge: Option<&Edge>,
        span: SourceSpan,
        caller: &EcFrame<'c>,
        depth: usize,
        level: usize,
    ) -> Result<InlStmt, EcExportError> {
        let edge = edge.ok_or_else(|| InlineError::UnresolvedEdge {
            oracle: oracle_name.to_string(),
            pkg_inst: caller.pkg_inst_name.clone(),
        })?;
        let comp = self.comp;
        let target_idx = edge.to();
        let target_inst = &comp.pkgs[target_idx];
        let target_sig = edge.sig();
        let target_odef = target_inst
            .pkg
            .oracles
            .iter()
            .find(|odef| odef.sig.name == target_sig.name)
            .ok_or_else(|| InlineError::CalleeNotFound {
                oracle: target_sig.name.clone(),
                pkg_inst: target_inst.name.clone(),
            })?;
        if depth + 1 > MAX_INLINE_DEPTH {
            return Err(InlineError::MaxDepthExceeded {
                oracle: oracle_name.to_string(),
                max: MAX_INLINE_DEPTH,
            }
            .into());
        }

        // Everything on the caller's side is translated before the callee
        // frame claims its names.
        let bind = bind_pattern.map(|p| place_from_pattern(p, caller.scope()));
        let lhs = match bind_pattern {
            None => None,
            Some(Pattern::Ident(id)) => {
                let mut naming =
                    FrameNaming::new(&mut self.locals, &self.inst_modules[caller.pkg_idx], caller);
                Some(EcLvalue::Var(naming.target(id)?))
            }
            Some(_) => unreachable!("easycryptify binds every invoke to an `ec_r<N>` temporary"),
        };
        let args_ec = args
            .iter()
            .map(|a| self.translate_expr(caller, a, span))
            .collect::<Result<Vec<_>, _>>()?;

        let callee = self.new_frame(target_idx, target_odef, false)?;

        let call = EcStmt::Call {
            lhs: lhs.clone(),
            module: self.inst_modules[target_idx].clone(),
            proc: Names::new().mangle(NameKind::Proc, &target_sig.name)?,
            args: args_ec.clone(),
        };
        let label = self.emit_site(
            &render_stmt(&EcStmt::Comment(render_stmt(&call, 0)), level),
            SiteKind::Call,
            span,
            caller,
            depth,
        );

        let mut arg_bindings = Vec::with_capacity(target_sig.args.len());
        let mut arg_lines: Option<(Label, Label)> = None;
        for (((param, ty), arg), arg_ec) in target_sig.args.iter().zip(args).zip(args_ec) {
            let param_name = self.local_name(&callee, param, false, ty)?;
            let arg_label = self.alloc_line(&render_stmt(
                &EcStmt::Assign {
                    lhs: EcLvalue::Var(param_name),
                    rhs: arg_ec,
                },
                level + 1,
            ));
            arg_lines = Some(match arg_lines {
                None => (arg_label, arg_label),
                Some((first, _)) => (first, arg_label),
            });
            arg_bindings.push((
                callee.scope().key(param),
                ty.clone(),
                // argument expressions live in the *caller's* namespace
                rewrite_expr(arg, caller.scope()),
            ));
        }

        let mut body = self.lower_frame_body(&callee, depth + 1, level + 1)?;

        // The callee's `return ec_result`, inlined: its result lands in the
        // caller's `ec_r<N>`. Reached only when the callee never assigned
        // `ec_result`, i.e. it aborted.
        let callee_result = self.local_name(&callee, EC_RESULT, true, &target_sig.ty)?;
        let close = match lhs {
            Some(lhs) => EcStmt::Assign {
                lhs,
                rhs: EcExpr::Var(callee_result),
            },
            None => EcStmt::Comment(format!("{callee_result} is discarded")),
        };
        let close_label = self.emit_site(
            &render_stmt(&close, level),
            SiteKind::Abort,
            target_odef.file_pos,
            &callee,
            depth + 1,
        );
        body.0.push(InlStmt::Abort { label: close_label });

        Ok(InlStmt::Call {
            label,
            frame: FrameInfo {
                frame_id: callee.frame_id,
                pkg_inst_name: callee.pkg_inst_name.clone(),
                oracle_name: target_sig.name.clone(),
                arg_bindings,
                return_type: target_sig.ty.clone(),
            },
            bind,
            body,
            frame_lines: (label, close_label),
            arg_lines,
        })
    }
}

/// Claims a listing name for every local `code` assigns, in order.
fn claim_block_locals(code: &CodeBlock, naming: &mut FrameNaming<'_>) -> Result<(), EcExportError> {
    for stmt in &code.0 {
        match stmt {
            Statement::Assignment(Assignment { pattern, .. }, _) => {
                let ids: &[Identifier] = match pattern {
                    Pattern::Ident(id) => std::slice::from_ref(id),
                    Pattern::Tuple(ids) => ids,
                    // The table itself is state, or a local its own
                    // `<gen> <- empty` assignment already claimed.
                    Pattern::Table { .. } => &[],
                };
                for id in ids {
                    match id {
                        Identifier::PackageIdentifier(PackageIdentifier::State(_)) => {}
                        _ => {
                            naming.expr(id)?;
                        }
                    }
                }
            }
            Statement::IfThenElse(ite) => {
                claim_block_locals(&ite.then_block, naming)?;
                claim_block_locals(&ite.else_block, naming)?;
            }
            Statement::For(_, _, _, body, _) => claim_block_locals(body, naming)?,
            Statement::Abort(_) | Statement::Return(..) | Statement::InvokeOracle(_) => {}
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests;
