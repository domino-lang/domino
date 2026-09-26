// SPDX-License-Identifier: MIT OR Apache-2.0

//! The artifacts of a lockstep run (story 23): the trace (schema 10), the summary (the joint
//! tree as text, in the story-17 style), the concise stdout report, the viewer
//! ([`crate::debug::lockstep_viewer`]), and the `smt/` files of the joint paths. On the
//! EasyCrypt listing they are `trace.json`, `summary.txt`, `index.html` and `smt/`; on the Domino
//! listing each carries the strategy (`lockstep_trace.json`, …), so they can share a directory
//! with the sequential debugger's (story 19, [`crate::debug::layout`]).
//!
//! Like the sequential artifacts, `trace.json` and `summary.txt` are
//! byte-deterministic for an unchanged project: the absolute output directory
//! and the wall-clock time are kept out of them.

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::path::{Path, PathBuf};

use serde_derive::Serialize;

use crate::debug::driver::{describe_unreachable, GoalBlock, StopReason, Verdict};
use crate::debug::layout::Layout;
use crate::debug::exec::TerminalPath;
use crate::debug::lockstep::{
    ChildOutcome, JointNode, JointTree, LockstepOutcome, PairRecord, SideStep, SideView, StuckPoint,
};
use crate::debug::lockstep_viewer;
use crate::debug::lockstep_run::{LockstepMeta, LockstepRun, LockstepSummary};
use crate::debug::report::format_elapsed;
use crate::debug::smtout::SmtOut;

/// What `trace.json` holds: the run's identity and listings, then the joint
/// tree, the joint paths, the stuck points and the counts.
#[derive(Serialize)]
pub struct LockstepTrace<'a> {
    #[serde(flatten)]
    pub meta: &'a LockstepMeta,
    pub tree: &'a JointTree,
    pub pairs: &'a [PairRecord],
    pub stuck: &'a [StuckPoint],
    pub summary: &'a LockstepSummary,
    pub stop_reason: StopReason,
}

/// Write `trace.json`, `summary.txt` and the `index.html` viewer for the run so
/// far. Called at most twice a second while the run is in progress (`live`), so
/// an interrupted run leaves a usable partial trace and the page can follow the
/// run, and once at the end (`live` false: the page then carries no refresh
/// tag).
pub fn flush(
    meta: &LockstepMeta,
    outcome: &LockstepOutcome,
    summary: &LockstepSummary,
    out_dir: &Path,
    live: bool,
) -> std::io::Result<()> {
    let trace = LockstepTrace {
        meta,
        tree: &outcome.tree,
        pairs: &outcome.pairs,
        stuck: &outcome.stuck,
        summary,
        stop_reason: outcome.stop_reason,
    };
    let mut json = serde_json::to_string_pretty(&trace).map_err(std::io::Error::other)?;
    json.push('\n');
    std::fs::write(out_dir.join(meta.layout.trace()), &json)?;
    std::fs::write(
        out_dir.join(meta.layout.summary()),
        render_tree(meta, outcome, summary),
    )?;
    let compact = serde_json::to_string(&trace).map_err(std::io::Error::other)?;
    std::fs::write(
        out_dir.join(meta.layout.viewer()),
        lockstep_viewer::render_html(
            &compact,
            &lockstep_viewer::stuck_rollups(outcome, &meta.claims),
            live,
        ),
    )?;
    Ok(())
}

// ---------------------------------------------------------------------------
// summary.txt
// ---------------------------------------------------------------------------

/// The joint tree as text: one block per node, its children beneath it.
pub fn render_tree(
    meta: &LockstepMeta,
    outcome: &LockstepOutcome,
    summary: &LockstepSummary,
) -> String {
    let mut out = String::new();
    let _ = writeln!(
        out,
        "theorem {}, proofstep {} ({} == {})",
        meta.theorem, meta.proofstep, meta.left_game, meta.right_game
    );
    let _ = writeln!(
        out,
        "oracle {}, lockstep execution on the {} listing",
        meta.oracle,
        listing_name(meta)
    );
    let _ = writeln!(out, "strategy {}", meta.mode);
    let _ = writeln!(out, "claims {}", claim_names(meta));
    let _ = writeln!(out, "\nlisting: inlined.txt");
    let _ = writeln!(
        out,
        "(left and right line numbers are independent — they index different columns of inlined.txt)"
    );
    let _ = writeln!(
        out,
        "J = joint path, S = stuck point; a node lists what each side consumed on the way, then\n\
         where each side stands, the solver's answers, and its children"
    );

    if let Some(root) = outcome.tree.nodes.first() {
        out.push('\n');
        render_node(&mut out, meta, outcome, root, 0);
    }

    if !outcome.stuck.is_empty() {
        let _ = writeln!(out, "\nstuck points:");
        for s in &outcome.stuck {
            let _ = writeln!(out, "  {}", describe_stuck(s));
        }
    }

    let _ = writeln!(out, "\n{}", one_line_summary(summary));
    if let Some(line) = stop_line(outcome) {
        let _ = writeln!(out, "{line}");
    }
    out
}

fn render_node(
    out: &mut String,
    meta: &LockstepMeta,
    outcome: &LockstepOutcome,
    node: &JointNode,
    depth: usize,
) {
    let pad = "  ".repeat(depth);
    let mut header = format!("{pad}[{}] {}", node.index, node.kind.as_str());
    if let Some(j) = &node.pair {
        let _ = write!(header, " {j}");
    }
    if let Some(s) = &node.stuck {
        let _ = write!(header, " {s}");
    }
    let _ = writeln!(out, "{header}");

    let _ = writeln!(
        out,
        "{pad}    left  {}",
        describe_side(&node.left, &meta.left_sites)
    );
    let _ = writeln!(
        out,
        "{pad}    right {}",
        describe_side(&node.right, &meta.right_sites)
    );

    if !node.answers.is_empty() {
        let answers: Vec<String> = node
            .answers
            .iter()
            .map(|a| format!("{}={}", a.query, answer_str(a.answer)))
            .collect();
        let _ = writeln!(out, "{pad}    solver: {}", answers.join(" "));
    }

    if let Some(pair) = node
        .pair
        .as_ref()
        .and_then(|id| outcome.pairs.iter().find(|p| &p.id == id))
    {
        let width = pair
            .claims
            .iter()
            .map(|c| c.claim.len() + 2)
            .max()
            .unwrap_or(0)
            .max(14);
        for c in &pair.claims {
            let name = format!("{}:", c.claim);
            let reason = match &c.verdict {
                Verdict::Unreachable { reason } => format!(
                    "  ({})",
                    describe_unreachable(reason, &pair.left.terminal, &pair.right.terminal)
                ),
                _ => String::new(),
            };
            let _ = writeln!(
                out,
                "{pad}    {name:<width$}{}{reason}",
                render_verdict(&c.verdict)
            );
            for r in &c.relations {
                let _ = writeln!(
                    out,
                    "{pad}      relation {}: {}",
                    r.name,
                    render_verdict(&r.verdict)
                );
            }
        }
    }

    // A node with one child (a determined branch, an independent sampling, a
    // stuck point) is a step in a sequence: its child continues at the same
    // indentation, so a long run of them stays readable.
    let sequence = node.children.len() == 1;
    for (i, child) in node.children.iter().enumerate() {
        let steps = describe_steps(child.left.as_ref(), child.right.as_ref());
        let next_depth = if sequence { depth } else { depth + 2 };
        let label = if sequence {
            format!("{pad}  ->")
        } else {
            format!("{pad}  child {}:", i + 1)
        };
        match &child.outcome {
            ChildOutcome::Explored { node: n } => {
                let _ = writeln!(out, "{label} {steps}");
                if let Some(next) = outcome.tree.nodes.get(*n) {
                    render_node(out, meta, outcome, next, next_depth);
                }
            }
            ChildOutcome::Pruned { answer } => {
                let _ = writeln!(
                    out,
                    "{label} {steps}   [{}: pruned, infeasible]",
                    answer_str(answer.answer)
                );
            }
            ChildOutcome::NotExplored => {
                let _ = writeln!(out, "{label} {steps}   [not explored]");
            }
        }
    }
}

fn describe_side(
    side: &SideView,
    sites: &BTreeMap<usize, crate::debug::driver::SiteView>,
) -> String {
    let mut s = String::new();
    if !side.consumed.is_empty() {
        let ranges: Vec<String> = side
            .consumed
            .iter()
            .map(|[a, b]| {
                if a == b {
                    format!("L{a}")
                } else {
                    format!("L{a}-{b}")
                }
            })
            .collect();
        let _ = write!(s, "consumed {}, ", ranges.join(" "));
    }
    let line = sites
        .get(&side.head.label)
        .map(|site| site.line.as_str())
        .unwrap_or("");
    let _ = write!(s, "at L{} {line}", side.head.label);
    if let Some(p) = side.plumbing {
        let _ = write!(s, "   [plumbing: {}]", plumbing_str(p));
    }
    s
}

fn plumbing_str(p: crate::debug::lockstep::PlumbingKind) -> &'static str {
    match p {
        crate::debug::lockstep::PlumbingKind::DoneGuard => "done-guard",
        crate::debug::lockstep::PlumbingKind::CallResult => "call-result",
    }
}

fn describe_steps(left: Option<&SideStep>, right: Option<&SideStep>) -> String {
    let side = |name: &str, step: Option<&SideStep>| {
        step.map(|s| format!("{name} L{} {}", s.label, s.decision))
    };
    let parts: Vec<String> = [side("left", left), side("right", right)]
        .into_iter()
        .flatten()
        .collect();
    parts.join(", ")
}

fn describe_stuck(s: &StuckPoint) -> String {
    format!(
        "{}  {} sampling {} (draw {}) at L{} — {}   [left at L{}, right at L{}]",
        s.id,
        s.side,
        s.sample,
        s.draw,
        s.label,
        s.reason.as_str(),
        s.left_label,
        s.right_label
    )
}

fn answer_str(a: crate::debug::lockstep::Answer) -> &'static str {
    match a {
        crate::debug::lockstep::Answer::Sat => "sat",
        crate::debug::lockstep::Answer::Unsat => "unsat",
        crate::debug::lockstep::Answer::Unknown => "unknown",
    }
}

fn render_verdict(v: &Verdict) -> String {
    match v {
        Verdict::Verified => "[unsat: ok]".to_string(),
        Verdict::Unreachable { .. } => "[unsat: unreachable]".to_string(),
        Verdict::GoalFails { model } => format!("[sat: GOAL FAILS]  {model}"),
        Verdict::Inconclusive { model: Some(model) } => format!("[unknown: inconclusive]  {model}"),
        Verdict::Inconclusive { model: None } => "[unknown: inconclusive]".to_string(),
    }
}

fn one_line_summary(s: &LockstepSummary) -> String {
    let mut line = format!(
        "summary: {} joint paths, {} stuck points",
        s.joint_paths, s.stuck_points
    );
    for c in &s.claims {
        let c = (&c.claim, &c.counts);
        let _ = write!(
            line,
            "; {} {} verified / {} GOAL FAILS / {} unreachable / {} inconclusive",
            c.0, c.1.verified, c.1.goal_fails, c.1.unreachable, c.1.inconclusive
        );
    }
    line
}

fn listing_name(meta: &LockstepMeta) -> &'static str {
    if meta.listing == "easycrypt" {
        "EasyCrypt"
    } else {
        "Domino"
    }
}

/// `equal-output, invariant`, or `all 5 claims of the oracle`.
fn claim_names(meta: &LockstepMeta) -> String {
    let checked: Vec<&str> = meta
        .claims
        .iter()
        .filter(|c| !c.admitted)
        .map(|c| c.name.as_str())
        .collect();
    let admitted = meta.claims.len() - checked.len();
    if meta.all_claims && meta.listing == "domino" {
        if admitted == 0 {
            format!("all {} claims of the oracle", checked.len())
        } else {
            format!(
                "all {} claims of the oracle ({admitted} admitted, not checked)",
                checked.len()
            )
        }
    } else {
        checked.join(", ")
    }
}

fn stop_line(outcome: &LockstepOutcome) -> Option<String> {
    match outcome.stop_reason {
        StopReason::Completed => None,
        StopReason::Interrupted => Some(format!(
            "[STOPPED EARLY (interrupted by Ctrl-C) — {} joint paths explored]",
            outcome.pairs.len()
        )),
        StopReason::MaxPaths { limit } => Some(format!(
            "[STOPPED EARLY (--max-paths {limit} reached) — {} joint paths explored]",
            outcome.pairs.len()
        )),
    }
}

// ---------------------------------------------------------------------------
// stdout
// ---------------------------------------------------------------------------

/// The concise report `domino debug --lockstep` and `domino easycrypt debug` print: counts
/// of joint paths per claim and per combination of verdicts, the stuck points, the failures
/// per state relation, and why the run stopped. The full tree is the summary file.
pub fn render_summary(run: &LockstepRun) -> String {
    let meta = &run.meta;
    let outcome = &run.outcome;
    let sm = &run.summary;
    let mut s = String::new();

    let title = if meta.listing == "easycrypt" {
        "domino easycrypt debug — summary"
    } else {
        "domino debug — summary"
    };
    let _ = writeln!(s, "{title}");
    let _ = writeln!(s, "{}", "=".repeat(title.chars().count()));
    let _ = writeln!(s, "{:<14}{}", "strategy", meta.mode);
    let _ = writeln!(s, "{:<14}{}", "listing", listing_name(meta));
    let _ = writeln!(
        s,
        "{:<14}{}, proofstep {}",
        "theorem", meta.theorem, meta.proofstep
    );
    let _ = writeln!(
        s,
        "{:<14}{}  ==  {}",
        "games", meta.left_game, meta.right_game
    );
    let _ = writeln!(s, "{:<14}{}", "oracle", meta.oracle);
    let _ = writeln!(s, "{:<14}{}", "claims", claim_names(meta));
    let o = &meta.options;
    let _ = writeln!(
        s,
        "{:<14}timeout={} max-paths={} smt={}",
        "options",
        o.timeout_ms
            .map_or("none".to_string(), |ms| format!("{ms}ms")),
        o.max_paths
            .map_or("unlimited".to_string(), |n| n.to_string()),
        o.smt.as_str(),
    );
    s.push('\n');

    let status = match outcome.stop_reason {
        StopReason::Completed => "COMPLETE — the whole joint tree explored".to_string(),
        StopReason::Interrupted => "STOPPED EARLY (interrupted by Ctrl-C)".to_string(),
        StopReason::MaxPaths { limit } => format!("STOPPED EARLY (--max-paths {limit} reached)"),
    };
    let _ = writeln!(s, "{:<14}{status}", "status");
    let _ = writeln!(s, "{:<14}{}", "elapsed", format_elapsed(run.elapsed));

    s.push_str("\npaths\n");
    let _ = writeln!(
        s,
        "  {:<14}{}   (sequential: {} left x {} right = {})",
        "joint paths",
        sm.joint_paths,
        meta.left_syntactic,
        meta.right_syntactic,
        meta.left_syntactic.saturating_mul(meta.right_syntactic),
    );
    let _ = writeln!(
        s,
        "  {:<14}{} ({} children pruned as infeasible)",
        "joint nodes", sm.nodes, sm.pruned_children
    );

    let names: Vec<&str> = sm.claims.iter().map(|c| c.claim.as_str()).collect();
    if names.len() <= 2 {
        let _ = writeln!(s, "\nverdicts   ({})", names.join(" / "));
        if sm.verdict_combos.is_empty() {
            s.push_str("  none\n");
        }
        for combo in &sm.verdict_combos {
            let cells: Vec<String> = combo.verdicts.iter().map(|v| format!("{v:<13}")).collect();
            let _ = writeln!(s, "  {}{}", cells.join(" / "), combo.count);
        }
    } else {
        // many claims: one row per claim rather than one column per claim
        let width = names.iter().map(|n| n.len()).max().unwrap_or(0).max(5);
        let _ = writeln!(
            s,
            "\nclaims     {:<width$}  verified  unreachable (pair / dependency)  GOAL FAILS  inconclusive",
            "claim"
        );
        for c in &sm.claims {
            let k = &c.counts;
            let _ = writeln!(
                s,
                "           {:<width$}  {:>8}  {:>11} / {:<10}  {:>10}  {:>12}",
                c.claim,
                k.verified,
                k.unreachable - k.unreachable_dependency,
                k.unreachable_dependency,
                k.goal_fails,
                k.inconclusive,
            );
        }
        for info in meta.claims.iter().filter(|c| c.admitted) {
            let _ = writeln!(s, "           {:<width$}  admitted — not checked", info.name);
        }
    }

    if !sm.relation_failures.is_empty() {
        s.push_str("\nstate relations failing (joint paths)\n");
        for (name, n) in &sm.relation_failures {
            let _ = writeln!(s, "  {name:<24}{n}");
        }
    }

    let _ = writeln!(s, "\nstuck points  {}", outcome.stuck.len());
    for st in &outcome.stuck {
        let _ = writeln!(s, "  {}", describe_stuck(st));
    }

    let failing: Vec<&PairRecord> = outcome.pairs.iter().filter(|p| p.has_failure()).collect();
    if !failing.is_empty() {
        s.push_str("\nfailing joint paths\n");
        const CAP: usize = 20;
        for p in failing.iter().take(CAP) {
            let aborts = match (p.left.terminal.is_abort, p.right.terminal.is_abort) {
                (false, false) => "",
                (true, false) => "   [left aborts]",
                (false, true) => "   [right aborts]",
                (true, true) => "   [both abort]",
            };
            // two claims: both, as ever; more: the ones that failed
            let shown: Vec<String> = p
                .claims
                .iter()
                .filter(|c| p.claims.len() <= 2 || c.verdict.is_failure())
                .map(|c| format!("{} {:<14}", c.claim, c.verdict.slug()))
                .collect();
            let _ = writeln!(s, "  {:<6} {}{aborts}", p.id, shown.join(" "));
        }
        if failing.len() > CAP {
            let _ = writeln!(s, "  … and {} more (see summary.txt)", failing.len() - CAP);
        }
    }

    let layout = meta.layout;
    let _ = writeln!(s, "\n{:<14}{}", "artifacts", meta.out_dir);
    let _ = writeln!(
        s,
        "  {:<12}{}        (joint tree: {} nodes, {} joint paths)",
        "tree",
        layout.summary(),
        sm.nodes,
        sm.joint_paths
    );
    let _ = writeln!(
        s,
        "  {:<12}{}         (joint-tree viewer)",
        "viewer",
        layout.viewer()
    );
    let _ = writeln!(s, "  {:<12}{}", "trace", layout.trace());
    let _ = writeln!(s, "  {:<12}inlined.txt", "listing");
    if o.smt.as_str() != "none" {
        let _ = writeln!(
            s,
            "  {:<12}{}/               ({})",
            "smt",
            layout.rel("smt"),
            o.smt.as_str()
        );
    }
    if o.transcript {
        let _ = writeln!(s, "  {:<12}{}", "transcript", layout.rel("transcript.smt2"));
    }
    s
}

// ---------------------------------------------------------------------------
// smt/
// ---------------------------------------------------------------------------

/// Writes `smt/`: runnable cvc5 inputs for the joint paths, keyed by `J` id.
///
/// ```text
/// smt/
///   base.smt2     the base frame: declarations, game definitions, assumptions
///   J3.smt2       joint path J3: base ++ both sides' paths ++ vacuity ++ each failing check
/// ```
///
/// `cvc5 --lang smt2 smt/J3.smt2` reproduces the recorded verdicts: the first
/// `(check-sat)` is the vacuity check (`unsat` means the path cannot happen),
/// then one per failing check (`sat` means the check fails). Coverage is
/// [`SmtOut`]: `failures` writes files for the failing joint paths, `all` for
/// every one, `deltas` for every one without the base frame (reassemble with
/// `cat smt/base.smt2 smt/J3.smt2 | cvc5 --lang smt2 -`).
pub struct LockstepSmtWriter {
    root: PathBuf,
    /// `root` relative to the run's output directory.
    rel: String,
    mode: SmtOut,
    header: String,
    base_body: String,
}

impl LockstepSmtWriter {
    pub fn new(
        out_dir: &Path,
        layout: Layout,
        mode: SmtOut,
        header: String,
        base_frame_smt: &str,
    ) -> std::io::Result<Self> {
        let mut preamble = String::new();
        if !base_frame_smt.contains(":incremental") && !base_frame_smt.contains("incremental true")
        {
            preamble.push_str("(set-option :incremental true)\n");
        }
        if !base_frame_smt.contains("produce-models") {
            preamble.push_str("(set-option :produce-models true)\n");
        }
        let writer = Self {
            root: layout.path(out_dir, "smt"),
            rel: layout.rel("smt"),
            mode,
            header,
            base_body: format!("{preamble}{base_frame_smt}\n"),
        };
        if !matches!(mode, SmtOut::None) {
            std::fs::create_dir_all(&writer.root)?;
            std::fs::write(writer.root.join("base.smt2"), &writer.base_body)?;
        }
        Ok(writer)
    }

    fn covers(&self, pair: &PairRecord) -> bool {
        match self.mode {
            SmtOut::None => false,
            SmtOut::All | SmtOut::Deltas => true,
            SmtOut::Failures => pair.has_failure(),
        }
    }

    /// Write `smt/<J>.smt2` if the mode covers `pair`. `goals` are the negated
    /// goals of the checks, `(name, smt)`, in the order the engine ran them.
    pub fn write_pair(
        &self,
        pair: &PairRecord,
        left: &TerminalPath,
        right: &TerminalPath,
        goals: &[GoalBlock],
    ) -> std::io::Result<()> {
        if !self.covers(pair) {
            return Ok(());
        }
        let self_contained = !matches!(self.mode, SmtOut::Deltas);
        let mut s = String::new();
        s.push_str(&self.header);
        let _ = writeln!(s, "; joint path {}", pair.id);
        let recorded: Vec<String> = pair
            .claims
            .iter()
            .map(|c| format!("{} {}", c.claim, c.verdict.slug()))
            .collect();
        let _ = writeln!(s, "; verdicts recorded: {}", recorded.join(", "));
        if self_contained {
            s.push_str("; run:  cvc5 --lang smt2 <this file>\n");
        } else {
            let _ = writeln!(
                s,
                "; run:  cat {rel}/base.smt2 {rel}/{}.smt2 | cvc5 --lang smt2 -",
                pair.id,
                rel = self.rel
            );
        }
        s.push_str(
            ";   first  (check-sat)  is the vacuity check   — `unsat` means the joint path cannot happen\n\
             ;   then one (check-sat) per check that did not verify — `sat` means it FAILS\n\n",
        );
        if self_contained {
            s.push_str(
                "; ---- base frame -------------------------------------------------------\n",
            );
            s.push_str(&self.base_body);
            s.push('\n');
        }
        for (name, path) in [("left", left), ("right", right)] {
            let _ = writeln!(
                s,
                "; ---- {name} path ------------------------------------------------------"
            );
            for e in path
                .decls
                .iter()
                .chain(&path.constraints)
                .chain(std::iter::once(&path.return_constraint))
            {
                let _ = writeln!(s, "{e}");
            }
            s.push('\n');
        }
        s.push_str("; ---- vacuity ----------------------------------------------------------\n(check-sat)\n\n");

        let verdict_of = |name: &str| -> Option<&Verdict> {
            pair.verdict_of(name).or_else(|| {
                pair.claims
                    .iter()
                    .flat_map(|c| &c.relations)
                    .find(|r| format!("relation-{}", r.name) == name)
                    .map(|r| &r.verdict)
            })
        };
        for goal in goals {
            let name = &goal.claim;
            let Some(verdict) = verdict_of(name) else {
                continue;
            };
            if matches!(self.mode, SmtOut::Failures) && !verdict.is_failure() {
                continue;
            }
            let _ = writeln!(s, "; ---- {name}: {} ----", verdict.slug());
            s.push_str("(push 1)\n");
            for dependency in &goal.dependencies {
                s.push_str(dependency);
                s.push('\n');
            }
            s.push_str(&goal.negated);
            s.push_str("\n(check-sat)\n(get-model)\n(pop 1)\n\n");
        }

        std::fs::write(self.root.join(format!("{}.smt2", pair.id)), s)
    }
}
