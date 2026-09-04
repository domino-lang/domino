// SPDX-License-Identifier: MIT OR Apache-2.0

//! Serialisation of a [`DebugRun`](crate::debug::driver::DebugRun) to
//! `trace.json` and a self-contained `index.html` tree viewer.
//!
//! `trace.json` is the source of truth; `index.html` is only a renderer over it
//! (a future TUI or CI check consumes the same JSON). The HTML embeds the JSON
//! verbatim in a `<script type="application/json">` block and carries all of its
//! CSS and JS inline — it opens from `file://` with the machine offline and
//! fetches nothing.
//!
//! Determinism: for an unchanged project two runs produce byte-identical
//! `trace.json` and `index.html`. `serde_json` preserves struct field order,
//! [`DebugRun`](crate::debug::driver::DebugRun) uses `BTreeMap` for its site
//! maps, and the absolute `out_dir` is `#[serde(skip)]`ped.

use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::time::Duration;

use crate::debug::driver::{DebugRun, StepView, StopReason, TerminalView, Verdict};

/// Write `trace.json` into `out_dir`. Returns the path written.
pub fn write_trace_json(run: &DebugRun, out_dir: &Path) -> std::io::Result<PathBuf> {
    let path = out_dir.join("trace.json");
    let mut json = serde_json::to_string_pretty(run)
        .map_err(std::io::Error::other)?;
    json.push('\n');
    std::fs::write(&path, json)?;
    Ok(path)
}

/// Write `trace.json`, `index.html` and `summary.txt` for the run so far.
///
/// Called after every left path (story 09's incremental flush, so a `Ctrl-C` or
/// `--max-paths` leaves a usable partial trace + viewer) and once at the end.
/// All files truncate-write, so an intermediate flush is simply overwritten by
/// the next one; the *final* `trace.json` / `index.html` bytes are byte-identical
/// to a single end-of-run write (story 07's determinism guarantee — no
/// timestamps enter `DebugRun`). `summary.txt` is **excluded** from that
/// guarantee: it carries `elapsed` (story 12).
/// Errors are surfaced: a failing flush is a real problem (out of disk, bad
/// path).
pub fn flush(run: &DebugRun, elapsed: Duration, out_dir: &Path) -> std::io::Result<()> {
    write_trace_json(run, out_dir)?;
    write_html(run, out_dir)?;
    write_summary(run, elapsed, out_dir)?;
    Ok(())
}

/// Write the self-contained `index.html` viewer into `out_dir`. Returns the path
/// written.
pub fn write_html(run: &DebugRun, out_dir: &Path) -> std::io::Result<PathBuf> {
    let path = out_dir.join("index.html");
    let json = serde_json::to_string(run)
        .map_err(std::io::Error::other)?;
    std::fs::write(&path, render_html(&json))?;
    Ok(path)
}

/// Write the concise run report to `<out_dir>/summary.txt` (story 12).
///
/// This is the file that answers "did it finish, and what did it find?" without
/// scrolling back through a thousand-line `render_tree` dump. It is rewritten on
/// every [`flush`] (once per left path) so an interrupted run still has a current
/// summary.
///
/// Unlike `trace.json` / `index.html` this file is **not** byte-deterministic:
/// it carries the wall-clock `elapsed` line. Everything else on it is a function
/// of `run` alone, so two identical runs produce a `summary.txt` that differs
/// only in that one line.
pub fn write_summary(
    run: &DebugRun,
    elapsed: Duration,
    out_dir: &Path,
) -> std::io::Result<PathBuf> {
    let path = out_dir.join("summary.txt");
    std::fs::write(&path, render_summary(run, elapsed))?;
    Ok(path)
}

/// `1h 02m 03s` / `2m 04s` / `4.3s` / `0.2s`.
fn format_elapsed(d: Duration) -> String {
    let total = d.as_secs();
    if total >= 3600 {
        format!("{}h {:02}m {:02}s", total / 3600, (total % 3600) / 60, total % 60)
    } else if total >= 60 {
        format!("{}m {:02}s", total / 60, total % 60)
    } else {
        format!("{:.1}s", d.as_secs_f64())
    }
}

/// `L14 else → L20 then → L36 return` — the branch decisions that pin this path,
/// then the terminal. `assert-holds` / `unwrap-some` steps are dropped: they are
/// the *non*-events (the assert passed, the value was present), so a chain of
/// them adds width without telling you where the two sides diverged.
fn chain_str(steps: &[StepView], terminal: &TerminalView) -> String {
    let mut parts: Vec<String> = steps
        .iter()
        .filter(|s| !matches!(s.decision.as_str(), "assert-holds" | "unwrap-some"))
        .map(|s| format!("L{} {}", s.label, s.decision))
        .collect();
    parts.push(format!(
        "L{} {}",
        terminal.label,
        if terminal.is_abort { "abort" } else { "return" }
    ));
    parts.join(" → ")
}

fn render_summary(run: &DebugRun, elapsed: Duration) -> String {
    let o = &run.options;
    let mut s = String::new();

    // ---- header block -----------------------------------------------------
    s.push_str("domino debug — summary\n");
    s.push_str("======================\n");
    let _ = writeln!(s, "{:<14}{}, proofstep {}", "theorem", run.theorem, run.proofstep);
    let _ = writeln!(s, "{:<14}{}  ==  {}", "games", run.left_game, run.right_game);
    let _ = writeln!(s, "{:<14}{}", "oracle", run.oracle);
    let _ = writeln!(s, "{:<14}{}", "claim", run.claim);
    let _ = writeln!(
        s,
        "{:<14}check-left={} check-right={} timeout={} max-paths={} jobs=1 smt={}",
        "options",
        if o.check_left { "on" } else { "off" },
        if o.check_right { "on" } else { "off" },
        match o.timeout_ms {
            Some(ms) => format!("{ms}ms"),
            None => "none".to_string(),
        },
        match o.max_paths {
            Some(n) => n.to_string(),
            None => "unlimited".to_string(),
        },
        o.smt.as_str(),
    );
    s.push('\n');

    // ---- status ---------------------------------------------------------
    let status = if run.admitted {
        "ADMITTED — nothing to check".to_string()
    } else if !run.partial() {
        "COMPLETE — all paths explored".to_string()
    } else {
        match run.stop_reason {
            StopReason::Interrupted => "STOPPED EARLY (interrupted by Ctrl-C)".to_string(),
            StopReason::MaxPaths { limit } => {
                format!("STOPPED EARLY (--max-paths {limit} reached)")
            }
            StopReason::Completed => "COMPLETE — all paths explored".to_string(),
        }
    };
    let _ = writeln!(s, "{:<14}{}", "status", status);
    let _ = writeln!(s, "{:<14}{}", "elapsed", format_elapsed(elapsed));

    if run.admitted {
        return s;
    }

    let sm = &run.summary;

    // ---- paths ---------------------------------------------------------
    s.push_str("\npaths\n");
    let of_syntactic = if run.left_syntactic > 0 {
        format!(" of {} syntactic", run.left_syntactic)
    } else {
        String::new()
    };
    let left_note = if sm.left_pruned > 0 {
        format!("   ({} unreachable, pruned at its terminal)", sm.left_pruned)
    } else {
        String::new()
    };
    let _ = writeln!(
        s,
        "  {:<13}{} explored{}{}",
        "left", sm.left_paths, of_syntactic, left_note
    );
    let right_note = if sm.right_pruned_branches > 0 {
        format!("   ({} branches pruned)", sm.right_pruned_branches)
    } else {
        String::new()
    };
    let _ = writeln!(s, "  {:<13}{} explored{}", "right", sm.right_paths, right_note);
    let _ = writeln!(
        s,
        "  {:<13}{} left / {} right pruned as unreachable",
        "branches", sm.left_pruned_branches, sm.right_pruned_branches
    );
    let _ = writeln!(s, "  {:<13}{} checked", "pairs", sm.right_paths);

    // ---- verdicts ----------------------------------------------------
    s.push_str("\nverdicts\n");
    let _ = writeln!(s, "  {:<14}{}", "verified", sm.verified);
    let _ = writeln!(s, "  {:<14}{}", "unreachable", sm.unreachable);
    let _ = writeln!(s, "  {:<14}{}", "GOAL FAILS", sm.goal_fails);
    let _ = writeln!(s, "  {:<14}{}", "inconclusive", sm.inconclusive);

    // ---- failing / inconclusive pairs --------------------------------
    let mut goal_fails: Vec<(String, String, Option<String>)> = Vec::new();
    let mut inconclusive: Vec<(String, String, Option<String>)> = Vec::new();
    for lp in &run.left_paths {
        for rp in &lp.right_paths {
            let chain = chain_str(&rp.steps, &rp.terminal);
            match &rp.verdict {
                Verdict::GoalFails { model } => {
                    goal_fails.push((rp.id.clone(), chain, Some(model.clone())))
                }
                Verdict::Inconclusive { model } => {
                    inconclusive.push((rp.id.clone(), chain, model.clone()))
                }
                _ => {}
            }
        }
    }
    write_pair_block(&mut s, "goal failures", &goal_fails);
    write_pair_block(&mut s, "inconclusive", &inconclusive);

    // ---- artifacts -------------------------------------------------
    s.push_str("\nartifacts\n");
    let mut artifact = |label: &str, target: &str| {
        let _ = writeln!(s, "  {label:<14}{target}");
    };
    artifact("tree", "index.html");
    artifact("trace", "trace.json");
    artifact("listing", "inlined.txt");
    if o.smt.as_str() != "none" {
        artifact("smt", &format!("smt/            ({})", o.smt.as_str()));
    }
    if o.transcript {
        artifact("transcript", "transcript.smt2");
    }

    s
}

/// A `goal failures` / `inconclusive` block: heading, up to 20 entries, then a
/// `… and N more` line. Nothing at all when the list is empty.
fn write_pair_block(
    s: &mut String,
    heading: &str,
    entries: &[(String, String, Option<String>)],
) {
    if entries.is_empty() {
        return;
    }
    let _ = writeln!(s, "\n{heading}");
    const CAP: usize = 20;
    for (id, chain, model) in entries.iter().take(CAP) {
        let id = format!("#{id}");
        match model {
            Some(m) => {
                let _ = writeln!(s, "  {id:<7} {chain:<40}  {m}");
            }
            None => {
                let _ = writeln!(s, "  {id:<7} {chain}");
            }
        }
    }
    if entries.len() > CAP {
        let _ = writeln!(s, "  … and {} more (see index.html)", entries.len() - CAP);
    }
}

/// Splice the trace JSON into the static template.
fn render_html(trace_json: &str) -> String {
    // Every `<` in valid JSON is inside a string literal, so replacing it with
    // the equivalent `<` escape keeps the JSON semantically identical while
    // making a `</script>` breakout impossible.
    let safe = trace_json.replace('<', "\\u003c");
    TEMPLATE.replace("__TRACE_JSON__", &safe)
}

const TEMPLATE: &str = r##"<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>domino debug — execution tree</title>
<style>
:root {
  --bg: #ffffff;
  --bg-alt: #f4f5f7;
  --bg-inset: #eceef1;
  --fg: #1c1e21;
  --fg-muted: #626772;
  --border: #d5d8dd;
  --accent: #3355cc;
  --ok-fg: #1f6f3f;      --ok-bg: #e3f3e8;
  --unreach-fg: #55606e; --unreach-bg: #e7e9ec;
  --fail-fg: #a11d1d;    --fail-bg: #f7e0e0;
  --amber-fg: #8a5a00;   --amber-bg: #fbeecc;
  --mono: ui-monospace, SFMono-Regular, "SF Mono", Menlo, Consolas, monospace;
}
@media (prefers-color-scheme: dark) {
  :root {
    --bg: #16181c;
    --bg-alt: #1e2127;
    --bg-inset: #12141a;
    --fg: #e7e9ec;
    --fg-muted: #9aa2ae;
    --border: #333842;
    --accent: #8aa0ff;
    --ok-fg: #7fd6a0;      --ok-bg: #16321f;
    --unreach-fg: #aab2bf; --unreach-bg: #262a31;
    --fail-fg: #ff9b9b;    --fail-bg: #3a1d1d;
    --amber-fg: #f0c674;   --amber-bg: #38300f;
  }
}
* { box-sizing: border-box; }
html, body { height: 100%; }
body {
  margin: 0;
  background: var(--bg);
  color: var(--fg);
  font: 14px/1.5 system-ui, -apple-system, Segoe UI, Roboto, sans-serif;
  display: flex;
  flex-direction: column;
  overflow: hidden;
}
header {
  padding: 10px 16px;
  border-bottom: 1px solid var(--border);
  background: var(--bg-alt);
  flex: none;
}
header h1 { font-size: 15px; margin: 0 0 2px; font-weight: 600; }
header .sub { color: var(--fg-muted); font-size: 13px; }
.chips { margin-top: 8px; display: flex; flex-wrap: wrap; gap: 6px; }
.chip {
  font: 12px/1 var(--mono);
  padding: 4px 8px;
  border-radius: 10px;
  background: var(--bg-inset);
  color: var(--fg-muted);
  white-space: nowrap;
}
.chip.ok { background: var(--ok-bg); color: var(--ok-fg); }
.chip.unreach { background: var(--unreach-bg); color: var(--unreach-fg); }
.chip.fail { background: var(--fail-bg); color: var(--fail-fg); }
.chip.amber { background: var(--amber-bg); color: var(--amber-fg); }

main { flex: 1; display: flex; min-height: 0; }
#left {
  width: 42%;
  min-width: 280px;
  border-right: 1px solid var(--border);
  display: flex;
  flex-direction: column;
  min-height: 0;
}
#filter {
  padding: 8px 12px;
  border-bottom: 1px solid var(--border);
  background: var(--bg-alt);
  flex: none;
}
#filter input[type=text] {
  width: 100%;
  padding: 5px 8px;
  border: 1px solid var(--border);
  border-radius: 5px;
  background: var(--bg);
  color: var(--fg);
  font: 13px var(--mono);
}
#filter .toggles { margin-top: 6px; display: flex; flex-wrap: wrap; gap: 10px; }
#filter label { font-size: 12px; color: var(--fg-muted); cursor: pointer; user-select: none; }
#tree { overflow: auto; padding: 6px 0 40px; flex: 1; }

.lp { border-bottom: 1px solid var(--border); }
.lp-head, .rp {
  display: flex;
  gap: 8px;
  align-items: baseline;
  padding: 5px 12px;
  cursor: pointer;
}
.lp-head:hover, .rp:hover { background: var(--bg-alt); }
.node.sel > .lp-head, .rp.sel { background: var(--bg-inset); box-shadow: inset 3px 0 0 var(--accent); }
.twist { width: 12px; color: var(--fg-muted); flex: none; font-size: 11px; }
.pid { font: 12px var(--mono); color: var(--fg-muted); flex: none; }
.chain { font: 12px/1.4 var(--mono); color: var(--fg); flex: 1; word-break: break-word; }
.chain .dec { color: var(--accent); }
.rp-list { }
.rp { padding-left: 30px; font-size: 13px; border-top: 1px dashed var(--border); }
.lp.collapsed .rp-list { display: none; }

.badge {
  font: 11px/1 var(--mono);
  padding: 3px 6px;
  border-radius: 4px;
  flex: none;
  white-space: nowrap;
}
.badge.verified { background: var(--ok-bg); color: var(--ok-fg); }
.badge.unreachable { background: var(--unreach-bg); color: var(--unreach-fg); }
.badge.goalfails { background: var(--fail-bg); color: var(--fail-fg); }
.badge.inconclusive { background: var(--amber-bg); color: var(--amber-fg); }
.badge.pruned { background: var(--unreach-bg); color: var(--unreach-fg); text-decoration: line-through; }
.mini { font: 11px var(--mono); color: var(--fg-muted); flex: none; }

#detail { flex: 1; overflow: auto; padding: 14px 18px 60px; min-width: 0; }
#detail h2 { font-size: 14px; margin: 0 0 4px; }
#detail .path-sub { color: var(--fg-muted); font-size: 12px; margin-bottom: 12px; }
/* Detail-pane toolbar + tree toolbar (story 13). */
.sectoolbar { display: flex; gap: 8px; margin-bottom: 14px; }
.sectoolbar button, .treetoolbar button {
  font: 11px var(--mono);
  padding: 3px 9px;
  border: 1px solid var(--border);
  border-radius: 4px;
  background: var(--bg);
  color: var(--fg-muted);
  cursor: pointer;
}
.sectoolbar button:hover, .treetoolbar button:hover { color: var(--fg); border-color: var(--accent); }
.treetoolbar { display: flex; gap: 8px; margin-top: 8px; }

/* Every detail section is a <details class="sec"> (story 13). */
details.sec {
  margin: 0 0 10px;
  border: 1px solid var(--border);
  border-radius: 6px;
  background: var(--bg-alt);
}
details.sec > summary {
  cursor: pointer;
  list-style: none;
  padding: 8px 12px;
  display: flex;
  gap: 10px;
  align-items: baseline;
  font: 12px/1.3 var(--mono);
  text-transform: uppercase;
  letter-spacing: .05em;
  color: var(--fg-muted);
}
details.sec > summary::-webkit-details-marker { display: none; }
details.sec > summary::before {
  content: "\25B8";
  color: var(--fg-muted);
  font-size: 10px;
  flex: none;
}
details.sec[open] > summary::before { content: "\25BE"; }
details.sec .sec-title { color: var(--fg); font-weight: 600; }
details.sec .sec-meta {
  margin-left: auto;
  text-transform: none;
  letter-spacing: 0;
  color: var(--fg-muted);
  font-size: 11px;
  text-align: right;
}
details.sec > .sec-body { padding: 0 12px 12px; }
.copy-btn {
  font: 11px var(--mono);
  padding: 2px 8px;
  margin-bottom: 8px;
  border: 1px solid var(--border);
  border-radius: 4px;
  background: var(--bg);
  color: var(--fg-muted);
  cursor: pointer;
}
.copy-btn:hover { color: var(--fg); border-color: var(--accent); }
.assertion-note { color: var(--fg-muted); font-size: 12px; margin-bottom: 8px; }
.assertion-outcome { font-size: 12px; margin-top: 8px; }
table.steps { border-collapse: collapse; width: 100%; font: 12px var(--mono); }
table.steps td { padding: 3px 8px 3px 0; vertical-align: top; }
table.steps td.l { color: var(--fg-muted); white-space: nowrap; }
table.steps td.d { color: var(--accent); white-space: nowrap; }
pre {
  margin: 0;
  padding: 10px 12px;
  background: var(--bg-inset);
  border: 1px solid var(--border);
  border-radius: 6px;
  overflow-x: auto;
  font: 12px/1.5 var(--mono);
  white-space: pre;
}
.listing { counter-reset: ln; }
.listing .row { display: flex; }
.listing .row .n {
  color: var(--fg-muted);
  text-align: right;
  padding-right: 12px;
  user-select: none;
  flex: none;
  min-width: 3ch;
}
.listing .row.hi { background: var(--amber-bg); }
.listing .row.term { background: var(--fail-bg); }
details { margin-top: 6px; }
summary { cursor: pointer; color: var(--fg-muted); font: 12px var(--mono); }
.empty { color: var(--fg-muted); padding: 20px; }
.hidden { display: none !important; }
</style>
</head>
<body>
<header>
  <h1 id="h-title"></h1>
  <div class="sub" id="h-sub"></div>
  <div class="chips" id="h-opts"></div>
  <div class="chips" id="h-summary"></div>
</header>
<main>
  <div id="left">
    <div id="filter">
      <input type="text" id="q" placeholder="filter by path id or source text…" autocomplete="off">
      <div class="toggles" id="vtoggles"></div>
      <div class="treetoolbar">
        <button type="button" id="tree-collapse">Collapse all</button>
        <button type="button" id="tree-expand">Expand all</button>
      </div>
    </div>
    <div id="tree"></div>
  </div>
  <div id="detail"><div class="empty">Select a path on the left.</div></div>
</main>

<script type="application/json" id="trace">__TRACE_JSON__</script>
<script>
"use strict";
const T = JSON.parse(document.getElementById("trace").textContent);

const el = (tag, cls, txt) => {
  const n = document.createElement(tag);
  if (cls) n.className = cls;
  if (txt != null) n.textContent = txt;
  return n;
};
const verdictKind = v => (v && v.kind) || "verified";
const badgeClass = k => ({ "verified":"verified", "unreachable":"unreachable",
  "goal-fails":"goalfails", "inconclusive":"inconclusive", "pruned":"pruned" }[k] || "verified");
const badgeText = k => ({ "verified":"verified", "unreachable":"unreachable",
  "goal-fails":"GOAL FAILS", "inconclusive":"inconclusive", "pruned":"pruned (unsat)" }[k] || k);

// A pruned branch is rendered with the same machinery as a path: a synthetic
// row whose "terminal" is the cut fork line and whose verdict is "pruned".
const PRUNED = { kind: "pruned" };
const prunedRow = (pb, parentId) => ({
  id: pb.id,
  steps: pb.steps,
  terminal: { label: pb.label, line: pb.line, is_abort: false },
  verdict: PRUNED,
  pruned: true,
  decision: pb.decision,
  model_smt: null,
  smt: [],
  _parent: parentId,
});

// ---- header ---------------------------------------------------------------
document.getElementById("h-title").textContent =
  `${T.theorem} · proofstep ${T.proofstep} · ${T.left_game} == ${T.right_game}`;
document.getElementById("h-sub").textContent =
  `oracle ${T.oracle} · claim ${T.claim}` + (T.admitted ? " · ADMITTED (nothing checked)" : "");

const optChips = document.getElementById("h-opts");
const o = T.options;
[["check-left", o.check_left], ["check-right (vacuity)", o.check_right],
 ["timeout", o.timeout_ms == null ? "off" : o.timeout_ms + "ms"],
 ["max-paths", o.max_paths == null ? "unlimited" : o.max_paths],
 ["smt", o.smt == null ? "failures" : o.smt],
 ["transcript", o.transcript ? "on" : "off"]].forEach(([k, val]) => {
  optChips.appendChild(el("span", "chip", `${k}: ${val}`));
});

const s = T.summary;
const sc = document.getElementById("h-summary");
const addChip = (cls, txt) => sc.appendChild(el("span", "chip " + cls, txt));
addChip("", `${s.left_paths} left paths` + (s.left_pruned ? ` (${s.left_pruned} pruned)` : ""));
addChip("", `${s.right_paths} right paths`);
if (s.left_pruned_branches || s.right_pruned_branches)
  addChip("unreach", `${s.left_pruned_branches + s.right_pruned_branches} branches pruned` +
    ` (${s.left_pruned_branches}L / ${s.right_pruned_branches}R)`);
addChip("ok", `${s.verified} verified`);
addChip("unreach", `${s.unreachable} unreachable`);
addChip(s.goal_fails ? "fail" : "", `${s.goal_fails} goal fails`);
addChip(s.inconclusive ? "amber" : "", `${s.inconclusive} inconclusive`);
if (s.sibling_shortcuts) addChip("", `${s.sibling_shortcuts} sibling shortcuts`);
// story 12: `partial: bool` became `stop_reason: {kind, …}`. Read the new shape,
// fall back to the old flag so a schema-4 trace still renders.
const stopReason = T.stop_reason || null;
const partial = stopReason ? stopReason.kind !== "completed" : !!T.partial;
if (partial) {
  let why = "";
  if (stopReason && stopReason.kind === "interrupted") why = " (interrupted by Ctrl-C)";
  else if (stopReason && stopReason.kind === "max-paths") why = ` (--max-paths ${stopReason.limit} reached)`;
  addChip("fail", "PARTIAL — exploration stopped early" + why);
}

// ---- verdict toggles ----------------------------------------------------
const VERDICTS = ["verified", "unreachable", "goal-fails", "inconclusive", "pruned"];
const active = new Set(VERDICTS);
const vt = document.getElementById("vtoggles");
VERDICTS.forEach(k => {
  const lab = el("label");
  const cb = el("input");
  cb.type = "checkbox";
  cb.checked = true;
  cb.onchange = () => { cb.checked ? active.add(k) : active.delete(k); applyFilter(); };
  lab.appendChild(cb);
  lab.appendChild(document.createTextNode(" " + k));
  vt.appendChild(lab);
});

// ---- tree ---------------------------------------------------------------
const chainSpan = (steps, terminal, pruned) => {
  const c = el("span", "chain");
  steps.forEach(st => {
    c.appendChild(document.createTextNode(`L${st.label} `));
    c.appendChild(el("span", "dec", st.decision));
    c.appendChild(document.createTextNode(" → "));
  });
  if (pruned) {
    c.appendChild(document.createTextNode(`L${terminal.label} `));
    c.appendChild(el("span", "dec", "✂ branch pruned"));
  } else {
    c.appendChild(document.createTextNode(`L${terminal.label} ${terminal.is_abort ? "abort" : "return"}`));
  }
  return c;
};

let selected = null;
const tree = document.getElementById("tree");

const rpRow = (lp, rp) => {
  const k = verdictKind(rp.verdict);
  const row = el("div", "rp");
  row._lp = lp; row._rp = rp; row._vk = k;
  row.appendChild(el("span", "twist", ""));
  row.appendChild(el("span", "pid", "#" + rp.id));
  row.appendChild(chainSpan(rp.steps, rp.terminal, rp.pruned));
  const bt = rp.pruned ? `pruned at L${rp.terminal.label} (unsat)` : badgeText(k);
  row.appendChild(el("span", "badge " + badgeClass(k), bt));
  row.onclick = () => select(row, lp, rp);
  return row;
};

T.left_paths.forEach(lp => {
  const prunes = (lp.pruned_branches || []).map(pb => prunedRow(pb, lp.id));
  const kids = lp.reachable ? lp.right_paths.concat(prunes) : [];
  const node = el("div", "node lp");
  node._lp = lp;
  // Story 13: a left path with a wall of right paths opens collapsed, so a big
  // run reads as an overview instead of a 100-row scroll. Re-toggling is cheap;
  // nothing here is persisted.
  if (kids.length > 25) node.classList.add("collapsed");
  const head = el("div", "lp-head");
  const twist = el("span", "twist", kids.length ? (node.classList.contains("collapsed") ? "▸" : "▾") : "");
  head.appendChild(twist);
  head.appendChild(el("span", "pid", "#" + lp.id));
  head.appendChild(chainSpan(lp.steps, lp.terminal));

  if (!lp.reachable) {
    head.appendChild(el("span", "badge pruned", "pruned (unsat)"));
  } else {
    const counts = {};
    kids.forEach(rp => {
      const k = verdictKind(rp.verdict);
      counts[k] = (counts[k] || 0) + 1;
    });
    const summ = Object.entries(counts).map(([k, n]) => `${n} ${badgeText(k)}`).join(" · ");
    head.appendChild(el("span", "mini", summ || "no right paths"));
  }

  head.onclick = e => {
    if (e.target === twist) {
      node.classList.toggle("collapsed");
      if (kids.length) twist.textContent = node.classList.contains("collapsed") ? "▸" : "▾";
      return;
    }
    select(node, lp, null);
  };
  node.appendChild(head);

  if (kids.length) {
    const list = el("div", "rp-list");
    kids.forEach(rp => list.appendChild(rpRow(lp, rp)));
    node.appendChild(list);
  }
  tree.appendChild(node);
});

// Left branches cut before any terminal below them — top-level rows.
(T.left_pruned_branches || []).forEach(pb => {
  const rp = prunedRow(pb, null);
  const node = el("div", "node lp");
  node._lp = null; node._leftPrune = rp;
  const head = el("div", "lp-head");
  head.appendChild(el("span", "twist", ""));
  head.appendChild(el("span", "pid", "#" + rp.id));
  head.appendChild(chainSpan(rp.steps, rp.terminal, true));
  head.appendChild(el("span", "badge pruned", `pruned at L${rp.terminal.label} (unsat)`));
  head.onclick = () => select(node, rp, null);
  node.appendChild(head);
  tree.appendChild(node);
});

function select(domNode, lp, rp) {
  if (selected) selected.classList.remove("sel");
  selected = domNode;
  selected.classList.add("sel");
  renderDetail(lp, rp);
}

// ---- tree collapse / expand all (story 13; not persisted — cheap to redo) ---
function setAllNodes(collapsed) {
  tree.querySelectorAll(".node.lp").forEach(node => {
    const hasKids = !!node.querySelector(".rp-list");
    const twist = node.querySelector(".lp-head > .twist");
    node.classList.toggle("collapsed", collapsed);
    if (twist && hasKids) twist.textContent = collapsed ? "▸" : "▾";
  });
}
document.getElementById("tree-collapse").onclick = () => setAllNodes(true);
document.getElementById("tree-expand").onclick = () => setAllNodes(false);

// ---- detail -----------------------------------------------------------
const detail = document.getElementById("detail");

// `localStorage` can *throw* (not just return null) on a file:// page in a
// browser with site data blocked — every access is guarded (story 13).
function lsGet(k) { try { return localStorage.getItem(k); } catch (e) { return null; } }
function lsSet(k, v) { try { localStorage.setItem(k, v); } catch (e) {} }
const secKey = title => "domino.debug.sec." + title;

function listingBlock(text, steps, terminal) {
  const hi = new Set(steps.map(s => s.label));
  const wrap = el("div", "listing");
  const pre = el("pre");
  pre.appendChild(wrap);
  const lines = text.split("\n");
  lines.forEach((line, i) => {
    const n = i + 1;
    const row = el("div", "row" + (hi.has(n) ? " hi" : "") + (terminal && n === terminal.label ? " term" : ""));
    row.appendChild(el("span", "n", String(n)));
    row.appendChild(el("span", "c", line));
    // Centring now happens when the section opens (see `sec`), not on a
    // render-time setTimeout, so a collapsed listing never scrolls the pane.
    if (terminal && n === terminal.label) pre._termRow = row;
    wrap.appendChild(row);
  });
  return pre;
}

// A collapsible detail section. `title` keys its open/closed state in
// localStorage, so the choice persists across selections and reloads; `meta`
// shows on the summary line so a closed section still says how big it is.
function sec(title, body, defaultOpen, meta) {
  const d = el("details", "sec");
  const stored = lsGet(secKey(title));
  d.open = stored === "1" ? true : stored === "0" ? false : !!defaultOpen;

  const sum = el("summary");
  sum.appendChild(el("span", "sec-title", title));
  if (meta) sum.appendChild(el("span", "sec-meta", meta));
  d.appendChild(sum);

  const wrap = el("div", "sec-body");
  wrap.appendChild(body);
  d.appendChild(wrap);

  d.addEventListener("toggle", () => lsSet(secKey(title), d.open ? "1" : "0"));

  // If this section holds a listing, centre its terminal line when it opens.
  const pre = body.tagName === "PRE" ? body
    : (body.querySelector ? body.querySelector("pre") : null);
  const centre = () => { if (d.open && pre && pre._termRow) pre._termRow.scrollIntoView({ block: "center" }); };
  d.addEventListener("toggle", centre);
  if (d.open && pre && pre._termRow) requestAnimationFrame(centre);

  return d;
}

// Expand all / Collapse all for the current detail pane (persists each choice).
function addSecToolbar() {
  const bar = el("div", "sectoolbar");
  const setAll = open => detail.querySelectorAll("details.sec").forEach(d => {
    d.open = open;
    const t = d.querySelector(".sec-title");
    if (t) lsSet(secKey(t.textContent), open ? "1" : "0");
  });
  const mk = (label, open) => {
    const b = el("button", null, label);
    b.type = "button";
    b.onclick = () => setAll(open);
    return b;
  };
  bar.appendChild(mk("Expand all", true));
  bar.appendChild(mk("Collapse all", false));
  detail.appendChild(bar);
}

function stepsTable(steps, sites) {
  const tbl = el("table", "steps");
  steps.forEach(st => {
    const tr = el("tr");
    tr.appendChild(el("td", "l", "L" + st.label));
    tr.appendChild(el("td", "d", st.decision));
    const site = sites && sites[st.label];
    tr.appendChild(el("td", "s", (site && site.line) || st.line || ""));
    tbl.appendChild(tr);
  });
  return tbl;
}

// ---- section metas + SMT / claim-assertion bodies (story 13) ---------------
const termWord = t => (t.is_abort ? "abort" : "return");
const plural = (n, w) => `${n} ${w}${n === 1 ? "" : "s"}`;

const pathMeta = (steps, terminal) =>
  `${plural(steps.length, "step")} → L${terminal.label} ${termWord(terminal)}`;
const listingMeta = (text, steps) =>
  `${text.split("\n").length} lines · ${steps.length} on this path`;
const smtMeta = (lp, rp) =>
  `${plural(lp.smt.length + (rp ? rp.smt.length : 0), "assertion")} + base frame`;

// Does a self-contained `smt/<L>/<R>.smt2` exist for this pair?
function smtOnDisk(rp) {
  const mode = T.options && T.options.smt;
  if (!mode || mode === "none" || !rp) return false;
  if (mode === "all" || mode === "deltas") return true;
  const k = verdictKind(rp.verdict);
  return k === "goal-fails" || k === "inconclusive";
}

// The runnable query for a pair: base frame, both path deltas, the vacuity
// check-sat, then the negated goal and its check-sat — the sequence `domino
// debug` sent the solver, and what `smt/<L>/<R>.smt2` records.
function pairQueryText(lp, rp) {
  const parts = [];
  if (T.base_frame_smt) parts.push(T.base_frame_smt);
  lp.smt.forEach(l => parts.push(l));
  if (rp) rp.smt.forEach(l => parts.push(l));
  parts.push("(check-sat)");
  if (T.goal_smt) parts.push("(push 1)", T.goal_smt, "(check-sat)", "(pop 1)");
  return parts.join("\n") + "\n";
}

function execCopyFallback(text) {
  try {
    const ta = el("textarea");
    ta.value = text;
    ta.style.position = "fixed";
    ta.style.opacity = "0";
    document.body.appendChild(ta);
    ta.focus();
    ta.select();
    const ok = document.execCommand("copy");
    document.body.removeChild(ta);
    return ok;
  } catch (e) { return false; }
}

function copyBtn(label, getText) {
  const b = el("button", "copy-btn", label);
  b.type = "button";
  b.onclick = () => {
    const flash = () => { b.textContent = "copied"; setTimeout(() => { b.textContent = label; }, 1200); };
    let text = "";
    try { text = getText(); } catch (e) { return; }
    try {
      if (navigator.clipboard && navigator.clipboard.writeText) {
        navigator.clipboard.writeText(text).then(flash, () => { if (execCopyFallback(text)) flash(); });
      } else if (execCopyFallback(text)) {
        flash();
      }
    } catch (e) { /* silent — a copy failure must never break the pane */ }
  };
  return b;
}

function smtBlock(lp, rp) {
  const wrap = el("div");
  wrap.appendChild(copyBtn("Copy runnable query", () => pairQueryText(lp, rp)));
  if (rp && smtOnDisk(rp)) {
    wrap.appendChild(el("div", "assertion-note",
      `also on disk: smt/${lp.id}/${rp.id.split(".").pop()}.smt2`));
  }
  const base = el("details");
  base.appendChild(el("summary", null, "base frame (asserted once at level 0)"));
  base.appendChild((() => { const p = el("pre"); p.textContent = T.base_frame_smt || "(none)"; return p; })());
  wrap.appendChild(base);
  wrap.appendChild(el("div", "path-sub", "left path #" + lp.id));
  const lpre = el("pre");
  lpre.textContent = lp.smt.join("\n");
  wrap.appendChild(lpre);
  if (rp) {
    wrap.appendChild(el("div", "path-sub", "right path #" + rp.id));
    const rpre = el("pre");
    rpre.textContent = rp.smt.join("\n");
    wrap.appendChild(rpre);
  }
  return wrap;
}

// The actual claim assertion the solver was asked about at this terminal pair.
function claimAssertionSec(lp, rp) {
  const k = verdictKind(rp.verdict);
  const tw = termWord(rp.terminal);
  const wrap = el("div");

  wrap.appendChild(el("div", "assertion-note",
    `checked after right path #${rp.id} terminates at L${rp.terminal.label} (${tw})`));
  wrap.appendChild(copyBtn("Copy runnable query", () => pairQueryText(lp, rp)));

  const pre = el("pre");
  if (k === "unreachable") {
    pre.textContent =
      "; the vacuity (check-sat) was `unsat` — this (left, right) pair cannot\n" +
      "; occur, so the negated goal below was never checked.\n\n" +
      (T.goal_smt || "(goal not recorded)");
  } else {
    pre.textContent =
      "(check-sat)          ; vacuity — is this (left, right) pair reachable?\n\n" +
      (T.goal_smt || "(goal not recorded)") + "\n" +
      "(check-sat)          ; the negated claim goal";
  }
  wrap.appendChild(pre);

  const outcome = {
    "verified": "vacuity `sat`, goal check `unsat` — the claim holds on this pair.",
    "unreachable": "vacuity check `unsat` — the pair is unreachable; the goal was not checked.",
    "goal-fails": "goal check `sat` — the claim FAILS; the Model section above has the witness.",
    "inconclusive": "goal check `unknown` — timed out or undecided within the budget.",
  }[k] || "";
  const out = el("div", "assertion-outcome");
  out.appendChild(el("span", "badge " + badgeClass(k), badgeText(k)));
  out.appendChild(document.createTextNode(" " + outcome));
  wrap.appendChild(out);

  return sec("Claim assertion", wrap, true, `#${rp.id} → L${rp.terminal.label} ${tw}`);
}

function renderDetail(lp, rp) {
  detail.innerHTML = "";

  // A top-level left-branch prune is passed as `lp` with `.pruned`.
  if (lp && lp.pruned && !rp) {
    detail.appendChild(el("h2", null, "Left branch prune #" + lp.id));
    detail.appendChild(el("div", "path-sub",
      `cut at L${lp.terminal.label} ${lp.decision} — prefix unsat, subtree not explored`));
    addSecToolbar();
    detail.appendChild(sec("Path — left", stepsTable(lp.steps, T.left_sites), true,
      pathMeta(lp.steps, lp.terminal)));
    detail.appendChild(sec("Listing — left (" + T.left_game + ")",
      listingBlock(T.left_listing, lp.steps, lp.terminal), false,
      listingMeta(T.left_listing, lp.steps)));
    return;
  }

  const isRight = !!rp;
  const node = rp || lp;
  const rightPruned = isRight && rp.pruned;
  detail.appendChild(el("h2", null,
    (rightPruned ? "Right branch prune #" : isRight ? "Right path #" : "Left path #") + node.id));

  const sub = el("div", "path-sub");
  if (rightPruned) {
    sub.textContent = `under left path #${lp.id} — cut at L${rp.terminal.label} ${rp.decision}, prefix unsat`;
  } else if (isRight) {
    sub.textContent = `under left path #${lp.id} — verdict: ${badgeText(verdictKind(rp.verdict))}`;
  } else {
    sub.textContent = lp.reachable
      ? `${lp.right_paths.length} right path(s) explored`
      : "unreachable — pruned by check-left, right side not explored";
  }
  detail.appendChild(sub);

  addSecToolbar();

  // The question and the answer come before the bulk (story 13 reorder).
  detail.appendChild(sec("Path — left", stepsTable(lp.steps, T.left_sites), true,
    pathMeta(lp.steps, lp.terminal)));
  if (isRight) detail.appendChild(sec("Path — right", stepsTable(rp.steps, T.right_sites), true,
    pathMeta(rp.steps, rp.terminal)));

  // A right-branch prune never reached a terminal: no claim assertion, no SMT.
  if (rightPruned) {
    detail.appendChild(sec("Listing — left (" + T.left_game + ")",
      listingBlock(T.left_listing, lp.steps, lp.terminal), false,
      listingMeta(T.left_listing, lp.steps)));
    detail.appendChild(sec("Listing — right (" + T.right_game + ")",
      listingBlock(T.right_listing, rp.steps, rp.terminal), false,
      listingMeta(T.right_listing, rp.steps)));
    return;
  }

  if (isRight) detail.appendChild(claimAssertionSec(lp, rp));

  if (isRight && rp.model_smt) {
    const p = el("pre");
    p.textContent = rp.model_smt;
    detail.appendChild(sec("Model", p, true));
  }

  detail.appendChild(sec("SMT asserted", smtBlock(lp, isRight ? rp : null), false,
    smtMeta(lp, isRight ? rp : null)));

  detail.appendChild(sec("Listing — left (" + T.left_game + ")",
    listingBlock(T.left_listing, lp.steps, lp.terminal), false,
    listingMeta(T.left_listing, lp.steps)));
  if (isRight) detail.appendChild(sec("Listing — right (" + T.right_game + ")",
    listingBlock(T.right_listing, rp.steps, rp.terminal), false,
    listingMeta(T.right_listing, rp.steps)));
}

// ---- filter ---------------------------------------------------------
const q = document.getElementById("q");
q.oninput = applyFilter;

function applyFilter() {
  const needle = q.value.trim().toLowerCase();
  const matchText = (steps, terminal, id) => {
    if (!needle) return true;
    if (("#" + id).includes(needle)) return true;
    if (steps.some(st => (st.line || "").toLowerCase().includes(needle)
                      || st.decision.includes(needle))) return true;
    return (terminal.line || "").toLowerCase().includes(needle);
  };

  tree.querySelectorAll(".lp").forEach(node => {
    const lp = node._lp;

    // top-level left-branch prune row
    if (!lp) {
      const rp = node._leftPrune;
      const show = active.has("pruned") && matchText(rp.steps, rp.terminal, rp.id);
      node.classList.toggle("hidden", !show);
      return;
    }

    let anyChild = false;
    node.querySelectorAll(".rp").forEach(row => {
      const rp = row._rp;
      const vOk = active.has(row._vk);
      const tOk = matchText(rp.steps, rp.terminal, rp.id) || matchText(lp.steps, lp.terminal, lp.id);
      const show = vOk && tOk;
      row.classList.toggle("hidden", !show);
      if (show) anyChild = true;
    });
    const kidCount = lp.right_paths.length + (lp.pruned_branches || []).length;
    let showNode;
    if (!lp.reachable) {
      showNode = active.has("pruned") && matchText(lp.steps, lp.terminal, lp.id);
    } else if (kidCount === 0) {
      showNode = matchText(lp.steps, lp.terminal, lp.id);
    } else {
      showNode = anyChild;
    }
    node.classList.toggle("hidden", !showNode);
  });
}
applyFilter();
</script>
</body>
</html>
"##;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::debug::driver::{
        DebugRun, LeftPath, OptionsView, PrunedBranch, RightPath, SiteView, StepView, StopReason,
        Summary, TerminalView, Verdict, TRACE_SCHEMA,
    };
    use std::collections::BTreeMap;
    use std::time::Duration;

    fn summary_of(run: &DebugRun, elapsed: Duration) -> String {
        let dir = tempfile::tempdir().unwrap();
        let p = write_summary(run, elapsed, dir.path()).unwrap();
        assert_eq!(p.file_name().unwrap(), "summary.txt");
        std::fs::read_to_string(&p).unwrap()
    }

    fn synthetic_run(out_dir: &str) -> DebugRun {
        let mut left_sites = BTreeMap::new();
        left_sites.insert(
            12usize,
            SiteView {
                kind: "branch".into(),
                line: "if (k != bot) {".into(),
                pkg_inst: "MON_CCA_PKE".into(),
                oracle: "PKDEC".into(),
                depth: 1,
            },
        );

        DebugRun {
            schema: TRACE_SCHEMA,
            theorem: "demo".into(),
            proofstep: 0,
            left_game: "Game_L".into(),
            right_game: "Game_R".into(),
            oracle: "O".into(),
            claim: "same-output".into(),
            admitted: false,
            out_dir: out_dir.into(),
            options: OptionsView {
                check_left: false,
                check_right: true,
                timeout_ms: None,
                max_paths: Some(1000),
                smt: crate::debug::smtout::SmtOut::Failures,
                transcript: false,
            },
            base_frame_smt: "(declare-const x Int)".into(),
            goal_smt: "(assert (not (= x 0)))".into(),
            left_listing: "OracleO {\n    if (k != bot) {\n    return k\n}".into(),
            right_listing: "OracleO {\n    return k\n}".into(),
            left_sites,
            right_sites: BTreeMap::new(),
            left_paths: vec![LeftPath {
                id: "1".into(),
                steps: vec![StepView {
                    label: 2,
                    line: "if (k != bot) {".into(),
                    decision: "then".into(),
                }],
                terminal: TerminalView {
                    label: 3,
                    line: "return k".into(),
                    is_abort: false,
                },
                reachable: true,
                smt: vec!["(assert true)".into()],
                pruned_branches: vec![PrunedBranch {
                    id: "1.p1".into(),
                    steps: vec![StepView {
                        label: 2,
                        line: "if (k != bot) {".into(),
                        decision: "else".into(),
                    }],
                    label: 2,
                    line: "if (k != bot) {".into(),
                    decision: "else".into(),
                }],
                right_paths: vec![
                    RightPath {
                        id: "1.1".into(),
                        steps: vec![],
                        terminal: TerminalView {
                            label: 2,
                            line: "return k".into(),
                            is_abort: false,
                        },
                        verdict: Verdict::Verified,
                        model_smt: None,
                        smt: vec!["(assert true)".into()],
                    },
                    RightPath {
                        id: "1.2".into(),
                        steps: vec![],
                        terminal: TerminalView {
                            label: 2,
                            line: "return k".into(),
                            is_abort: false,
                        },
                        verdict: Verdict::GoalFails {
                            model: "models/1.2.smt2".into(),
                        },
                        model_smt: Some("(define-fun x () Int 0)".into()),
                        smt: vec!["(assert false)".into()],
                    },
                ],
            }],
            left_pruned_branches: vec![PrunedBranch {
                id: "p1".into(),
                steps: vec![StepView {
                    label: 2,
                    line: "if (k != bot) {".into(),
                    decision: "then".into(),
                }],
                label: 2,
                line: "if (k != bot) {".into(),
                decision: "then".into(),
            }],
            summary: Summary {
                left_paths: 1,
                left_pruned: 0,
                left_pruned_branches: 1,
                right_paths: 2,
                right_pruned_branches: 1,
                sibling_shortcuts: 0,
                verified: 1,
                unreachable: 0,
                goal_fails: 1,
                inconclusive: 0,
            },
            left_syntactic: 3,
            stop_reason: StopReason::Completed,
        }
    }

    #[test]
    fn trace_json_round_trips_and_is_deterministic() {
        let dir = tempfile::tempdir().unwrap();
        let run = synthetic_run("/some/absolute/path");

        let p1 = write_trace_json(&run, dir.path()).unwrap();
        let first = std::fs::read_to_string(&p1).unwrap();
        let second_run = synthetic_run("/a/completely/different/path");
        write_trace_json(&second_run, dir.path()).unwrap();
        let second = std::fs::read_to_string(&p1).unwrap();

        assert_eq!(first, second, "trace.json must not depend on out_dir");
        assert!(!first.contains("absolute/path"), "out_dir must be skipped");

        let parsed: serde_json::Value = serde_json::from_str(&first).unwrap();
        assert_eq!(parsed["schema"], 6);
        assert_eq!(parsed["options"]["max_paths"], 1000);
        assert_eq!(parsed["goal_smt"], "(assert (not (= x 0)))");
        assert_eq!(parsed["left_paths"][0]["right_paths"][1]["verdict"]["kind"], "goal-fails");
        assert_eq!(parsed["summary"]["goal_fails"], 1);
        assert_eq!(parsed["left_sites"]["12"]["kind"], "branch");
        assert_eq!(parsed["left_pruned_branches"][0]["id"], "p1");
        assert_eq!(parsed["left_paths"][0]["pruned_branches"][0]["id"], "1.p1");
        assert_eq!(parsed["summary"]["right_pruned_branches"], 1);
    }

    #[test]
    fn unlimited_max_paths_serialises_as_null() {
        let dir = tempfile::tempdir().unwrap();
        let mut run = synthetic_run("/x");
        run.options.max_paths = None;
        let p = write_trace_json(&run, dir.path()).unwrap();
        let parsed: serde_json::Value =
            serde_json::from_str(&std::fs::read_to_string(&p).unwrap()).unwrap();
        assert_eq!(parsed["schema"], 6);
        assert!(parsed["options"]["max_paths"].is_null());
    }

    #[test]
    fn html_is_self_contained_and_embeds_the_trace() {
        let dir = tempfile::tempdir().unwrap();
        let run = synthetic_run("/x");
        let p = write_html(&run, dir.path()).unwrap();
        let html = std::fs::read_to_string(&p).unwrap();

        assert!(html.starts_with("<!doctype html>"));
        assert!(!html.contains("http://") && !html.contains("https://"),
            "no external references allowed");
        assert!(html.contains("application/json\" id=\"trace\""));
        assert!(html.contains("goal-fails"));
        // the embedded JSON must still parse after `<` escaping
        let start = html.find("id=\"trace\">").unwrap() + "id=\"trace\">".len();
        let end = html[start..].find("</script>").unwrap() + start;
        let _: serde_json::Value = serde_json::from_str(&html[start..end]).unwrap();
    }

    #[test]
    fn html_is_byte_identical_across_runs() {
        let dir = tempfile::tempdir().unwrap();
        let a = write_html(&synthetic_run("/one"), dir.path()).unwrap();
        let first = std::fs::read_to_string(&a).unwrap();
        write_html(&synthetic_run("/two"), dir.path()).unwrap();
        let second = std::fs::read_to_string(&a).unwrap();
        assert_eq!(first, second);
    }

    // ---- story 12: summary.txt -----------------------------------------

    #[test]
    fn summary_txt_completed_run_shape() {
        let txt = summary_of(&synthetic_run("/x"), Duration::from_secs(64));
        assert!(txt.starts_with("domino debug — summary\n======================\n"));
        assert!(txt.contains("\nstatus        COMPLETE — all paths explored\n"), "{txt}");
        assert!(txt.contains("\nelapsed       1m 04s\n"), "{txt}");
        // options line is greppable and stable
        assert!(
            txt.contains("options       check-left=off check-right=on timeout=none max-paths=1000 jobs=1 smt=failures\n"),
            "{txt}"
        );
        // verdict counts equal run.summary
        assert!(txt.contains("  verified      1\n"), "{txt}");
        assert!(txt.contains("  GOAL FAILS    1\n"), "{txt}");
        assert!(txt.contains("  inconclusive  0\n"), "{txt}");
        // the one goal-fail pair is listed with its id + model
        assert!(txt.contains("goal failures\n"), "{txt}");
        assert!(txt.contains("#1.2"), "{txt}");
        assert!(txt.contains("models/1.2.smt2"), "{txt}");
        // left-path line carries the syntactic denominator
        assert!(txt.contains("explored of 3 syntactic"), "{txt}");
        // no empty inconclusive block
        assert!(!txt.contains("\ninconclusive\n"), "{txt}");
    }

    #[test]
    fn summary_txt_stop_reason_status_lines() {
        let mut run = synthetic_run("/x");
        run.stop_reason = StopReason::MaxPaths { limit: 20 };
        assert!(summary_of(&run, Duration::from_secs(1))
            .contains("status        STOPPED EARLY (--max-paths 20 reached)\n"));

        run.stop_reason = StopReason::Interrupted;
        assert!(summary_of(&run, Duration::from_secs(1))
            .contains("status        STOPPED EARLY (interrupted by Ctrl-C)\n"));
    }

    #[test]
    fn summary_txt_admitted_is_header_plus_status() {
        let mut run = synthetic_run("/x");
        run.admitted = true;
        let txt = summary_of(&run, Duration::from_secs(1));
        assert!(txt.contains("status        ADMITTED — nothing to check\n"), "{txt}");
        assert!(!txt.contains("\nverdicts\n"), "{txt}");
        assert!(!txt.contains("\npaths\n"), "{txt}");
    }

    #[test]
    fn summary_txt_differs_only_in_the_elapsed_line() {
        let run = synthetic_run("/x");
        let a = summary_of(&run, Duration::from_secs(3));
        let b = summary_of(&run, Duration::from_secs(9999));
        let diffs: Vec<_> = a
            .lines()
            .zip(b.lines())
            .filter(|(x, y)| x != y)
            .collect();
        assert_eq!(a.lines().count(), b.lines().count());
        assert_eq!(diffs.len(), 1, "{diffs:?}");
        assert!(diffs[0].0.starts_with("elapsed"), "{diffs:?}");
    }

    #[test]
    fn summary_txt_goal_fail_ids_match_the_trace() {
        let dir = tempfile::tempdir().unwrap();
        let run = synthetic_run("/x");
        let txt = summary_of(&run, Duration::from_secs(1));
        let tp = write_trace_json(&run, dir.path()).unwrap();
        let parsed: serde_json::Value =
            serde_json::from_str(&std::fs::read_to_string(&tp).unwrap()).unwrap();

        let mut trace_ids: Vec<String> = Vec::new();
        for lp in parsed["left_paths"].as_array().unwrap() {
            for rp in lp["right_paths"].as_array().unwrap() {
                if rp["verdict"]["kind"] == "goal-fails" {
                    trace_ids.push(rp["id"].as_str().unwrap().to_string());
                }
            }
        }
        assert_eq!(trace_ids, vec!["1.2".to_string()]);
        for id in &trace_ids {
            assert!(txt.contains(&format!("#{id}")), "summary must list {id}:\n{txt}");
        }
        assert_eq!(parsed["stop_reason"]["kind"], "completed");
        assert!(parsed.get("partial").is_none(), "partial must be gone from trace.json");
    }
}
