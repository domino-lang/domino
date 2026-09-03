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

use std::path::{Path, PathBuf};

use crate::debug::driver::DebugRun;

/// Write `trace.json` into `out_dir`. Returns the path written.
pub fn write_trace_json(run: &DebugRun, out_dir: &Path) -> std::io::Result<PathBuf> {
    let path = out_dir.join("trace.json");
    let mut json = serde_json::to_string_pretty(run)
        .map_err(std::io::Error::other)?;
    json.push('\n');
    std::fs::write(&path, json)?;
    Ok(path)
}

/// Write both `trace.json` and `index.html` for the run so far.
///
/// Called after every left path (story 09's incremental flush, so a `Ctrl-C` or
/// `--max-paths` leaves a usable partial trace + viewer) and once at the end.
/// Both files truncate-write, so an intermediate flush is simply overwritten by
/// the next one; the *final* bytes are byte-identical to a single end-of-run
/// write (story 07's determinism guarantee — no timestamps enter `DebugRun`).
/// Errors are surfaced: a failing flush is a real problem (out of disk, bad
/// path).
pub fn flush(run: &DebugRun, out_dir: &Path) -> std::io::Result<()> {
    write_trace_json(run, out_dir)?;
    write_html(run, out_dir)?;
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
.sec { margin-bottom: 18px; }
.sec > h3 {
  font: 12px/1 var(--mono);
  text-transform: uppercase;
  letter-spacing: .05em;
  color: var(--fg-muted);
  margin: 0 0 6px;
}
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
 ["max-paths", o.max_paths == null ? "unlimited" : o.max_paths]].forEach(([k, val]) => {
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
if (T.partial) addChip("fail", "PARTIAL — exploration stopped early");

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
  const head = el("div", "lp-head");
  const twist = el("span", "twist", kids.length ? "▾" : "");
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
    if (e.target === twist) { node.classList.toggle("collapsed"); return; }
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

// ---- detail -----------------------------------------------------------
const detail = document.getElementById("detail");

function listingBlock(text, steps, terminal) {
  const hi = new Set(steps.map(s => s.label));
  const wrap = el("div", "listing");
  const pre = el("pre");
  pre.appendChild(wrap);
  const lines = text.split("\n");
  let termRow = null;
  lines.forEach((line, i) => {
    const n = i + 1;
    const row = el("div", "row" + (hi.has(n) ? " hi" : "") + (terminal && n === terminal.label ? " term" : ""));
    row.appendChild(el("span", "n", String(n)));
    row.appendChild(el("span", "c", line));
    if (terminal && n === terminal.label) termRow = row;
    wrap.appendChild(row);
  });
  if (termRow) setTimeout(() => termRow.scrollIntoView({ block: "center" }), 0);
  return pre;
}

function sec(title, body) {
  const d = el("div", "sec");
  d.appendChild(el("h3", null, title));
  d.appendChild(body);
  return d;
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

function renderDetail(lp, rp) {
  detail.innerHTML = "";

  // A top-level left-branch prune is passed as `lp` with `.pruned`.
  if (lp && lp.pruned && !rp) {
    detail.appendChild(el("h2", null, "Left branch prune #" + lp.id));
    detail.appendChild(el("div", "path-sub",
      `cut at L${lp.terminal.label} ${lp.decision} — prefix unsat, subtree not explored`));
    detail.appendChild(sec("Path — left", stepsTable(lp.steps, T.left_sites)));
    detail.appendChild(sec("Listing — left (" + T.left_game + ")",
      listingBlock(T.left_listing, lp.steps, lp.terminal)));
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

  // Path
  detail.appendChild(sec("Path — left", stepsTable(lp.steps, T.left_sites)));
  if (isRight) detail.appendChild(sec("Path — right", stepsTable(rp.steps, T.right_sites)));

  // Listing
  detail.appendChild(sec("Listing — left (" + T.left_game + ")",
    listingBlock(T.left_listing, lp.steps, lp.terminal)));
  if (isRight) {
    detail.appendChild(sec("Listing — right (" + T.right_game + ")",
      listingBlock(T.right_listing, rp.steps, rp.terminal)));
  }
  if (rightPruned) return;

  // SMT
  const smtWrap = el("div");
  const base = el("details");
  base.appendChild(el("summary", null, "base frame (asserted once at level 0)"));
  base.appendChild((() => { const p = el("pre"); p.textContent = T.base_frame_smt || "(none)"; return p; })());
  smtWrap.appendChild(base);
  const lpre = el("pre");
  lpre.textContent = lp.smt.join("\n");
  smtWrap.appendChild(el("div", "path-sub", "left path #" + lp.id));
  smtWrap.appendChild(lpre);
  if (isRight) {
    smtWrap.appendChild(el("div", "path-sub", "right path #" + rp.id));
    const rpre = el("pre");
    rpre.textContent = rp.smt.join("\n");
    smtWrap.appendChild(rpre);
  }
  detail.appendChild(sec("SMT asserted", smtWrap));

  // Model
  if (isRight && rp.model_smt) {
    const p = el("pre");
    p.textContent = rp.model_smt;
    detail.appendChild(sec("Model", p));
  }
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
        DebugRun, LeftPath, OptionsView, PrunedBranch, RightPath, SiteView, StepView, Summary,
        TerminalView, Verdict, TRACE_SCHEMA,
    };
    use std::collections::BTreeMap;

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
            },
            base_frame_smt: "(declare-const x Int)".into(),
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
            partial: false,
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
        assert_eq!(parsed["schema"], 3);
        assert_eq!(parsed["options"]["max_paths"], 1000);
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
        assert_eq!(parsed["schema"], 3);
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
}
