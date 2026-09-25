// SPDX-License-Identifier: MIT OR Apache-2.0

//! The HTML of the live translation page (story 28); see [`super`] for what it shows and
//! what it embeds. Self-contained: inline CSS and JS, no network.

use std::collections::BTreeMap;
use std::fmt::Write as _;

use super::{GoalTexts, Live, NodeRec, RunState, StepStatus};

const CSS: &str = r##"
:root { --bg:#fff; --fg:#1b1f24; --dim:#68707a; --line:#d5d9de; --card:#f5f6f8; --ok:#1a7f37; --bad:#c62828;
  --warn:#9a6700; --acc:#0b62d6; --sel:#fff4c2; }
@media (prefers-color-scheme: dark) { :root:not([data-theme="light"]) { --bg:#14171b; --fg:#e4e7eb; --dim:#98a1ac;
  --line:#343a42; --card:#1d2126; --ok:#56d364; --bad:#ff7b72; --warn:#e3b341; --acc:#79b8ff; --sel:#3a3320; } }
body { margin:0; background:var(--bg); color:var(--fg); font:14px/1.45 system-ui,sans-serif; }
main, header, footer { max-width:1100px; margin:0 auto; padding:0 16px; }
header { padding-top:16px; }
h1 { font-size:20px; margin:0 0 8px; } h2 { font-size:16px; margin:24px 0 8px; }
code, pre { font-family:ui-monospace,Menlo,monospace; font-size:12.5px; }
.chips span, .chip { display:inline-block; border:1px solid var(--line); border-radius:10px; padding:0 8px; margin:0 4px 4px 0;
  color:var(--dim); background:var(--card); }
.chip.active { color:var(--acc); border-color:var(--acc); } .chip.done { color:var(--ok); }
.pending { border:1px solid var(--warn); border-radius:6px; padding:8px 10px; margin:10px 0; background:var(--card); }
.spinner { display:inline-block; width:10px; height:10px; border:2px solid var(--warn); border-right-color:transparent;
  border-radius:50%; animation:spin 1s linear infinite; vertical-align:-1px; margin-right:6px; }
@keyframes spin { to { transform:rotate(360deg); } }
.banner { border-radius:6px; padding:8px 10px; margin:10px 0; background:var(--card); border:1px solid var(--line); }
.banner.failed { border-color:var(--bad); color:var(--bad); }
table { border-collapse:collapse; } td, th { padding:2px 12px 2px 0; text-align:left; }
details.oracle, details.node { border-left:2px solid var(--line); margin:4px 0 4px 8px; padding-left:8px; }
details.oracle { border-left:none; margin-left:0; padding-left:0; }
summary { cursor:pointer; padding:2px 0; }
.nid { font-weight:600; } .kind, .ids { color:var(--dim); }
.st-open { color:var(--warn); } .st-closed { color:var(--ok); } .st-admitted { color:var(--bad); }
ol.steps { list-style:none; margin:2px 0 4px; padding:0; }
li.step { padding:1px 4px; border-radius:4px; cursor:pointer; }
li.step:hover { background:var(--card); } li.step.sel, .flash { background:var(--sel); }
.badge { font-size:11px; border-radius:8px; padding:0 6px; margin-right:6px; border:1px solid var(--line); }
.b-accepted { color:var(--ok); } .b-failed { color:var(--bad); } .b-timeout { color:var(--warn); } .b-undone { color:var(--dim); }
li.step.undone code { text-decoration:line-through; color:var(--dim); }
.err { color:var(--bad); } .t { color:var(--dim); font-size:11px; margin-left:6px; }
.detail { display:none; margin:4px 0 8px 12px; } li.sel > .detail { display:block; }
pre { background:var(--card); border:1px solid var(--line); border-radius:4px; padding:6px 8px; overflow:auto; max-height:420px;
  white-space:pre-wrap; margin:4px 0; }
.admit { border:1px solid var(--bad); border-radius:4px; padding:2px 8px; margin:3px 0; }
.note { color:var(--dim); } a { color:var(--acc); }
footer { color:var(--dim); padding-bottom:40px; margin-top:24px; }
"##;

const JS: &str = r##"
(function () {
  var timings = JSON.parse(document.getElementById("timings").textContent);
  var t0 = Date.now();
  function fmt(ms) {
    if (ms == null) return "";
    if (ms < 1000) return ms + " ms";
    var s = ms / 1000;
    if (s < 60) return s.toFixed(1) + " s";
    return Math.floor(s / 60) + " min " + Math.round(s % 60) + " s";
  }
  function fill() {
    document.querySelectorAll("[data-t]").forEach(function (el) {
      var k = el.getAttribute("data-t");
      var v = k === "elapsed" ? timings.elapsed + (timings.live ? Date.now() - t0 : 0)
            : k === "pending" ? timings.pending + (Date.now() - t0)
            : timings.t[k];
      el.textContent = fmt(v);
    });
  }
  fill();
  if (timings.live) setInterval(fill, 1000);
  // selection, opened nodes and scroll live in the hash: a refresh reloads the page
  function parse() {
    var h = {};
    location.hash.replace(/^#/, "").split("&").forEach(function (kv) {
      var i = kv.indexOf("="); if (i > 0) h[kv.slice(0, i)] = decodeURIComponent(kv.slice(i + 1));
    });
    return h;
  }
  var state = parse();
  var toggled = {};
  (state.o || "").split(",").forEach(function (x) { if (x) toggled[x.slice(0, -2)] = x.slice(-1) === "1"; });
  function write() {
    var o = Object.keys(toggled).map(function (k) { return k + "." + (toggled[k] ? 1 : 0); }).join(",");
    var parts = [];
    if (state.sel) parts.push("sel=" + encodeURIComponent(state.sel));
    if (o) parts.push("o=" + encodeURIComponent(o));
    parts.push("y=" + Math.round(window.scrollY));
    history.replaceState(null, "", "#" + parts.join("&"));
  }
  Object.keys(toggled).forEach(function (k) {
    var d = document.getElementById(k); if (d && d.tagName === "DETAILS") d.open = toggled[k];
  });
  function reveal(el) {
    for (var p = el.parentElement; p; p = p.parentElement) if (p.tagName === "DETAILS") p.open = true;
  }
  function select(id) {
    document.querySelectorAll(".sel").forEach(function (e) { e.classList.remove("sel"); });
    var el = id && document.getElementById(id);
    if (!el) return null;
    if (el.classList.contains("step")) el.classList.add("sel"); else el.classList.add("flash");
    reveal(el);
    return el;
  }
  var el = select(state.sel);
  if (state.y != null) window.scrollTo(0, +state.y); else if (el) el.scrollIntoView({ block: "center" });
  document.addEventListener("toggle", function (e) {
    var d = e.target;
    if (d.tagName === "DETAILS" && d.id) { toggled[d.id] = d.open; write(); }
  }, true);
  document.addEventListener("click", function (e) {
    var a = e.target.closest("a[data-goto]");
    if (a) { e.preventDefault(); state.sel = a.getAttribute("data-goto"); select(state.sel).scrollIntoView({ block: "center" }); write(); return; }
    if (e.target.closest("a, pre, summary")) return;
    var li = e.target.closest("li.step");
    if (!li) return;
    state.sel = state.sel === li.id ? "" : li.id;
    select(state.sel); write();
  });
  var timer = null;
  window.addEventListener("scroll", function () { clearTimeout(timer); timer = setTimeout(write, 150); });
})();
"##;

fn esc(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    for c in text.chars() {
        match c {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '"' => out.push_str("&quot;"),
            c => out.push(c),
        }
    }
    out
}

impl Live {
    /// The whole page for the current model. Reads the goal text of the shown steps from the
    /// transcript first.
    pub(super) fn render_html(&mut self) -> String {
        let running = self.state == RunState::Running;
        let shown = self.shown_steps(running);
        self.load_texts(&shown);
        let mut timing_steps: BTreeMap<usize, u64> = BTreeMap::new();

        let mut out = String::with_capacity(64 * 1024);
        out.push_str("<!doctype html>\n<html lang=\"en\"><head><meta charset=\"utf-8\">\n");
        if running {
            out.push_str("<meta http-equiv=\"refresh\" content=\"2\">\n");
        }
        let _ = write!(
            out,
            "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n\
             <title>EasyCrypt translation of {}</title>\n<style>{CSS}</style></head><body>\n",
            esc(&self.theorem)
        );
        self.header(&mut out, running);
        out.push_str("<main>\n");
        self.summary(&mut out);
        for (e, eq) in self.eqs.iter().enumerate() {
            let _ = writeln!(
                out,
                "<h2>{} <span class=\"note\">(proofstep {}: {} ~ {})</span></h2>",
                esc(&eq.file),
                eq.proofstep,
                esc(&eq.left),
                esc(&eq.right)
            );
            let mut notes = vec![format!(
                "{} sentence(s) outside any oracle (proof opening, base case, goals not asked for)",
                eq.setup_steps
            )];
            if eq.base_case_admitted {
                notes.push("the base case did not close and was admitted".to_string());
            }
            if let Some(report) = &eq.report_file {
                notes.push(format!("report: <code>{}</code>", esc(report)));
            }
            let _ = writeln!(out, "<p class=\"note\">{}</p>", notes.join("; "));
            for (o, oracle) in eq.oracles.iter().enumerate() {
                let key = format!("o{e}_{o}");
                let active = self.cur_eq == Some(e) && self.cur_oracle == Some(o);
                let open = active
                    || (oracle.summary.is_none() && oracle.started)
                    || oracle.summary.as_ref().is_some_and(|s| s.admit_total > 0);
                let status = match (&oracle.summary, oracle.started) {
                    (Some(s), _) if s.problem.is_some() => "no tactics".to_string(),
                    (Some(s), _) if s.admit_total == 0 => "no admit".to_string(),
                    (Some(s), _) => format!("{} admit(s)", s.admit_total),
                    (None, true) => "running".to_string(),
                    (None, false) => "waiting".to_string(),
                };
                let _ = write!(
                    out,
                    "<details class=\"oracle\" id=\"{key}\"{}><summary><b>{}</b> <span class=\"chip\">{status}</span>",
                    if open { " open" } else { "" },
                    esc(&oracle.name)
                );
                if let Some(s) = &oracle.summary {
                    let _ = write!(
                        out,
                        " <span class=\"note\">{} goals closed, {} attempts undone, {} fallback(s), EasyCrypt <span class=\"t\" data-t=\"{key}\"></span></span>",
                        s.closed, s.undone, s.fallbacks
                    );
                }
                out.push_str("</summary>\n");
                if let Some(s) = &oracle.summary {
                    if let Some(problem) = &s.problem {
                        let _ = writeln!(out, "<p class=\"err\">no tactics: {}</p>", esc(problem));
                    } else {
                        let _ = writeln!(
                            out,
                            "<p class=\"note\">lockstep: {} joint paths, {} nodes, {} stuck points{}</p>",
                            s.joint_paths,
                            s.nodes,
                            s.stuck_points,
                            if s.alignment_mismatches > 0 {
                                format!("; {} alignment mismatch(es), fallback used", s.alignment_mismatches)
                            } else {
                                String::new()
                            }
                        );
                    }
                }
                if let Some(href) = &oracle.lockstep_href {
                    let _ = writeln!(
                        out,
                        "<p><a href=\"{}\">lockstep page of this oracle</a></p>",
                        esc(href)
                    );
                }
                for &root in &oracle.roots {
                    self.node(&mut out, e, o, root, &shown, &mut timing_steps);
                }
                out.push_str("</details>\n");
            }
        }
        out.push_str("</main>\n<footer><p>Only the goal text of the steps shown here is embedded (the step EasyCrypt is working on, the steps of the goal being worked on, and the last step of each goal), each cut at ");
        let _ = writeln!(
            out,
            "{} characters and {} goals. Every sentence with EasyCrypt's answer is in <code>ec-transcript.jsonl</code> next to this page (record numbers below are its line numbers); its goals are cut the same way unless the run had <code>--ec-transcript full</code>.</p></footer>",
            super::GOAL_TEXT_CAP,
            super::GOALS_PER_STEP
        );
        self.timings_element(&mut out, running, &timing_steps);
        let _ = write!(out, "<script>{JS}</script>\n</body></html>\n");
        out
    }

    fn header(&self, out: &mut String, running: bool) {
        let _ = write!(
            out,
            "<header><h1>EasyCrypt translation of {}</h1>\n<div class=\"chips\">",
            esc(&self.theorem)
        );
        for (name, items) in &self.phases {
            let _ = write!(out, "<span class=\"done\">{} ({items})</span>", esc(name));
        }
        let (class, label) = match &self.state {
            RunState::Running => ("active", "tactics (running)"),
            RunState::Done => ("done", "tactics (done)"),
            RunState::Failed(_) => ("active", "tactics (failed)"),
        };
        let _ = writeln!(out, "<span class=\"chip {class}\">{label}</span></div>");
        if let RunState::Failed(message) = &self.state {
            let _ = writeln!(
                out,
                "<div class=\"banner failed\">the run stopped: {}</div>",
                esc(message)
            );
        }
        if running {
            let mut place = Vec::new();
            if let Some(e) = self.cur_eq {
                let eq = &self.eqs[e];
                place.push(esc(&eq.file));
                if let Some(o) = self.cur_oracle {
                    let oracle = &eq.oracles[o];
                    place.push(esc(&oracle.name));
                    if let Some(&n) = self.node_stack.last() {
                        let node = &oracle.nodes[n];
                        place.push(format!("{} {}", esc(&node.label), esc(&node.kind)));
                    }
                }
            }
            if self.node_stack.is_empty() && !self.activity.is_empty() {
                place.push(esc(&self.activity));
            }
            let _ = writeln!(
                out,
                "<p>working on: {}</p>",
                if place.is_empty() {
                    "starting".to_string()
                } else {
                    place.join(" &rsaquo; ")
                }
            );
            if let Some(p) = &self.pending {
                let _ = writeln!(
                    out,
                    "<div class=\"pending\"><span class=\"spinner\"></span>waiting for EasyCrypt (<span data-t=\"pending\"></span>): <code>{}</code></div>",
                    esc(&p.sentence)
                );
            }
        }
        let _ = writeln!(
            out,
            "<p class=\"note\">elapsed <span data-t=\"elapsed\"></span></p></header>"
        );
    }

    fn summary(&self, out: &mut String) {
        let mut by_reason: BTreeMap<&'static str, usize> = BTreeMap::new();
        let (mut closed, mut admits, mut done, mut total) = (0, 0, 0, 0);
        for eq in &self.eqs {
            for o in &eq.oracles {
                total += 1;
                if let Some(s) = &o.summary {
                    done += 1;
                    closed += s.closed;
                    admits += s.admit_total;
                    for (reason, n) in &s.admits {
                        *by_reason.entry(reason).or_default() += n;
                    }
                }
            }
        }
        let _ = write!(
            out,
            "<h2>Summary</h2>\n<p>{done} of {total} oracles done, {closed} goals closed, {admits} admit(s)"
        );
        if !by_reason.is_empty() {
            let parts: Vec<String> = by_reason.iter().map(|(r, n)| format!("{r} {n}")).collect();
            let _ = write!(out, " ({})", parts.join(", "));
        }
        out.push_str("</p>\n");
        let mut listed = false;
        for (e, eq) in self.eqs.iter().enumerate() {
            for (o, oracle) in eq.oracles.iter().enumerate() {
                for (n, node) in oracle.nodes.iter().enumerate() {
                    for admit in &node.admits {
                        if !listed {
                            out.push_str(
                                "<table><tr><th>admit</th><th>reason</th><th>where</th></tr>\n",
                            );
                            listed = true;
                        }
                        let _ = writeln!(
                            out,
                            "<tr><td>{}</td><td>{}</td><td><a href=\"#n{e}_{o}_{n}\" data-goto=\"n{e}_{o}_{n}\">{} {}</a></td></tr>",
                            esc(&admit.id),
                            esc(admit.reason),
                            esc(&oracle.name),
                            esc(&node.label)
                        );
                    }
                }
            }
        }
        if listed {
            out.push_str("</table>\n");
        }
    }

    fn node(
        &self,
        out: &mut String,
        e: usize,
        o: usize,
        n: usize,
        shown: &std::collections::BTreeSet<usize>,
        timing: &mut BTreeMap<usize, u64>,
    ) {
        let oracle = &self.eqs[e].oracles[o];
        let node: &NodeRec = &oracle.nodes[n];
        let key = format!("n{e}_{o}_{n}");
        let current =
            self.cur_eq == Some(e) && self.cur_oracle == Some(o) && self.node_stack.contains(&n);
        let (state_class, state) = if !node.admits.is_empty() {
            ("st-admitted", "admitted")
        } else if node.done {
            ("st-closed", "closed")
        } else {
            ("st-open", "open")
        };
        let open = current || !node.admits.is_empty();
        let _ = write!(
            out,
            "<details class=\"node\" id=\"{key}\"{}><summary><span class=\"nid\">{}</span> <span class=\"kind\">{}</span>",
            if open { " open" } else { "" },
            esc(&node.label),
            esc(&node.kind)
        );
        if !node.ids.is_empty() {
            let mut ids = node.ids.join(" ");
            if node.more_ids > 0 {
                let _ = write!(ids, " +{}", node.more_ids);
            }
            let _ = write!(out, " <span class=\"ids\">[{}]</span>", esc(&ids));
        }
        if let (Some(href), Some(ln)) = (&oracle.lockstep_href, node.lockstep_node) {
            let _ = write!(out, " <a href=\"{}#n={ln}\">tree</a>", esc(href));
        }
        if let Some(rung) = node.rungs.last() {
            let _ = write!(out, " <span class=\"chip\">rung: {}</span>", esc(rung));
        }
        let _ = writeln!(
            out,
            " <span class=\"{state_class}\">{state}</span></summary>"
        );
        for admit in &node.admits {
            let _ = writeln!(
                out,
                "<div class=\"admit\"><b>admit</b> <code>{}</code></div>",
                esc(&admit.label)
            );
        }
        if !node.steps.is_empty() {
            out.push_str("<ol class=\"steps\">\n");
            for &id in &node.steps {
                self.step(out, id, shown.contains(&id), timing);
            }
            out.push_str("</ol>\n");
        }
        for &child in &node.children {
            self.node(out, e, o, child, shown, timing);
        }
        out.push_str("</details>\n");
    }

    fn step(&self, out: &mut String, id: usize, embedded: bool, timing: &mut BTreeMap<usize, u64>) {
        let step = &self.steps[id];
        timing.insert(id, step.ms);
        let (class, badge) = match (step.status, step.undone) {
            (StepStatus::Accepted, true) => ("b-undone", "undone"),
            (StepStatus::Accepted, false) => ("b-accepted", "accepted"),
            (StepStatus::Failed, _) => ("b-failed", "failed"),
            (StepStatus::TimedOut, _) => ("b-timeout", "timed out"),
        };
        let _ = write!(
            out,
            "<li class=\"step{}\" id=\"s{id}\"><span class=\"badge {class}\">{badge}</span><code>{}</code>",
            if step.undone { " undone" } else { "" },
            esc(&step.sentence)
        );
        if let Some(error) = &step.error {
            let short: String = error.chars().take(200).collect();
            let _ = write!(out, " <span class=\"err\">{}</span>", esc(&short));
        }
        let _ = write!(out, "<span class=\"t\" data-t=\"s{id}\"></span>");
        out.push_str("<div class=\"detail\">");
        let record = match step.record {
            Some(span) => format!("transcript record {}", span.line),
            None => "no transcript record".to_string(),
        };
        let _ = write!(
            out,
            "<div class=\"note\">{record} ({} goal(s) left, EasyCrypt depth {})</div>",
            step.goals_left, step.state
        );
        if let Some(error) = &step.error {
            let _ = write!(
                out,
                "<div class=\"err\">error: <pre>{}</pre></div>",
                esc(error)
            );
        }
        for message in &step.messages {
            let _ = write!(out, "<pre>{}</pre>", esc(message));
        }
        match (embedded, self.text_of(id)) {
            (
                true,
                Some(GoalTexts {
                    unreadable: true, ..
                }),
            ) => {
                out.push_str(
                    "<div class=\"note\">the goal text could not be read from the transcript</div>",
                );
            }
            (true, Some(texts)) => {
                for (i, goal) in texts.goals.iter().enumerate() {
                    let _ = write!(
                        out,
                        "<div class=\"note\">goal {} of {}</div><pre>{}</pre>",
                        i + 1,
                        texts.total,
                        esc(goal)
                    );
                    if texts.cut[i] > 0 {
                        let _ = write!(
                            out,
                            "<div class=\"note\">... {} more characters, see {record}</div>",
                            texts.cut[i]
                        );
                    }
                }
                if texts.total > texts.goals.len() {
                    let _ = write!(
                        out,
                        "<div class=\"note\">{} more goal(s), see {record}</div>",
                        texts.total - texts.goals.len(),
                    );
                }
                if texts.total == 0 {
                    out.push_str("<div class=\"note\">no goal left</div>");
                }
            }
            _ => match step.record {
                Some(span) => {
                    let _ = write!(
                        out,
                        "<div class=\"note\">goal text not embedded; it is in <code>ec-transcript.jsonl</code>, record {}</div>",
                        span.line
                    );
                }
                None => out.push_str(
                    "<div class=\"note\">goal text not embedded; the transcript was not written for this step</div>",
                ),
            },
        }
        out.push_str("</div></li>\n");
    }

    /// Every timing of the page, and nothing else that varies between runs.
    fn timings_element(&self, out: &mut String, running: bool, steps: &BTreeMap<usize, u64>) {
        let mut json = format!(
            "{{\"live\":{running},\"elapsed\":{},\"pending\":{},\"t\":{{",
            self.started.elapsed().as_millis(),
            self.pending
                .as_ref()
                .map_or(0, |p| p.since.elapsed().as_millis())
        );
        let mut first = true;
        let mut push = |json: &mut String, key: String, ms: u64| {
            if !first {
                json.push(',');
            }
            first = false;
            let _ = write!(json, "\"{key}\":{ms}");
        };
        for (&id, &ms) in steps {
            push(&mut json, format!("s{id}"), ms);
        }
        for (e, eq) in self.eqs.iter().enumerate() {
            for (o, oracle) in eq.oracles.iter().enumerate() {
                if let Some(s) = &oracle.summary {
                    push(&mut json, format!("o{e}_{o}"), s.ec_ms);
                }
            }
        }
        json.push_str("}}");
        let _ = writeln!(
            out,
            "<script id=\"timings\" type=\"application/json\">{json}</script>"
        );
    }
}
