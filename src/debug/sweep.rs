// SPDX-License-Identifier: MIT OR Apache-2.0

//! Sweeping the debugger over a project (story 19 §4.1, §4.7).
//!
//! `--proof`, `--proofstep`, `--oracle` and `--claim` are all optional: omitted means *all*,
//! given means *only that*, exactly as in `domino prove`. [`plan`] turns the filters into the
//! list of oracles to run; the caller runs each one and hands its [`SweepEntry`] to
//! [`write_index`], which links every run and lists what failed.

use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::time::Duration;

use crate::debug::driver::{equivalence_of, ClaimSummary, DebugError, DebugRun, StopReason};
use crate::debug::layout::Layout;
use crate::debug::lockstep::PairRecord;
use crate::debug::lockstep_run::LockstepRun;
use crate::debug::report::format_elapsed;
use crate::project::Project;

/// One oracle of one equivalence proofstep: what a debug run is about.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Target {
    pub theorem: String,
    pub proofstep: usize,
    pub left: String,
    pub right: String,
    pub oracle: String,
}

/// A proofstep the sweep passed over because it is not an equivalence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Skipped {
    pub theorem: String,
    pub proofstep: usize,
    pub kind: &'static str,
}

impl Skipped {
    /// The one-line note the sweep prints on stderr.
    pub fn note(&self) -> String {
        format!(
            "debug: skipping {} proofstep {}: a {}, not an equivalence",
            self.theorem, self.proofstep, self.kind
        )
    }
}

#[derive(Debug, Clone, Default)]
pub struct Plan {
    pub targets: Vec<Target>,
    pub skipped: Vec<Skipped>,
}

/// The oracles the filters select, theorems in name order, proofsteps and oracles in
/// declaration order.
///
/// A proofstep that is a reduction or a conjecture is **skipped** while sweeping; naming it
/// with `proofstep` is an error, as it always was.
pub fn plan<P: Project>(
    project: &P,
    proof: Option<&str>,
    proofstep: Option<usize>,
    oracle: Option<&str>,
) -> Result<Plan, DebugError> {
    let theorem_names: Vec<String> = match proof {
        Some(name) => vec![name.to_string()],
        None => {
            let mut names: Vec<String> = project.theorems().map(String::from).collect();
            names.sort();
            names
        }
    };

    let mut plan = Plan::default();
    for name in &theorem_names {
        let theorem = project
            .get_theorem(name)
            .ok_or_else(|| DebugError::TheoremNotFound { name: name.clone() })?;
        let steps: Vec<usize> = match proofstep {
            Some(step) => vec![step],
            None => (0..theorem.game_hops.len()).collect(),
        };
        for step in steps {
            let eq = match equivalence_of(theorem, step) {
                Ok(eq) => eq,
                Err(DebugError::ProofstepNotEquivalence { kind, .. }) if proofstep.is_none() => {
                    plan.skipped.push(Skipped {
                        theorem: name.clone(),
                        proofstep: step,
                        kind,
                    });
                    continue;
                }
                Err(e) => return Err(e),
            };
            let exports: Vec<String> = theorem
                .find_game_instance(eq.left_name())
                .map(|inst| {
                    inst.game()
                        .exports
                        .iter()
                        .map(|export| export.name().to_string())
                        .collect()
                })
                .unwrap_or_default();
            if let Some(wanted) = oracle {
                if !exports.iter().any(|o| o == wanted) && proof.is_some() && proofstep.is_some()
                {
                    return Err(DebugError::OracleNotExported {
                        oracle: wanted.to_string(),
                        game_inst: eq.left_name().to_string(),
                    });
                }
            }
            for exported in exports {
                if oracle.is_some_and(|wanted| wanted != exported) {
                    continue;
                }
                plan.targets.push(Target {
                    theorem: name.clone(),
                    proofstep: step,
                    left: eq.left_name().to_string(),
                    right: eq.right_name().to_string(),
                    oracle: exported,
                });
            }
        }
    }

    if plan.targets.is_empty() {
        if let Some(wanted) = oracle {
            return Err(DebugError::OracleNotExported {
                oracle: wanted.to_string(),
                game_inst: "any selected proofstep".to_string(),
            });
        }
    }
    Ok(plan)
}

/// What one claim said over every pair (or joint path) of a run.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ClaimLine {
    pub claim: String,
    pub verified: usize,
    pub unreachable: usize,
    pub goal_fails: usize,
    pub inconclusive: usize,
}

/// One pair (or joint path) a claim failed on.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Failure {
    pub claim: String,
    pub pair: String,
    pub verdict: &'static str,
}

/// The outcome of one oracle's run, as the sweep's report needs it.
#[derive(Debug, Clone)]
pub struct SweepEntry {
    pub target: Target,
    /// `sequential` or `lockstep`.
    pub strategy: &'static str,
    /// `domino` or `easycrypt`.
    pub listing: &'static str,
    pub out_dir: PathBuf,
    /// The viewer, relative to `out_dir`.
    pub viewer: String,
    /// `pairs` for the sequential strategy, `joint paths` for lockstep.
    pub unit: &'static str,
    pub units: usize,
    pub claims: Vec<ClaimLine>,
    pub failures: Vec<Failure>,
    /// No failing or inconclusive claim, and the run finished.
    pub ok: bool,
    pub stop_reason: StopReason,
    pub elapsed: Duration,
}

impl SweepEntry {
    pub fn from_sequential(target: Target, run: &DebugRun) -> Self {
        let claims: Vec<ClaimLine> = if run.claim_summaries.is_empty() {
            let s = &run.summary;
            vec![ClaimLine {
                claim: run.claim.clone(),
                verified: s.verified,
                unreachable: s.unreachable,
                goal_fails: s.goal_fails,
                inconclusive: s.inconclusive,
            }]
        } else {
            run.claim_summaries.iter().map(claim_line_of).collect()
        };
        let mut failures = Vec::new();
        for lp in &run.left_paths {
            for rp in &lp.right_paths {
                if rp.claims.is_empty() {
                    if rp.verdict.is_failure() {
                        failures.push(Failure {
                            claim: run.claim.clone(),
                            pair: format!("#{}", rp.id),
                            verdict: rp.verdict.slug(),
                        });
                    }
                }
                for c in rp.claims.iter().filter(|c| c.verdict.is_failure()) {
                    failures.push(Failure {
                        claim: c.claim.clone(),
                        pair: format!("#{}", rp.id),
                        verdict: c.verdict.slug(),
                    });
                }
            }
        }
        Self {
            target,
            strategy: run.strategy,
            listing: "domino",
            out_dir: PathBuf::from(&run.out_dir),
            viewer: Layout::Strategy(run.strategy).viewer(),
            unit: "pairs",
            units: run.summary.right_paths,
            claims: if run.admitted { Vec::new() } else { claims },
            failures,
            ok: run.is_ok(),
            stop_reason: run.stop_reason,
            elapsed: run.elapsed,
        }
    }

    pub fn from_lockstep(target: Target, run: &LockstepRun) -> Self {
        let claims = run
            .summary
            .claims
            .iter()
            .map(|c| ClaimLine {
                claim: c.claim.clone(),
                verified: c.counts.verified,
                unreachable: c.counts.unreachable,
                goal_fails: c.counts.goal_fails,
                inconclusive: c.counts.inconclusive,
            })
            .collect();
        let mut failures = Vec::new();
        for pair in &run.outcome.pairs {
            failures.extend(failures_of(pair));
        }
        Self {
            target,
            strategy: run.meta.mode,
            listing: run.meta.listing,
            out_dir: PathBuf::from(&run.meta.out_dir),
            viewer: run.meta.layout.viewer(),
            unit: "joint paths",
            units: run.summary.joint_paths,
            claims,
            failures,
            ok: run.is_ok(),
            stop_reason: run.outcome.stop_reason,
            elapsed: run.elapsed,
        }
    }

    /// `theorem / proofstep 0 (Left == Right) / oracle`.
    fn label(&self) -> String {
        let t = &self.target;
        format!(
            "{} proofstep {} ({} == {}) {}",
            t.theorem, t.proofstep, t.left, t.right, t.oracle
        )
    }

    /// The claims that failed or could not be decided somewhere, and how often.
    fn failing_claims(&self) -> impl Iterator<Item = &ClaimLine> {
        self.claims
            .iter()
            .filter(|c| c.goal_fails > 0 || c.inconclusive > 0)
    }

    /// The line printed as the run finishes.
    pub fn one_line(&self) -> String {
        let status = if self.ok {
            "ok".to_string()
        } else if self.stop_reason.is_partial() {
            format!("STOPPED EARLY ({})", self.stop_reason.phrase())
        } else {
            let failing: Vec<String> = self
                .failing_claims()
                .map(|c| {
                    format!(
                        "{} ({})",
                        c.claim,
                        [(c.goal_fails, "GOAL FAILS"), (c.inconclusive, "inconclusive")]
                            .iter()
                            .filter(|(n, _)| *n > 0)
                            .map(|(n, w)| format!("{n} {w}"))
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                })
                .collect();
            format!("FAILS: {}", failing.join("; "))
        };
        format!(
            "{}: {} {}, {} [{}]",
            self.label(),
            self.units,
            self.unit,
            status,
            format_elapsed(self.elapsed)
        )
    }
}

fn claim_line_of(c: &ClaimSummary) -> ClaimLine {
    ClaimLine {
        claim: c.claim.clone(),
        verified: c.verified,
        unreachable: c.unreachable_pair + c.unreachable_dependency,
        goal_fails: c.goal_fails,
        inconclusive: c.inconclusive,
    }
}

fn failures_of(pair: &PairRecord) -> Vec<Failure> {
    pair.claims
        .iter()
        .filter(|c| c.verdict.is_failure())
        .map(|c| Failure {
            claim: c.claim.clone(),
            pair: pair.id.clone(),
            verdict: c.verdict.slug(),
        })
        .collect()
}

/// A run that stopped on `Ctrl-C` stops the sweep with it.
pub fn is_interrupted(entry: &SweepEntry) -> bool {
    matches!(entry.stop_reason, StopReason::Interrupted)
}

/// The project-wide table of failures: one row per (oracle, claim) that failed or could not be
/// decided, with the pairs it failed on. Empty when nothing did.
pub fn failure_table(entries: &[SweepEntry]) -> String {
    const SHOWN: usize = 6;
    let mut rows = String::new();
    for entry in entries {
        for c in entry.failing_claims() {
            let pairs: Vec<&str> = entry
                .failures
                .iter()
                .filter(|f| f.claim == c.claim)
                .map(|f| f.pair.as_str())
                .collect();
            let more = pairs.len().saturating_sub(SHOWN);
            let _ = writeln!(
                rows,
                "  {}  {}: {} GOAL FAILS, {} inconclusive on {}{}{}",
                entry.label(),
                c.claim,
                c.goal_fails,
                c.inconclusive,
                entry.unit,
                if pairs.is_empty() {
                    String::new()
                } else {
                    format!(" ({}", pairs.iter().take(SHOWN).copied().collect::<Vec<_>>().join(", "))
                },
                if pairs.is_empty() {
                    String::new()
                } else if more > 0 {
                    format!(", … and {more} more)")
                } else {
                    ")".to_string()
                },
            );
        }
    }
    if rows.is_empty() {
        return rows;
    }
    format!("failures\n{rows}")
}

/// Write `index.html` and `summary.txt` into `root` (`_build/debug/domino`), linking every run
/// of this sweep. Returns the paths written.
pub fn write_index(root: &Path, entries: &[SweepEntry]) -> std::io::Result<(PathBuf, PathBuf)> {
    std::fs::create_dir_all(root)?;
    let href = |entry: &SweepEntry| -> String {
        let dir = entry
            .out_dir
            .strip_prefix(root)
            .map(Path::to_path_buf)
            .unwrap_or_else(|_| entry.out_dir.clone());
        format!("{}/{}", dir.display(), entry.viewer)
    };

    let mut text = String::new();
    let _ = writeln!(text, "domino debug — every run");
    let _ = writeln!(text, "========================\n");
    for entry in entries {
        let _ = writeln!(text, "{}", entry.one_line());
        let _ = writeln!(
            text,
            "    {} strategy, {} listing: {}",
            entry.strategy,
            entry.listing,
            href(entry)
        );
    }
    let table = failure_table(entries);
    if !table.is_empty() {
        let _ = writeln!(text, "\n{table}");
    }
    let summary = root.join("summary.txt");
    std::fs::write(&summary, text)?;

    let mut html = String::from(
        "<!doctype html>\n<html lang=\"en\"><head><meta charset=\"utf-8\">\n\
         <meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n\
         <title>domino debug — every run</title>\n<style>\n\
         :root{--bg:#fff;--fg:#1b1f24;--dim:#59636e;--ok:#1a7f37;--bad:#cf222e;--line:#d0d7de}\n\
         @media (prefers-color-scheme:dark){:root{--bg:#0d1117;--fg:#e6edf3;--dim:#8d96a0;--ok:#3fb950;--bad:#f85149;--line:#30363d}}\n\
         body{background:var(--bg);color:var(--fg);font:14px/1.5 system-ui,sans-serif;margin:0 auto;max-width:72rem;padding:1rem 16px}\n\
         table{border-collapse:collapse;width:100%}th,td{border-bottom:1px solid var(--line);padding:.35rem .6rem;text-align:left;vertical-align:top}\n\
         .ok{color:var(--ok)}.bad{color:var(--bad)}.dim{color:var(--dim)}a{color:inherit}\n\
         .scroll{overflow-x:auto}\n</style></head><body>\n<h1>domino debug — every run</h1>\n",
    );
    html.push_str(
        "<div class=\"scroll\"><table><thead><tr><th>theorem</th><th>proofstep</th><th>oracle</th>\
         <th>strategy</th><th>result</th><th>claims that failed</th><th>time</th></tr></thead><tbody>\n",
    );
    for entry in entries {
        let t = &entry.target;
        let failing: Vec<String> = entry
            .failing_claims()
            .map(|c| format!("{} ({} fail, {} inconclusive)", esc(&c.claim), c.goal_fails, c.inconclusive))
            .collect();
        let _ = writeln!(
            html,
            "<tr><td>{}</td><td>{} <span class=\"dim\">{} == {}</span></td><td><a href=\"{}\">{}</a></td>\
             <td>{} <span class=\"dim\">({} listing)</span></td><td class=\"{}\">{} {}, {}</td><td>{}</td><td>{}</td></tr>",
            esc(&t.theorem),
            t.proofstep,
            esc(&t.left),
            esc(&t.right),
            esc(&href_attr(&href(entry))),
            esc(&t.oracle),
            entry.strategy,
            entry.listing,
            if entry.ok { "ok" } else { "bad" },
            entry.units,
            entry.unit,
            if entry.ok {
                "ok".to_string()
            } else if entry.stop_reason.is_partial() {
                format!("stopped early ({})", esc(&entry.stop_reason.phrase()))
            } else {
                "FAILS".to_string()
            },
            failing.join("<br>"),
            format_elapsed(entry.elapsed),
        );
    }
    html.push_str("</tbody></table></div>\n</body></html>\n");
    let index = root.join("index.html");
    std::fs::write(&index, html)?;
    Ok((index, summary))
}

/// Percent-encode what a relative `href` cannot hold: `!` and spaces appear in run names
/// (`!all-claims!`) and stay legal, but `#` and `?` would cut the path short.
fn href_attr(path: &str) -> String {
    path.replace('#', "%23").replace('?', "%3F").replace(' ', "%20")
}

fn esc(s: &str) -> String {
    s.replace('&', "&amp;").replace('<', "&lt;").replace('>', "&gt;").replace('"', "&quot;")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn entry(ok: bool, claims: Vec<ClaimLine>, failures: Vec<Failure>) -> SweepEntry {
        SweepEntry {
            target: Target {
                theorem: "T".into(),
                proofstep: 0,
                left: "L".into(),
                right: "R".into(),
                oracle: "O".into(),
            },
            strategy: "sequential",
            listing: "domino",
            out_dir: PathBuf::from("/r/T/L-R/O/!all-claims!"),
            viewer: "sequential_viewer.html".into(),
            unit: "pairs",
            units: 4,
            claims,
            failures,
            ok,
            stop_reason: StopReason::Completed,
            elapsed: Duration::from_millis(1200),
        }
    }

    fn line(claim: &str, goal_fails: usize) -> ClaimLine {
        ClaimLine {
            claim: claim.into(),
            verified: 3,
            goal_fails,
            ..ClaimLine::default()
        }
    }

    #[test]
    fn a_clean_sweep_has_no_failure_table() {
        assert_eq!(failure_table(&[entry(true, vec![line("same-output", 0)], vec![])]), "");
    }

    #[test]
    fn the_failure_table_names_the_claim_and_the_pairs() {
        let e = entry(
            false,
            vec![line("same-output", 0), line("invariant", 2)],
            vec![
                Failure { claim: "invariant".into(), pair: "#1.2".into(), verdict: "goal-fails" },
                Failure { claim: "invariant".into(), pair: "#3.1".into(), verdict: "goal-fails" },
            ],
        );
        let table = failure_table(&[e]);
        assert!(table.starts_with("failures\n"), "{table}");
        assert!(table.contains("invariant: 2 GOAL FAILS"), "{table}");
        assert!(table.contains("#1.2, #3.1"), "{table}");
        assert!(!table.contains("same-output"), "{table}");
    }

    #[test]
    fn the_index_links_each_run_relative_to_its_root() {
        let dir = tempfile::tempdir().unwrap();
        let mut e = entry(true, vec![line("same-output", 0)], vec![]);
        e.out_dir = dir.path().join("T/L-R/O/!all-claims!");
        let (index, summary) = write_index(dir.path(), &[e]).unwrap();
        let html = std::fs::read_to_string(index).unwrap();
        assert!(
            html.contains("href=\"T/L-R/O/!all-claims!/sequential_viewer.html\""),
            "{html}"
        );
        let text = std::fs::read_to_string(summary).unwrap();
        assert!(text.contains("T proofstep 0 (L == R) O: 4 pairs, ok"), "{text}");
    }
}
