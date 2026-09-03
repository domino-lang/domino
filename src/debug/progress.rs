// SPDX-License-Identifier: MIT OR Apache-2.0

//! Live exploration progress for `domino debug` (story 09).
//!
//! [`run_debug_command`](crate::debug::driver::run_debug_command) streams a
//! sequence of [`DebugEvent`]s to a [`DebugObserver`] as it explores. The driver
//! borrows its strings straight from the in-flight
//! [`DebugRun`](crate::debug::driver::DebugRun); an observer that needs to keep
//! one must clone.
//!
//! ## Guarantees
//!
//! - **The driver behaves identically whether an observer is supplied or not.**
//!   Events are emitted at points the driver already passes through; no solver
//!   call, path, or verdict depends on the observer, and elapsed times live only
//!   inside events — never in `DebugRun` (story 07's determinism guarantee). Pass
//!   [`NopObserver`] (the null object) for "no progress".
//! - A panicking observer unwinds through `run_debug_command` and loses the run.
//!   That is a bug in the observer, not the driver — the observers here stay
//!   deliberately simple (no `unwrap` on per-event formatting, no locks).
//! - [`DebugEvent`] is `#[non_exhaustive]`: later stories may add variants
//!   without a breaking change, so every consumer `match` ends in `_ => {}`.
//!
//! ## Event order
//!
//! ```text
//! Started
//! Totals                         // skipped for an admitted claim
//!   ( LeftPathStarted
//!       ( PairChecked | BranchPruned )*
//!       LeftPathPruned?          // only when `--check-left` cut the terminal
//!       LeftPathFinished )*
//! Finished
//! ```
//!
//! `LeftPathStarted.index` / `LeftPathFinished.index` are 1-based and strictly
//! increasing. An admitted claim emits `Started { admitted: true }` then
//! `Finished` and nothing between.
//!
//! [`DebugEvent::Totals`] (story 10) carries the syntactic terminal counts of
//! both oracles ([`crate::debug::ir::count_terminals`]) — solver-free upper
//! bounds computed once, right after inlining. Branch pruning (story 08) and
//! `--check-left` mean a run reaches fewer paths than the totals promise, so the
//! bars label the numbers as bounds and never claim `N/N` is exact.
//!
//! Note (divergence from the story spec): the spec's `LeftPathsCollected` /
//! `RightPathsCollected` events assumed both sides were fully enumerated up
//! front. Story 08 made both sides stream, so those were dropped; story 10's
//! `Totals` replaces them with a purely structural count that needs no
//! enumeration pass.

use std::cell::RefCell;
use std::io::Write as _;
use std::time::Duration;

use indicatif::{MultiProgress, ProgressBar, ProgressStyle};
use indicatif_log_bridge::LogWrapper;

use crate::debug::driver::{Summary, Verdict};
use crate::debug::exec::Side;

/// A structured event emitted by `run_debug_command` as it explores.
#[non_exhaustive]
pub enum DebugEvent<'a> {
    /// Emitted once, before any solver work. An admitted run emits this then
    /// [`DebugEvent::Finished`] and nothing between.
    Started {
        oracle: &'a str,
        claim: &'a str,
        admitted: bool,
    },

    /// Syntactic terminal counts for both sides, from
    /// [`crate::debug::ir::count_terminals`]. Emitted once, after
    /// [`DebugEvent::Started`] and before any solver work; skipped for an
    /// admitted claim. Both are **upper bounds** — branch pruning and
    /// `--check-left` cut the real numbers down. `right_total` is per left path
    /// (the right oracle is the same under each left terminal).
    Totals { left_total: u64, right_total: u64 },

    /// Starting to explore left path `index` (1-based).
    LeftPathStarted { index: usize, id: &'a str },

    /// `--check-left` proved this left path's terminal unreachable; its right
    /// side is skipped. Followed by [`DebugEvent::LeftPathFinished`].
    LeftPathPruned { id: &'a str },

    /// One `(left, right)` terminal pair has been classified. `elapsed` is the
    /// wall-clock of that pair's `check-sat`(s) only.
    PairChecked {
        id: &'a str,
        verdict: &'a Verdict,
        elapsed: Duration,
    },

    /// A branch was proved unreachable and cut before its subtree was explored
    /// (story 08's `SolverPruner`). `id` is in the same namespace as path ids
    /// (`"p2"` for a left prune, `"3.p1"` for a right prune under left path
    /// `#3`).
    BranchPruned {
        side: Side,
        id: &'a str,
        label: usize,
    },

    /// Left path `index` and its whole right subtree are done. `running` is the
    /// summary of everything classified so far.
    LeftPathFinished { index: usize, running: Summary },

    /// Exploration stopped — naturally, by `--max-paths`, or by `Ctrl-C`.
    Finished { summary: Summary, partial: bool },
}

/// Consumes [`DebugEvent`]s. Implementations must tolerate unknown future
/// variants (`match … { _ => {} }`).
pub trait DebugObserver {
    fn on_event(&mut self, event: &DebugEvent<'_>);
}

/// Shared, interior-mutable handle to a [`DebugObserver`].
///
/// `run_debug_command` wraps the caller's `&mut dyn DebugObserver` in one of
/// these so that the solver-backed branch oracle and the terminal callbacks —
/// which are both live at the same time during exploration — can each reach it,
/// exactly as the driver already does for the solver itself.
pub type SharedObserver<'a> = RefCell<&'a mut dyn DebugObserver>;

/// The default: does nothing. Library callers and tests pass `&mut NopObserver`.
pub struct NopObserver;

impl DebugObserver for NopObserver {
    fn on_event(&mut self, _: &DebugEvent<'_>) {}
}

// ---------------------------------------------------------------------------
// Shared formatting
// ---------------------------------------------------------------------------

fn verdict_label(v: &Verdict) -> &'static str {
    match v {
        Verdict::Verified => "verified",
        Verdict::Unreachable => "unreachable",
        Verdict::GoalFails { .. } => "GOAL FAILS",
        Verdict::Inconclusive { .. } => "inconclusive",
    }
}

fn side_label(side: &Side) -> &'static str {
    match side {
        Side::Left => "left",
        Side::Right => "right",
    }
}

/// One `debug: …` line for an event, or `None` for events that do not get their
/// own line. Factored out so it can be unit-tested without capturing stderr.
///
/// `left_total` / `right_total` are the last [`DebugEvent::Totals`] the observer
/// saw (`0` before it arrives); the per-path lines carry `k/N` when they are
/// known, plain `k` otherwise. Pure function of `(event, remembered totals)`.
fn plain_line(ev: &DebugEvent<'_>, left_total: u64, right_total: u64) -> Option<String> {
    // `DebugEvent` is `#[non_exhaustive]`; the trailing arm is dead within this
    // crate but load-bearing for future variants added by a later story.
    #[allow(unreachable_patterns)]
    Some(match ev {
        DebugEvent::Started {
            oracle,
            claim,
            admitted,
        } => {
            if *admitted {
                format!("debug: {oracle} / {claim} — admitted, nothing to check")
            } else {
                format!("debug: {oracle} / {claim} — exploring")
            }
        }
        DebugEvent::Totals {
            left_total,
            right_total,
        } => format!(
            "debug: {left_total} left paths, ≤{right_total} right paths per left path \
             (syntactic upper bounds)"
        ),
        DebugEvent::LeftPathStarted { index, id } => {
            if left_total > 0 {
                format!("debug: left {index}/{left_total} (#{id}) …")
            } else {
                format!("debug: left {index} (#{id}) …")
            }
        }
        DebugEvent::LeftPathPruned { id } => {
            format!("debug:   left path #{id} unreachable — pruned")
        }
        DebugEvent::PairChecked {
            id,
            verdict,
            elapsed,
        } => {
            let scope = if right_total > 0 {
                format!("#{id}/{right_total}")
            } else {
                format!("#{id}")
            };
            format!(
                "debug:   {scope}  {:<12}  {:.2}s",
                verdict_label(verdict),
                elapsed.as_secs_f64()
            )
        }
        DebugEvent::BranchPruned { side, id, label } => {
            format!("debug:   pruned #{id} at L{label} ({})", side_label(side))
        }
        DebugEvent::LeftPathFinished { index, running } => format!(
            "debug:   left {index} done — running: {} verified, {} unreachable, {} GOAL FAILS, {} inconclusive",
            running.verified, running.unreachable, running.goal_fails, running.inconclusive
        ),
        DebugEvent::Finished { summary, partial } => format!(
            "debug: done — {} left, {} right; {} verified, {} unreachable, {} GOAL FAILS, {} inconclusive (partial: {})",
            summary.left_paths,
            summary.right_paths,
            summary.verified,
            summary.unreachable,
            summary.goal_fails,
            summary.inconclusive,
            if *partial { "yes" } else { "no" }
        ),
        _ => return None,
    })
}

// ---------------------------------------------------------------------------
// PlainObserver — line-oriented stderr log
// ---------------------------------------------------------------------------

/// One terse, greppable line per event on stderr. For logs, CI and pipes.
pub struct PlainObserver {
    err: std::io::Stderr,
    left_total: u64,
    right_total: u64,
}

impl PlainObserver {
    pub fn new() -> Self {
        Self {
            err: std::io::stderr(),
            left_total: 0,
            right_total: 0,
        }
    }
}

impl Default for PlainObserver {
    fn default() -> Self {
        Self::new()
    }
}

impl DebugObserver for PlainObserver {
    fn on_event(&mut self, ev: &DebugEvent<'_>) {
        if let DebugEvent::Totals {
            left_total,
            right_total,
        } = ev
        {
            self.left_total = *left_total;
            self.right_total = *right_total;
        }
        if let Some(line) = plain_line(ev, self.left_total, self.right_total) {
            let _ = writeln!(self.err, "{line}");
        }
        // Surface a failing goal the moment it is found, not only in the tree.
        if let DebugEvent::PairChecked { id, verdict, .. } = ev {
            if matches!(verdict, Verdict::GoalFails { .. }) {
                let _ = writeln!(self.err, "debug: ⚠ GOAL FAILS at #{id}");
            }
        }
    }
}

// ---------------------------------------------------------------------------
// BarObserver — indicatif
// ---------------------------------------------------------------------------

#[derive(Default, Clone, Copy)]
struct Tally {
    verified: usize,
    unreachable: usize,
    goal_fails: usize,
    inconclusive: usize,
    pruned: usize,
}

impl Tally {
    fn bump(&mut self, v: &Verdict) {
        match v {
            Verdict::Verified => self.verified += 1,
            Verdict::Unreachable => self.unreachable += 1,
            Verdict::GoalFails { .. } => self.goal_fails += 1,
            Verdict::Inconclusive { .. } => self.inconclusive += 1,
        }
    }

    fn render(&self) -> String {
        format!(
            "✓{} ·{} ✗{} ?{} ✂{}",
            self.verified, self.unreachable, self.goal_fails, self.inconclusive, self.pruned
        )
    }
}

/// A two-line `indicatif` display on stderr. Spinners until
/// [`DebugEvent::Totals`] arrives, then two bounded bars:
///
/// ```text
/// left   ▕████████░░░░░░░░▏ 3/6    PKENC / same-output
/// pairs  ▕██████████████░░▏ 71/96  ✓2 ·68 ✗1 ?0 ✂12   [0:00:38]
/// ```
///
/// Both totals are syntactic upper bounds; the `pairs` bar resets to `0` at
/// every `LeftPathStarted` and is snapped to full at `LeftPathFinished` (a
/// sweep that pruned its way to the end would otherwise stall part-way).
///
/// `indicatif` draws nothing when stderr is not a terminal; `main.rs` only
/// constructs this for `--progress bar` or `--progress auto` on a TTY.
pub struct BarObserver {
    mp: MultiProgress,
    left: ProgressBar,
    pairs: ProgressBar,
    tally: Tally,
}

const SPINNER_LEFT: &str = "{spinner:.cyan} {msg}";
const SPINNER_PAIRS: &str = "{spinner:.green} pairs {pos:>4}  {msg}  [{elapsed_precise}]";
const BAR_LEFT: &str = "left   {bar:24.cyan/blue} {pos}/{len}  {msg}";
const BAR_PAIRS: &str = "pairs  {bar:24.green/blue} {pos}/{len}  {msg}  [{elapsed_precise}]";

fn style(template: &str, fallback_spinner: bool) -> ProgressStyle {
    ProgressStyle::with_template(template).unwrap_or_else(|_| {
        if fallback_spinner {
            ProgressStyle::default_spinner()
        } else {
            ProgressStyle::default_bar()
        }
    })
}

impl BarObserver {
    pub fn new() -> Self {
        let mp = MultiProgress::new();

        let left = mp.add(ProgressBar::new_spinner());
        left.set_style(style(SPINNER_LEFT, true));
        left.set_message("left: starting…");
        left.enable_steady_tick(Duration::from_millis(120));

        let pairs = mp.add(ProgressBar::new_spinner());
        pairs.set_style(style(SPINNER_PAIRS, true));
        pairs.enable_steady_tick(Duration::from_millis(120));

        // Keep `log::` output from tearing the bars. `prove` in the same process
        // would already have installed this — never happens for `debug`, but
        // swallow the error rather than panic if it does.
        let logger = env_logger::Builder::from_default_env().build();
        let _ = LogWrapper::new(mp.clone(), logger).try_init();

        Self {
            mp,
            left,
            pairs,
            tally: Tally::default(),
        }
    }

    /// Keep the bar from looking stuck if a `Prune`-free re-entry ever pushes
    /// `pos` past `len` (`indicatif` clamps silently otherwise).
    fn clamp_len(bar: &ProgressBar) {
        let pos = bar.position();
        if bar.length().is_some_and(|len| pos > len) {
            bar.set_length(pos);
        }
    }
}

impl Default for BarObserver {
    fn default() -> Self {
        Self::new()
    }
}

impl DebugObserver for BarObserver {
    fn on_event(&mut self, ev: &DebugEvent<'_>) {
        // `DebugEvent` is `#[non_exhaustive]`; the trailing `_` arm is dead
        // within this crate but load-bearing for future variants.
        #[allow(unreachable_patterns)]
        match ev {
            DebugEvent::Started {
                oracle,
                claim,
                admitted,
            } => {
                self.left.set_message(if *admitted {
                    format!("{oracle} / {claim} — admitted, nothing to check")
                } else {
                    format!("{oracle} / {claim}")
                });
            }
            DebugEvent::Totals {
                left_total,
                right_total,
            } => {
                // Switch both lines from spinner to a bounded bar. `indicatif`
                // needs a non-zero length; a genuinely path-free oracle (0) is
                // clamped to 1 so the bar renders rather than divide-by-zero.
                self.left.disable_steady_tick();
                self.pairs.disable_steady_tick();
                self.left.set_style(style(BAR_LEFT, false));
                self.pairs.set_style(style(BAR_PAIRS, false));
                self.left.set_length((*left_total).max(1));
                self.pairs.set_length((*right_total).max(1));
                self.left.set_position(0);
                self.pairs.set_position(0);
                self.pairs.set_message(self.tally.render());
            }
            DebugEvent::LeftPathStarted { index, id } => {
                self.left
                    .set_position((*index as u64).saturating_sub(1));
                self.left.set_message(format!("#{id}"));
                self.pairs.set_position(0);
                self.pairs.set_message(self.tally.render());
            }
            DebugEvent::LeftPathPruned { .. } => {
                self.pairs
                    .set_message(format!("left path pruned  {}", self.tally.render()));
            }
            DebugEvent::PairChecked { id, verdict, .. } => {
                self.tally.bump(verdict);
                self.pairs.inc(1);
                Self::clamp_len(&self.pairs);
                self.pairs.set_message(self.tally.render());
                if matches!(verdict, Verdict::GoalFails { .. }) {
                    let _ = self.mp.println(format!("⚠ GOAL FAILS at #{id}"));
                }
            }
            DebugEvent::BranchPruned { .. } => {
                self.tally.pruned += 1;
                self.pairs.set_message(self.tally.render());
            }
            DebugEvent::LeftPathFinished { index, .. } => {
                self.left.set_position(*index as u64);
                Self::clamp_len(&self.left);
                // A sweep that pruned its way to the end reads as complete
                // rather than stalling at 60 %.
                if let Some(len) = self.pairs.length() {
                    self.pairs.set_position(len);
                }
            }
            DebugEvent::Finished { .. } => {
                self.left.finish_and_clear();
                self.pairs.finish_and_clear();
                let _ = self.mp.clear();
            }
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nop_observer_ignores_everything() {
        let mut o = NopObserver;
        o.on_event(&DebugEvent::Started {
            oracle: "O",
            claim: "c",
            admitted: false,
        });
        o.on_event(&DebugEvent::Finished {
            summary: Summary::default(),
            partial: false,
        });
    }

    #[test]
    fn plain_lines_are_terse_and_greppable() {
        assert_eq!(
            plain_line(
                &DebugEvent::Started {
                    oracle: "PKENC",
                    claim: "same-output",
                    admitted: false,
                },
                0,
                0
            )
            .unwrap(),
            "debug: PKENC / same-output — exploring"
        );

        // Before Totals: no `k/N`, exactly the pre-story-10 format.
        assert_eq!(
            plain_line(&DebugEvent::LeftPathStarted { index: 2, id: "2" }, 0, 0).unwrap(),
            "debug: left 2 (#2) …"
        );
        let pc = plain_line(
            &DebugEvent::PairChecked {
                id: "2.5",
                verdict: &Verdict::Verified,
                elapsed: Duration::from_millis(240),
            },
            0,
            0,
        )
        .unwrap();
        assert!(pc.starts_with("debug:   #2.5  verified"), "{pc}");
        assert!(pc.ends_with("0.24s"), "{pc}");

        // The Totals line itself.
        assert_eq!(
            plain_line(
                &DebugEvent::Totals {
                    left_total: 6,
                    right_total: 12,
                },
                0,
                0
            )
            .unwrap(),
            "debug: 6 left paths, ≤12 right paths per left path (syntactic upper bounds)"
        );

        // After Totals: per-path lines carry `k/N` / `j/M`.
        assert_eq!(
            plain_line(&DebugEvent::LeftPathStarted { index: 3, id: "3" }, 6, 12).unwrap(),
            "debug: left 3/6 (#3) …"
        );
        let pc = plain_line(
            &DebugEvent::PairChecked {
                id: "3.7",
                verdict: &Verdict::Verified,
                elapsed: Duration::from_millis(240),
            },
            6,
            12,
        )
        .unwrap();
        assert!(pc.starts_with("debug:   #3.7/12  verified"), "{pc}");

        let done = plain_line(
            &DebugEvent::Finished {
                summary: Summary {
                    left_paths: 6,
                    right_paths: 96,
                    goal_fails: 1,
                    ..Summary::default()
                },
                partial: false,
            },
            6,
            12,
        )
        .unwrap();
        assert!(done.contains("6 left, 96 right"), "{done}");
        assert!(done.contains("1 GOAL FAILS"), "{done}");
        assert!(done.ends_with("(partial: no)"), "{done}");

        assert_eq!(
            plain_line(
                &DebugEvent::BranchPruned {
                    side: Side::Right,
                    id: "3.p1",
                    label: 14,
                },
                6,
                12
            )
            .unwrap(),
            "debug:   pruned #3.p1 at L14 (right)"
        );
    }

    #[test]
    fn plain_observer_remembers_totals_across_events() {
        let mut o = PlainObserver::new();
        o.on_event(&DebugEvent::Totals {
            left_total: 4,
            right_total: 9,
        });
        assert_eq!((o.left_total, o.right_total), (4, 9));
    }
}
