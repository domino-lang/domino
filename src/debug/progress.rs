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
//! Note (divergence from the story spec): the spec's `LeftPathsCollected` /
//! `RightPathsCollected` events assumed both sides were fully enumerated up
//! front. Story 08 made both sides stream (so branch pruning can cut subtrees
//! before their terminals are reached), so there is no up-front total on either
//! side and those two events were dropped. The bars are spinners with a running
//! pair counter instead of fixed-length progress bars.

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
fn plain_line(ev: &DebugEvent<'_>) -> Option<String> {
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
        DebugEvent::LeftPathStarted { index, id } => {
            format!("debug: left {index} (#{id}) …")
        }
        DebugEvent::LeftPathPruned { id } => {
            format!("debug:   left path #{id} unreachable — pruned")
        }
        DebugEvent::PairChecked {
            id,
            verdict,
            elapsed,
        } => format!(
            "debug:   #{id}  {:<12}  {:.2}s",
            verdict_label(verdict),
            elapsed.as_secs_f64()
        ),
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
}

impl PlainObserver {
    pub fn new() -> Self {
        Self {
            err: std::io::stderr(),
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
        if let Some(line) = plain_line(ev) {
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

/// A two-line `indicatif` display on stderr:
///
/// ```text
/// ⠹ left #3 (path 3)
/// ⠹ pairs   71  ✓2 ·68 ✗1 ?0 ✂12  [0:00:38]
/// ```
///
/// `indicatif` draws nothing when stderr is not a terminal; `main.rs` only
/// constructs this for `--progress bar` or `--progress auto` on a TTY.
pub struct BarObserver {
    mp: MultiProgress,
    left: ProgressBar,
    pairs: ProgressBar,
    tally: Tally,
}

impl BarObserver {
    pub fn new() -> Self {
        let mp = MultiProgress::new();

        let left = mp.add(ProgressBar::new_spinner());
        left.set_style(
            ProgressStyle::with_template("{spinner:.cyan} {msg}")
                .unwrap_or_else(|_| ProgressStyle::default_spinner()),
        );
        left.set_message("left: starting…");
        left.enable_steady_tick(Duration::from_millis(120));

        let pairs = mp.add(ProgressBar::new_spinner());
        pairs.set_style(
            ProgressStyle::with_template(
                "{spinner:.green} pairs {pos:>4}  {msg}  [{elapsed_precise}]",
            )
            .unwrap_or_else(|_| ProgressStyle::default_spinner()),
        );
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
            DebugEvent::LeftPathStarted { index, id } => {
                self.left.set_message(format!("left #{id} (path {index})"));
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
                self.pairs.set_message(self.tally.render());
                if matches!(verdict, Verdict::GoalFails { .. }) {
                    let _ = self.mp.println(format!("⚠ GOAL FAILS at #{id}"));
                }
            }
            DebugEvent::BranchPruned { .. } => {
                self.tally.pruned += 1;
                self.pairs.set_message(self.tally.render());
            }
            DebugEvent::LeftPathFinished { .. } => {}
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
            plain_line(&DebugEvent::Started {
                oracle: "PKENC",
                claim: "same-output",
                admitted: false,
            })
            .unwrap(),
            "debug: PKENC / same-output — exploring"
        );
        assert_eq!(
            plain_line(&DebugEvent::LeftPathStarted { index: 2, id: "2" }).unwrap(),
            "debug: left 2 (#2) …"
        );
        let pc = plain_line(&DebugEvent::PairChecked {
            id: "2.5",
            verdict: &Verdict::Verified,
            elapsed: Duration::from_millis(240),
        })
        .unwrap();
        assert!(pc.starts_with("debug:   #2.5  verified"), "{pc}");
        assert!(pc.ends_with("0.24s"), "{pc}");

        let done = plain_line(&DebugEvent::Finished {
            summary: Summary {
                left_paths: 6,
                right_paths: 96,
                goal_fails: 1,
                ..Summary::default()
            },
            partial: false,
        })
        .unwrap();
        assert!(done.contains("6 left, 96 right"), "{done}");
        assert!(done.contains("1 GOAL FAILS"), "{done}");
        assert!(done.ends_with("(partial: no)"), "{done}");

        assert_eq!(
            plain_line(&DebugEvent::BranchPruned {
                side: Side::Right,
                id: "3.p1",
                label: 14,
            })
            .unwrap(),
            "debug:   pruned #3.p1 at L14 (right)"
        );
    }
}
