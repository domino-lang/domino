// SPDX-License-Identifier: MIT OR Apache-2.0

//! Progress reporting for `domino easycrypt` (story 21).
//!
//! [`export_theorem_observed`](super::export::export_theorem_observed) and
//! [`write_files_observed`](super::export::write_files_observed) stream
//! [`ExportEvent`]s to an [`ExportObserver`]. Modelled on the debugger's
//! `DebugEvent`/`DebugObserver` (`crate::debug::progress`), deliberately not
//! generalised with it.
//!
//! ## Guarantees
//!
//! - Events are emitted synchronously at points the exporter already passes
//!   through, **before** the item they name is built. So when an export fails,
//!   the last event an observer saw is the item that failed.
//! - Nothing an observer does can change the exported files or stdout: the
//!   exporter never reads anything back from it.
//! - [`ExportEvent`] is `#[non_exhaustive]`; a consumer's `match` ends in `_ => {}`.
//!
//! ## Event order
//!
//! ```text
//! ( TheoremStarted
//!     ( PhaseStarted ItemStarted* PhaseFinished )   // transform, types, packages,
//!                                                   // games, invariants, proofs
//!   TheoremFinished )*
//! PhaseStarted{write} ItemStarted* PhaseFinished    // once, over every theorem's files
//! Finished { files_written }
//! ```
//!
//! `domino easycrypt --tactics` (story 28) then adds, per theorem, one more phase:
//!
//! ```text
//! PhaseStarted{tactics} ( ItemStarted GoalFinished* )* PhaseFinished
//! ```
//!
//! its items are the oracles (`Eq_A_B PKENC`), and a `GoalFinished` is one node of the joint
//! tree whose goal was closed or admitted.
//!
//! `index` fields are 1-based. Every theorem is exported in memory before any file
//! is written (a failed export must not leave a half-written tree), which is why
//! `write` is one phase after the last theorem and its item names carry the
//! theorem's directory (`Full4WHS/Comp_H5.ec`).

use std::io::Write as _;

use indicatif::{MultiProgress, ProgressBar, ProgressStyle};

/// The phases of one export, in the order they run. `Write` runs once at the end.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExportPhase {
    Transform,
    Types,
    Packages,
    Games,
    Invariants,
    Proofs,
    Write,
    /// `--tactics`: one item per oracle (story 28).
    Tactics,
}

impl ExportPhase {
    pub fn name(self) -> &'static str {
        match self {
            Self::Transform => "transform",
            Self::Types => "types",
            Self::Packages => "packages",
            Self::Games => "games",
            Self::Invariants => "invariants",
            Self::Proofs => "proofs",
            Self::Write => "write",
            Self::Tactics => "tactics",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ExportEvent<'a> {
    TheoremStarted { name: &'a str, index: usize, total: usize },
    PhaseStarted { phase: ExportPhase, total_items: usize },
    ItemStarted { phase: ExportPhase, name: &'a str, index: usize },
    PhaseFinished { phase: ExportPhase },
    TheoremFinished { name: &'a str },
    Finished { files_written: usize },
    /// `--tactics`: the goal of joint node `goal` (`N7`) of `oracle` is done, closed or admitted.
    GoalFinished { oracle: &'a str, goal: &'a str, admitted: bool },
}

pub trait ExportObserver {
    fn on_event(&mut self, event: &ExportEvent<'_>);
}

/// The null observer: "no progress".
pub struct NopExportObserver;

impl ExportObserver for NopExportObserver {
    fn on_event(&mut self, _: &ExportEvent<'_>) {}
}

/// The export phases of each theorem, as they went by: what the live translation page (story 28)
/// shows before the tactics start.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct PhaseLog {
    /// `(theorem, [(phase name, items)])`, in order. The `write` phase belongs to no theorem and
    /// is under the name `""`.
    pub theorems: Vec<(String, Vec<(&'static str, usize)>)>,
}

impl PhaseLog {
    /// The phases the export went through for `theorem`, followed by the `write` phase.
    pub fn phases_of(&self, theorem: &str) -> Vec<(&'static str, usize)> {
        let of = |name: &str| {
            self.theorems
                .iter()
                .find(|(t, _)| t == name)
                .map(|(_, p)| p.clone())
                .unwrap_or_default()
        };
        let mut phases = of(theorem);
        phases.extend(of(""));
        phases
    }
}

/// Forwards every event to `inner` and remembers the phases in a [`PhaseLog`].
pub struct LoggingExportObserver<'o> {
    inner: &'o mut dyn ExportObserver,
    log: PhaseLog,
    current: String,
}

impl<'o> LoggingExportObserver<'o> {
    pub fn new(inner: &'o mut dyn ExportObserver) -> Self {
        Self { inner, log: PhaseLog::default(), current: String::new() }
    }

    pub fn into_log(self) -> PhaseLog {
        self.log
    }
}

impl ExportObserver for LoggingExportObserver<'_> {
    fn on_event(&mut self, event: &ExportEvent<'_>) {
        match event {
            ExportEvent::TheoremStarted { name, .. } => {
                self.current = name.to_string();
                self.log.theorems.push((name.to_string(), Vec::new()));
            }
            ExportEvent::TheoremFinished { .. } => self.current.clear(),
            ExportEvent::PhaseStarted { phase, total_items } => {
                if self.current.is_empty()
                    && !self.log.theorems.last().is_some_and(|(t, _)| t.is_empty())
                {
                    self.log.theorems.push((String::new(), Vec::new()));
                }
                if let Some((_, phases)) = self.log.theorems.last_mut() {
                    phases.push((phase.name(), *total_items));
                }
            }
            _ => {}
        }
        self.inner.on_event(event);
    }
}

/// Emits `PhaseStarted`, and hands out `ItemStarted`/`PhaseFinished` with the
/// running index, so the exporter's loops stay one line each.
pub(crate) struct PhaseScope<'o> {
    observer: &'o mut dyn ExportObserver,
    phase: ExportPhase,
    next: usize,
}

impl<'o> PhaseScope<'o> {
    pub(crate) fn start(observer: &'o mut dyn ExportObserver, phase: ExportPhase, total_items: usize) -> Self {
        observer.on_event(&ExportEvent::PhaseStarted { phase, total_items });
        Self { observer, phase, next: 1 }
    }

    pub(crate) fn item(&mut self, name: &str) {
        self.observer.on_event(&ExportEvent::ItemStarted {
            phase: self.phase,
            name,
            index: self.next,
        });
        self.next += 1;
    }

    pub(crate) fn finish(self) {
        self.observer.on_event(&ExportEvent::PhaseFinished { phase: self.phase });
    }
}

// ---------------------------------------------------------------------------
// Plain
// ---------------------------------------------------------------------------

/// One line per phase and per item on stderr, e.g. `[Full4WHS 2/2] games 3/7: Comp_H5`.
pub struct PlainExportObserver {
    err: std::io::Stderr,
    theorem: Option<(String, usize, usize)>,
    totals: [usize; 8],
}

impl PlainExportObserver {
    pub fn new() -> Self {
        Self { err: std::io::stderr(), theorem: None, totals: [0; 8] }
    }

    fn prefix(&self, phase: ExportPhase) -> String {
        match (&self.theorem, phase) {
            (Some((name, i, n)), p) if p != ExportPhase::Write => format!("[{name} {i}/{n}] "),
            _ => String::new(),
        }
    }
}

impl Default for PlainExportObserver {
    fn default() -> Self {
        Self::new()
    }
}

impl ExportObserver for PlainExportObserver {
    #[allow(unreachable_patterns)]
    fn on_event(&mut self, event: &ExportEvent<'_>) {
        let line = match event {
            ExportEvent::TheoremStarted { name, index, total } => {
                self.theorem = Some((name.to_string(), *index, *total));
                format!("[{name} {index}/{total}] theorem")
            }
            ExportEvent::PhaseStarted { phase, total_items } => {
                self.totals[*phase as usize] = *total_items;
                format!("{}{}: {total_items} item(s)", self.prefix(*phase), phase.name())
            }
            ExportEvent::ItemStarted { phase, name, index } => format!(
                "{}{} {index}/{}: {name}",
                self.prefix(*phase),
                phase.name(),
                self.totals[*phase as usize]
            ),
            ExportEvent::PhaseFinished { .. } => return,
            ExportEvent::TheoremFinished { name } => {
                let line = format!("[{name}] exported");
                self.theorem = None;
                line
            }
            ExportEvent::Finished { files_written } => format!("done: {files_written} file(s) written"),
            ExportEvent::GoalFinished { oracle, goal, admitted } => {
                format!("  {oracle} {goal}: {}", if *admitted { "admitted" } else { "closed" })
            }
            _ => return,
        };
        let _ = writeln!(self.err, "{line}");
    }
}

// ---------------------------------------------------------------------------
// Bar
// ---------------------------------------------------------------------------

/// One `indicatif` bar per phase on stderr, labelled with the current item.
/// Finished phases stay on screen. Draws nothing when stderr is not a terminal.
pub struct BarExportObserver {
    mp: MultiProgress,
    bar: Option<ProgressBar>,
    theorem: Option<(String, usize, usize)>,
}

impl BarExportObserver {
    pub fn new() -> Self {
        Self { mp: MultiProgress::new(), bar: None, theorem: None }
    }
}

impl Default for BarExportObserver {
    fn default() -> Self {
        Self::new()
    }
}

impl ExportObserver for BarExportObserver {
    #[allow(unreachable_patterns)]
    fn on_event(&mut self, event: &ExportEvent<'_>) {
        match event {
            ExportEvent::TheoremStarted { name, index, total } => {
                self.theorem = Some((name.to_string(), *index, *total));
                let _ = self.mp.println(format!("theorem {name} ({index}/{total})"));
            }
            ExportEvent::PhaseStarted { phase, total_items } => {
                let bar = self.mp.add(ProgressBar::new(*total_items as u64));
                bar.set_style(
                    ProgressStyle::with_template("{prefix:<11} {bar:24.cyan/blue} {pos}/{len}  {msg}")
                        .unwrap_or_else(|_| ProgressStyle::default_bar()),
                );
                bar.set_prefix(phase.name());
                self.bar = Some(bar);
            }
            ExportEvent::ItemStarted { name, index, .. } => {
                if let Some(bar) = &self.bar {
                    bar.set_position(index.saturating_sub(1) as u64);
                    bar.set_message(name.to_string());
                }
            }
            ExportEvent::PhaseFinished { .. } => {
                if let Some(bar) = self.bar.take() {
                    bar.finish_with_message("done");
                }
            }
            ExportEvent::TheoremFinished { .. } => self.theorem = None,
            ExportEvent::GoalFinished { oracle, goal, admitted } => {
                if let Some(bar) = &self.bar {
                    bar.set_message(format!(
                        "{oracle} {goal} {}",
                        if *admitted { "admitted" } else { "closed" }
                    ));
                }
            }
            _ => {}
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
pub(crate) mod tests {
    use super::*;

    /// Records every event as one line: a compact, comparable rendering.
    #[derive(Default)]
    pub(crate) struct Recorder(pub Vec<String>);

    impl ExportObserver for Recorder {
        fn on_event(&mut self, ev: &ExportEvent<'_>) {
            self.0.push(match ev {
                ExportEvent::TheoremStarted { name, index, total } => format!("theorem {name} {index}/{total}"),
                ExportEvent::PhaseStarted { phase, total_items } => format!("phase {} {total_items}", phase.name()),
                ExportEvent::ItemStarted { phase, name, index } => format!("item {} {index} {name}", phase.name()),
                ExportEvent::PhaseFinished { phase } => format!("end {}", phase.name()),
                ExportEvent::TheoremFinished { name } => format!("theorem-end {name}"),
                ExportEvent::Finished { files_written } => format!("finished {files_written}"),
                ExportEvent::GoalFinished { oracle, goal, admitted } => {
                    format!("goal {oracle} {goal} {admitted}")
                }
            });
        }
    }

    #[test]
    fn logging_observer_remembers_phases_per_theorem_and_the_write_phase() {
        let mut inner = Recorder::default();
        let mut log = LoggingExportObserver::new(&mut inner);
        log.on_event(&ExportEvent::TheoremStarted { name: "T", index: 1, total: 1 });
        log.on_event(&ExportEvent::PhaseStarted { phase: ExportPhase::Types, total_items: 2 });
        log.on_event(&ExportEvent::PhaseFinished { phase: ExportPhase::Types });
        log.on_event(&ExportEvent::TheoremFinished { name: "T" });
        log.on_event(&ExportEvent::PhaseStarted { phase: ExportPhase::Write, total_items: 5 });
        let log = log.into_log();
        assert_eq!(log.phases_of("T"), [("types", 2), ("write", 5)]);
        assert_eq!(inner.0.len(), 5, "every event is forwarded");
    }

    #[test]
    fn phase_scope_numbers_items_from_one() {
        let mut rec = Recorder::default();
        let mut scope = PhaseScope::start(&mut rec, ExportPhase::Games, 2);
        scope.item("Comp_A");
        scope.item("Comp_B");
        scope.finish();
        assert_eq!(
            rec.0,
            ["phase games 2", "item games 1 Comp_A", "item games 2 Comp_B", "end games"]
        );
    }
}
