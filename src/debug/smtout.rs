// SPDX-License-Identifier: MIT OR Apache-2.0

//! Per-path SMT files (story 11): a `smt/` tree of runnable cvc5 inputs.
//!
//! Instead of one monolithic `transcript.smt2` (write-ordered, ~3.5 MB base
//! frame + every push/pop for every pair), `domino debug` writes a `smt/` tree
//! whose leaves are **self-contained** queries:
//!
//! ```text
//! smt/
//!   base.smt2          the base frame (declarations, game defs, invariants, claim assumptions)
//!   3/
//!     left.smt2        left path #3's own decls / constraints / return constraint (a delta)
//!     7.smt2           pair #3.7: base ++ left #3 ++ right #3.7 ++ vacuity ++ negated goal
//!
//! ```
//!
//! `<L>` / `<R>` are the **numeric ids the HTML already shows** — left path `#3`
//! → `smt/3/`, right path `#3.7` → `smt/3/7.smt2`.
//!
//! A self-contained pair file runs with no concatenation:
//!
//! ```text
//! cvc5 --lang smt2 smt/3/7.smt2
//! ```
//!
//! and reproduces that pair's verdict: the first `(check-sat)` is the vacuity
//! check (`unsat` ⇒ the pair is unreachable), the second is the negated goal
//! (`sat` ⇒ the claim fails on this pair).
//!
//! Coverage is a flag ([`SmtOut`]): `failures` (default) writes self-contained
//! files only for the pairs you care about; `all` for every pair (one base frame
//! per pair — large); `deltas` writes only `base.smt2` plus the small per-path
//! deltas; `none` writes nothing.
//!
//! [`SmtWriter`] is `Send + Sync` and stateless apart from `root` / `mode` (it
//! only creates directories and truncate-writes files) — story 14 calls it from
//! worker threads.

use std::path::{Path, PathBuf};

use serde_derive::Serialize;

use crate::debug::driver::{DebugRun, LeftPath, RightPath, Verdict};

/// Which pairs get a self-contained `.smt2` file under `<out>/smt/`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum SmtOut {
    /// Write nothing — no `smt/` directory at all.
    None,
    /// Self-contained files for `goal-fails` and `inconclusive` pairs only
    /// (default).
    Failures,
    /// Self-contained files for every explored pair. Writes ~one base frame per
    /// pair — for `kem-dem` `PKENC` that is roughly 3.5 MB × 96 ≈ 340 MB.
    All,
    /// `base.smt2` + per-path deltas only. Small; reassemble with
    /// `cat smt/base.smt2 smt/3/left.smt2 smt/3/7.smt2 | cvc5 --lang smt2 -`.
    Deltas,
}

impl SmtOut {
    fn writes_anything(self) -> bool {
        !matches!(self, SmtOut::None)
    }

    /// Does a pair with this verdict get a `.smt2` file in this mode?
    fn covers(self, verdict: &Verdict) -> bool {
        match self {
            SmtOut::None => false,
            SmtOut::All | SmtOut::Deltas => true,
            SmtOut::Failures => matches!(
                verdict,
                Verdict::GoalFails { .. } | Verdict::Inconclusive { .. }
            ),
        }
    }

    /// In `deltas` mode the per-pair file carries neither the base frame nor the
    /// left path — only the right path and the goal block.
    fn self_contained(self) -> bool {
        !matches!(self, SmtOut::Deltas)
    }
}

/// Header metadata for the emitted files — a snapshot of the run's identity.
struct Meta {
    theorem: String,
    proofstep: usize,
    left_game: String,
    right_game: String,
    oracle: String,
    claim: String,
}

impl Meta {
    fn of(run: &DebugRun) -> Self {
        Self {
            theorem: run.theorem.clone(),
            proofstep: run.proofstep,
            left_game: run.left_game.clone(),
            right_game: run.right_game.clone(),
            oracle: run.oracle.clone(),
            claim: run.claim.clone(),
        }
    }
}

/// Writes the `smt/` tree. Cheap to construct; holds only `root`, `mode`, the
/// run identity, and the already-rendered `base.smt2` body.
pub struct SmtWriter {
    root: PathBuf,
    mode: SmtOut,
    meta: Meta,
    /// The full text of `smt/base.smt2` (preamble + base frame), kept so
    /// self-contained pair files can inline it without re-reading from disk.
    base_body: String,
}

impl SmtWriter {
    /// Creates `<out_dir>/smt/` and writes `smt/base.smt2` (unless
    /// `mode == None`). `base_frame_smt` is [`DebugRun::base_frame_smt`] — the
    /// rendered base declarations, which `domino debug` feeds to a solver whose
    /// options are set through the API rather than the text. A bare
    /// `cvc5 <file>` gets neither, so we prepend the ones the pair files need:
    /// `:incremental` (the file has a `push`/`pop` around the goal and two
    /// `check-sat`s) and `:produce-models` (for `(get-model)`), skipping either
    /// if the base frame already carries it.
    pub fn new(out_dir: &Path, mode: SmtOut, run: &DebugRun) -> std::io::Result<Self> {
        let root = out_dir.join("smt");
        let mut preamble = String::new();
        if !run.base_frame_smt.contains(":incremental")
            && !run.base_frame_smt.contains("incremental true")
        {
            preamble.push_str("(set-option :incremental true)\n");
        }
        if !run.base_frame_smt.contains("produce-models") {
            preamble.push_str("(set-option :produce-models true)\n");
        }
        let base_body = format!("{preamble}{}\n", run.base_frame_smt);

        let writer = Self {
            root,
            mode,
            meta: Meta::of(run),
            base_body,
        };
        if mode.writes_anything() {
            std::fs::create_dir_all(&writer.root)?;
            std::fs::write(writer.root.join("base.smt2"), &writer.base_body)?;
        }
        Ok(writer)
    }

    /// Writes `smt/<lid>/left.smt2`: the left path's own decls, constraints and
    /// return constraint (never the base frame). Called once per explored left
    /// path, before its right sweep. A no-op when `mode == None`.
    pub fn write_left(&self, lid: &str, left: &LeftPath) -> std::io::Result<()> {
        if !self.mode.writes_anything() {
            return Ok(());
        }
        let dir = self.root.join(lid);
        std::fs::create_dir_all(&dir)?;

        let mut s = String::new();
        s.push_str(&self.file_header());
        s.push_str(&format!(
            "; left path #{}   {}\n",
            left.id,
            path_summary(&left.steps, &left.terminal)
        ));
        s.push_str("; a delta — assert on top of base.smt2\n\n");
        for line in &left.smt {
            s.push_str(line);
            s.push('\n');
        }
        std::fs::write(dir.join("left.smt2"), s)
    }

    /// Writes `smt/<lid>/<r>.smt2` for right path `<lid>.<r>` when `mode` covers
    /// `verdict`. `<r>` is the numeric tail of `rid` (`"3.7"` → `7`). A no-op
    /// when the mode does not cover this verdict.
    pub fn write_pair(
        &self,
        lid: &str,
        left: &LeftPath,
        right: &RightPath,
        goal_smt: &str,
    ) -> std::io::Result<()> {
        if !self.mode.covers(&right.verdict) {
            return Ok(());
        }
        let dir = self.root.join(lid);
        std::fs::create_dir_all(&dir)?;
        let rtail = right.id.rsplit('.').next().unwrap_or(&right.id);

        let self_contained = self.mode.self_contained();
        let mut s = String::new();
        s.push_str(&self.file_header());
        s.push_str(&format!(
            "; left path #{}   {}\n",
            left.id,
            path_summary(&left.steps, &left.terminal)
        ));
        s.push_str(&format!(
            "; right path #{}  {}\n",
            right.id,
            path_summary(&right.steps, &right.terminal)
        ));
        s.push_str(&format!(
            "; verdict recorded by `domino debug`: {}\n;\n",
            verdict_slug(&right.verdict)
        ));
        if self_contained {
            s.push_str("; run:  cvc5 --lang smt2 <this file>\n");
        } else {
            s.push_str(&format!(
                "; run:  cat smt/base.smt2 smt/{lid}/left.smt2 smt/{lid}/{rtail}.smt2 \
                 | cvc5 --lang smt2 -\n"
            ));
        }
        s.push_str(
            ";   first  (check-sat)  is the vacuity check   \
             — `unsat` means the pair is unreachable\n",
        );
        s.push_str(
            ";   second (check-sat)  is the negated goal    \
             — `sat` means the claim FAILS on this pair\n\n",
        );

        if self_contained {
            s.push_str("; ---- base frame -------------------------------------------------------\n");
            s.push_str(&self.base_body);
            s.push('\n');
            s.push_str(&format!(
                "; ---- left path #{} -----------------------------------------------------\n",
                left.id
            ));
            for line in &left.smt {
                s.push_str(line);
                s.push('\n');
            }
            s.push('\n');
        }

        s.push_str(&format!(
            "; ---- right path #{} --------------------------------------------------\n",
            right.id
        ));
        for line in &right.smt {
            s.push_str(line);
            s.push('\n');
        }
        s.push('\n');

        s.push_str("; ---- vacuity ----------------------------------------------------------\n");
        s.push_str("(check-sat)\n\n");
        s.push_str("; ---- negated goal -----------------------------------------------------\n");
        s.push_str("(push 1)\n");
        s.push_str(goal_smt);
        s.push('\n');
        s.push_str("(check-sat)\n");
        s.push_str("(get-model)\n");
        s.push_str("(pop 1)\n");

        std::fs::write(dir.join(format!("{rtail}.smt2")), s)
    }

    fn file_header(&self) -> String {
        let m = &self.meta;
        format!(
            "; domino debug — theorem {}, proofstep {}, {} == {}\n; oracle {}, claim {}\n",
            m.theorem, m.proofstep, m.left_game, m.right_game, m.oracle, m.claim
        )
    }
}

fn verdict_slug(v: &Verdict) -> &'static str {
    match v {
        Verdict::Verified => "verified",
        Verdict::Unreachable => "unreachable",
        Verdict::GoalFails { .. } => "goal-fails",
        Verdict::Inconclusive { .. } => "inconclusive",
    }
}

/// `L12 then L19 holds -> L27 return` — a one-line summary of a path's steps and
/// terminal, for the file header comment.
fn path_summary(
    steps: &[crate::debug::driver::StepView],
    terminal: &crate::debug::driver::TerminalView,
) -> String {
    let mut parts: Vec<String> = steps
        .iter()
        .map(|s| format!("L{} {}", s.label, s.decision))
        .collect();
    let term = format!(
        "L{} {}",
        terminal.label,
        if terminal.is_abort { "abort" } else { "return" }
    );
    if parts.is_empty() {
        term
    } else {
        parts.push(format!("-> {term}"));
        parts.join(" ")
    }
}
