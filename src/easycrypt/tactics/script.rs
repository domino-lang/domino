// SPDX-License-Identifier: MIT OR Apache-2.0

//! The script of one oracle's bullet: accepted sentences only, one bullet (`+`) per subgoal,
//! indented by depth as `BranchingAlgorithm.pdf` does (story 27 §3.2.5).
//!
//! Attempts run under `undo`, so the script has marks: [`Script::mark`] before an attempt and
//! [`Script::rollback`] when it is undone, keeping the script equal to "the sentences
//! EasyCrypt accepted, in order".

/// One accepted sentence.
#[derive(Debug, Clone)]
pub(super) struct Line {
    /// Nesting depth: the number of enclosing bullets.
    depth: usize,
    /// The sentence opens a bullet block.
    bullet: bool,
    pub(super) sentence: String,
    /// A `(* domino: … *)` comment, kept after the sentence.
    comment: Option<String>,
}

#[derive(Debug, Clone, Default)]
pub(super) struct Script {
    lines: Vec<Line>,
    depth: usize,
    /// The next sentence is the first of a new bullet block.
    pending_bullet: bool,
}

/// A point to return to.
#[derive(Debug, Clone, Copy)]
pub(super) struct Mark {
    len: usize,
    pending_bullet: bool,
}

impl Script {
    /// Enters the block of the next subgoal: its first sentence is prefixed with `+`.
    pub(super) fn enter_bullet(&mut self) {
        self.depth += 1;
        self.pending_bullet = true;
    }

    pub(super) fn leave_bullet(&mut self) {
        self.depth -= 1;
        self.pending_bullet = false;
    }

    pub(super) fn push(&mut self, sentence: &str, comment: Option<String>) {
        self.lines.push(Line {
            depth: self.depth,
            bullet: std::mem::take(&mut self.pending_bullet),
            sentence: sentence.to_string(),
            comment,
        });
    }

    pub(super) fn mark(&self) -> Mark {
        Mark {
            len: self.lines.len(),
            pending_bullet: self.pending_bullet,
        }
    }

    pub(super) fn rollback(&mut self, mark: Mark) {
        self.lines.truncate(mark.len);
        self.pending_bullet = mark.pending_bullet;
    }

    /// Number of `admit` sentences.
    #[cfg(test)]
    pub(super) fn admit_count(&self) -> usize {
        self.lines
            .iter()
            .filter(|l| l.sentence.starts_with("admit"))
            .count()
    }

    /// The script as text. Depth 1 is the oracle's own bullet (`+ proc; inline.` at column 0);
    /// a block at depth `d` has its bullet at column `2(d-1)` and its other sentences at `2d`.
    pub(super) fn render(&self) -> String {
        let mut out = String::new();
        for line in &self.lines {
            let indent = if line.bullet {
                2 * (line.depth.saturating_sub(1))
            } else {
                2 * line.depth
            };
            for _ in 0..indent {
                out.push(' ');
            }
            if line.bullet {
                out.push_str("+ ");
            }
            out.push_str(&line.sentence);
            if let Some(comment) = &line.comment {
                out.push(' ');
                out.push_str(comment);
            }
            out.push('\n');
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bullets_open_blocks_and_marks_roll_back() {
        let mut s = Script::default();
        s.enter_bullet();
        s.push("proc; inline.", None);
        s.push("sp 1 1.", None);
        s.push("if.", None);
        let mark = s.mark();
        s.enter_bullet();
        s.push("auto => /#.", None);
        s.leave_bullet();
        s.rollback(mark);
        s.enter_bullet();
        s.push("smt().", None);
        s.leave_bullet();
        s.enter_bullet();
        s.push("admit.", Some("(* domino: stuck *)".into()));
        s.leave_bullet();
        assert_eq!(
            s.render(),
            "+ proc; inline.\n  sp 1 1.\n  if.\n  + smt().\n  + admit. (* domino: stuck *)\n"
        );
        assert_eq!(s.admit_count(), 1);
    }
}
