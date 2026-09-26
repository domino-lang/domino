// SPDX-License-Identifier: MIT OR Apache-2.0

//! The script of one oracle's bullet: accepted sentences only, one bullet (`+`) per subgoal,
//! indented by depth as `BranchingAlgorithm.pdf` does (story 27 §3.2.5).
//!
//! Attempts run under `undo`, so the script has marks: [`Script::mark`] before an attempt and
//! [`Script::rollback`] when it is undone, keeping the script equal to "the sentences
//! EasyCrypt accepted, in order".
//!
//! [`Script::sealed`] is the **seal** (story 33): a copy of the script with every goal the
//! oracle still has open closed by a labelled `admit`, so it is a complete bullet. Nothing is
//! sent to EasyCrypt for it. EasyCrypt's bullets do not focus (no `strict_bullets` pragma), so
//! `n` admits close `n` goals wherever they stand; the seal still places each in the bullet
//! the walk would have given it, from the goal count recorded at each [`Script::enter_bullet`].

use crate::easycrypt::job::NodeRecord;

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
    /// The joint node the walk was in (`N<k>`); `None` in the router prelude.
    node: Option<usize>,
}

#[derive(Debug, Clone, Default)]
pub(super) struct Script {
    lines: Vec<Line>,
    /// The joint node new sentences belong to (see [`Line::node`]).
    node: Option<usize>,
    depth: usize,
    /// The next sentence is the first of a new bullet block.
    pending_bullet: bool,
    /// For each open block, outermost first: how many goals were open (in the whole session)
    /// when it was entered, its own in front. Always `depth` long.
    open_at_entry: Vec<usize>,
}

/// A point to return to.
#[derive(Debug, Clone, Copy)]
pub(super) struct Mark {
    len: usize,
    pending_bullet: bool,
}

impl Script {
    /// Enters the block of the next subgoal, the front one of the `open` goals open now: its
    /// first sentence is prefixed with `+`.
    pub(super) fn enter_bullet(&mut self, open: usize) {
        self.depth += 1;
        self.pending_bullet = true;
        self.open_at_entry.push(open);
    }

    pub(super) fn leave_bullet(&mut self) {
        self.depth -= 1;
        self.pending_bullet = false;
        self.open_at_entry.pop();
    }

    pub(super) fn push(&mut self, sentence: &str, comment: Option<String>) {
        self.lines.push(Line {
            depth: self.depth,
            bullet: std::mem::take(&mut self.pending_bullet),
            sentence: sentence.to_string(),
            comment,
            node: self.node,
        });
    }

    /// The joint node the sentences pushed from now on belong to.
    pub(super) fn set_node(&mut self, node: Option<usize>) {
        self.node = node;
    }

    /// The sentences of the script per joint node (`N<k>`, or `router`), in the order the nodes
    /// first appear, each node's sentences in script order (story 37's `nodes`).
    pub(super) fn by_node(&self) -> Vec<NodeRecord> {
        let mut nodes: Vec<NodeRecord> = Vec::new();
        for line in &self.lines {
            let id = line.node.map_or_else(|| "router".to_string(), |n| format!("N{n}"));
            match nodes.iter_mut().find(|n| n.id == id) {
                Some(node) => node.tactics.push(line.sentence.clone()),
                None => nodes.push(NodeRecord {
                    id,
                    tactics: vec![line.sentence.clone()],
                }),
            }
        }
        nodes
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

    /// The seal: a copy whose every goal of the oracle still open (of the `open` goals open
    /// in the session now) is closed with `admit.` and `label`, and how many admits that took.
    ///
    /// The goals of the current block come first: its front goal is admitted in the block
    /// itself, or, when the block's last tactic left several, each in a bullet of its own.
    /// Then, block by block outwards, the goals that were waiting behind it when it was
    /// entered, each in a bullet next to it. The goals behind the oracle's own are other
    /// oracles' and are left alone.
    ///
    /// Before the first sentence of the oracle, and once its bullet is closed, there is
    /// nothing to seal: the copy is the script as it is.
    pub(super) fn sealed(&self, open: usize, label: &str) -> (Script, usize) {
        let mut sealed = self.clone();
        let Some(&oracle_entry) = self.open_at_entry.first() else {
            return (sealed, 0);
        };
        if self.lines.is_empty() {
            return (sealed, 0);
        }
        // goal counts include the goal in front of each block: `open + 1 - entry` is how many
        // of the open goals were made inside the block
        let mut remaining = (open + 1).saturating_sub(oracle_entry);
        let total = remaining;
        let mut admit_at = |sealed: &mut Script, depth: usize, bullet: bool, n: usize| {
            let n = n.min(remaining);
            for _ in 0..n {
                sealed.depth = depth;
                sealed.pending_bullet = bullet;
                sealed.push("admit.", Some(label.to_string()));
            }
            remaining -= n;
        };
        let depth = self.depth;
        let here = (open + 1).saturating_sub(self.open_at_entry[depth - 1]);
        if here == 1 || self.pending_bullet {
            admit_at(&mut sealed, depth, self.pending_bullet, 1);
            admit_at(&mut sealed, depth + 1, true, here.saturating_sub(1));
        } else {
            admit_at(&mut sealed, depth + 1, true, here);
        }
        for outer in (1..depth).rev() {
            let waiting = self.open_at_entry[outer].saturating_sub(self.open_at_entry[outer - 1]);
            admit_at(&mut sealed, outer + 1, true, waiting);
        }
        // a count that does not add up still leaves no goal open
        admit_at(&mut sealed, 2, true, usize::MAX);
        sealed.depth = 0;
        sealed.pending_bullet = false;
        sealed.open_at_entry.clear();
        (sealed, total)
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

    fn node(id: &str, tactics: &[&str]) -> NodeRecord {
        NodeRecord {
            id: id.to_string(),
            tactics: tactics.iter().map(|t| t.to_string()).collect(),
        }
    }

    #[test]
    fn sentences_are_grouped_by_the_node_they_were_accepted_in() {
        let mut s = Script::default();
        s.enter_bullet(1);
        s.push("proc; inline.", None);
        s.set_node(Some(0));
        s.push("sp 1 1.", None);
        s.set_node(Some(3));
        s.push("auto.", None);
        s.set_node(Some(0));
        s.push("smt().", None);
        assert_eq!(
            s.by_node(),
            vec![
                node("router", &["proc; inline."]),
                node("N0", &["sp 1 1.", "smt()."]),
                node("N3", &["auto."]),
            ]
        );
    }

    #[test]
    fn bullets_open_blocks_and_marks_roll_back() {
        let mut s = Script::default();
        s.enter_bullet(1);
        s.push("proc; inline.", None);
        s.push("sp 1 1.", None);
        s.push("if.", None);
        let mark = s.mark();
        s.enter_bullet(2);
        s.push("auto => /#.", None);
        s.leave_bullet();
        s.rollback(mark);
        s.enter_bullet(2);
        s.push("smt().", None);
        s.leave_bullet();
        s.enter_bullet(1);
        s.push("admit.", Some("(* domino: stuck *)".into()));
        s.leave_bullet();
        assert_eq!(
            s.render(),
            "+ proc; inline.\n  sp 1 1.\n  if.\n  + smt().\n  + admit. (* domino: stuck *)\n"
        );
        assert_eq!(s.admit_count(), 1);
    }

    const L: &str = "(* L *)";

    /// Hello-world's oracle part way through: its goal was in front of 4 goals of other
    /// oracles, the router prelude's `if.` made 3, the condition closed, and the walk is on the
    /// guarded body.
    fn mid_oracle() -> Script {
        let mut s = Script::default();
        s.enter_bullet(5);
        s.push("proc; inline.", None);
        s.push("sp 1 1.", None);
        s.push("if.", None);
        s.enter_bullet(7);
        s.push("auto => /#.", None);
        s.leave_bullet();
        s.enter_bullet(6);
        s.push("sp 3 2.", None);
        s
    }

    #[test]
    fn a_seal_closes_the_current_block_then_each_outer_sibling_in_its_own_bullet() {
        let s = mid_oracle();
        // 6 goals open: the body in front, the both-aborted case, the 4 of other oracles
        let (sealed, admits) = s.sealed(6, L);
        assert_eq!(admits, 2);
        assert_eq!(
            sealed.render(),
            "+ proc; inline.\n  sp 1 1.\n  if.\n  + auto => /#.\n  + sp 3 2.\n    admit. (* L *)\n  + admit. (* L *)\n"
        );
        // not destructive: the walk goes on from the unsealed script
        assert_eq!(
            s.render(),
            "+ proc; inline.\n  sp 1 1.\n  if.\n  + auto => /#.\n  + sp 3 2.\n"
        );
        assert_eq!(sealed.admit_count(), 2);
    }

    #[test]
    fn a_seal_of_a_closed_block_admits_only_what_follows_it() {
        let s = mid_oracle();
        // the body closed: only the both-aborted case is left of this oracle
        let (sealed, admits) = s.sealed(5, L);
        assert_eq!(admits, 1);
        assert!(sealed
            .render()
            .ends_with("  + sp 3 2.\n  + admit. (* L *)\n"));
    }

    #[test]
    fn a_seal_right_after_a_bullet_opened_gives_that_bullet_its_admit() {
        let mut s = mid_oracle();
        s.push("if.", None); // two program goals where there was one
        s.enter_bullet(7);
        let (sealed, admits) = s.sealed(7, L);
        assert_eq!(admits, 3);
        assert!(
            sealed.render().ends_with(
                "  + sp 3 2.\n    if.\n    + admit. (* L *)\n    + admit. (* L *)\n  + admit. (* L *)\n"
            ),
            "{}",
            sealed.render()
        );
    }

    #[test]
    fn subgoals_not_yet_entered_are_sealed_as_bullets_of_the_block_that_made_them() {
        let mut s = Script::default();
        s.enter_bullet(5);
        s.push("proc; inline.", None);
        s.push("if.", None); // 3 goals where there was 1
        let (sealed, admits) = s.sealed(7, L);
        assert_eq!(admits, 3);
        assert_eq!(
            sealed.render(),
            "+ proc; inline.\n  if.\n  + admit. (* L *)\n  + admit. (* L *)\n  + admit. (* L *)\n"
        );
    }

    #[test]
    fn nothing_to_seal_before_the_first_sentence_or_after_the_oracle() {
        let mut s = Script::default();
        assert_eq!(s.sealed(3, L).1, 0);
        s.enter_bullet(3);
        // nothing accepted yet: the export's `+ proc; inline. admit.` stands
        let (sealed, admits) = s.sealed(3, L);
        assert_eq!((admits, sealed.render()), (0, String::new()));
        s.push("proc; inline.", None);
        s.push("auto => /#.", None);
        s.leave_bullet();
        let (sealed, admits) = s.sealed(2, L);
        assert_eq!((admits, sealed.render()), (0, s.render()));
    }
}
