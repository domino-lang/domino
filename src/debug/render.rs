// SPDX-License-Identifier: MIT OR Apache-2.0

//! Side-by-side rendering of two inlined listings.
//!
//! Two entry points:
//!
//! - [`side_by_side`] / [`columns`] — the low-level column joiner. `domino debug`
//!   writes [`side_by_side`]'s output to `inlined.txt`, the file the `L<n>` path
//!   labels index into.
//! - [`render_side_by_side`] — the full `domino inline` command: transform a
//!   theorem, inline one oracle for both sides of an equivalence proofstep, and
//!   render the result with a header.
//!
//! The two columns are numbered **independently**: left line `n` is `Label == n`
//! in the left [`crate::debug::ir::InlinedOracle::listing`], and likewise for the
//! right. This is the single easiest thing to misread, so the header says so too.

use crate::debug::ir::{inline_oracle, InlineError};
use crate::gamehops::GameHop;
use crate::theorem::Theorem;
use crate::transforms::theorem_transforms::{DebugTransform, EquivalenceTransformError};
use crate::transforms::TheoremTransform;

/// Render `left` and `right` (each a `\n`-separated listing) into two
/// line-numbered columns joined by `  |  `. The left column is padded to the
/// width of its widest (numbered) line.
pub fn side_by_side(left: &str, right: &str) -> String {
    columns(left, right, true)
}

/// Like [`side_by_side`], but `line_numbers = false` drops the numeric gutter
/// (`domino inline --no-line-numbers`). The content is otherwise identical.
pub fn columns(left: &str, right: &str, line_numbers: bool) -> String {
    let prep = |text: &str| -> Vec<String> {
        text.lines()
            .enumerate()
            .map(|(i, line)| {
                if line_numbers {
                    format!("{:>4} | {}", i + 1, line)
                } else {
                    line.to_string()
                }
            })
            .collect()
    };

    let left_lines = prep(left);
    let right_lines = prep(right);

    let left_width = left_lines
        .iter()
        .map(|l| l.chars().count())
        .max()
        .unwrap_or(0);

    let rows = left_lines.len().max(right_lines.len());
    let mut out = String::new();
    for i in 0..rows {
        let l = left_lines.get(i).map(String::as_str).unwrap_or("");
        let r = right_lines.get(i).map(String::as_str).unwrap_or("");
        let pad = left_width.saturating_sub(l.chars().count());
        out.push_str(l);
        out.push_str(&" ".repeat(pad));
        out.push_str("  |  ");
        out.push_str(r);
        out.push('\n');
    }
    out
}

/// Everything `render_side_by_side` can reject before it produces a listing.
///
/// Mirrors the taxonomy of the textual inliner on branch
/// `amir/ty-params-features`. Theorem lookup happens in the caller (it holds the
/// project), so "theorem not found" is not one of these.
#[derive(Debug, thiserror::Error, miette::Diagnostic)]
pub enum RenderError {
    #[error(
        "theorem `{theorem}` has no proofstep {index} \
         (it has {len} proofstep(s), numbered starting at 0)"
    )]
    #[diagnostic(code(inline::proofstep_out_of_range))]
    ProofstepOutOfRange {
        theorem: String,
        index: usize,
        len: usize,
    },

    #[error(
        "proofstep {index} of theorem `{theorem}` is a {kind}; \
         `domino inline` only supports equivalence proofsteps"
    )]
    #[diagnostic(code(inline::not_an_equivalence))]
    ProofstepNotEquivalence {
        theorem: String,
        index: usize,
        kind: &'static str,
    },

    #[error(transparent)]
    #[diagnostic(transparent)]
    Transform(#[from] EquivalenceTransformError),

    #[error(transparent)]
    #[diagnostic(transparent)]
    Inline(#[from] InlineError),
}

/// Render the inlined code of `oracle_name` for both sides of the equivalence
/// proved at `proofstep` of `theorem`, side by side.
///
/// `line_numbers = false` omits the numeric gutter (useful for diffing two runs).
///
/// `theorem` must be the *untransformed* theorem — [`DebugTransform`] is run
/// here.
pub fn render_side_by_side(
    theorem: &Theorem,
    proofstep: usize,
    oracle_name: &str,
    line_numbers: bool,
) -> Result<String, RenderError> {
    use std::fmt::Write as _;

    let hop = theorem
        .game_hops
        .get(proofstep)
        .ok_or_else(|| RenderError::ProofstepOutOfRange {
            theorem: theorem.name.clone(),
            index: proofstep,
            len: theorem.game_hops.len(),
        })?;

    let not_eq = |kind| RenderError::ProofstepNotEquivalence {
        theorem: theorem.name.clone(),
        index: proofstep,
        kind,
    };
    let eq = match hop {
        GameHop::Equivalence(eq) => eq,
        // `prove` treats a hybrid as its underlying equivalence; so do we.
        GameHop::Hybrid(hyb) => hyb.equivalence(),
        GameHop::Reduction(_) => return Err(not_eq("reduction")),
        GameHop::Conjecture(_) => return Err(not_eq("conjecture")),
    };

    let (theorem_dbg, _aux) = DebugTransform.transform_theorem(theorem)?;
    let left_inst = theorem_dbg
        .find_game_instance(eq.left_name())
        .expect("equivalence references a valid left game instance");
    let right_inst = theorem_dbg
        .find_game_instance(eq.right_name())
        .expect("equivalence references a valid right game instance");

    let left_inl = inline_oracle(left_inst, oracle_name)?;
    let right_inl = inline_oracle(right_inst, oracle_name)?;

    let mut out = String::new();
    let _ = writeln!(
        out,
        "theorem {}, proofstep {proofstep} ({} == {}), oracle {oracle_name}",
        theorem.name,
        eq.left_name(),
        eq.right_name(),
    );
    let _ = writeln!(
        out,
        "(left and right line numbers are independent — they index different columns)"
    );
    out.push('\n');
    out.push_str(&columns(
        &left_inl.listing.text,
        &right_inl.listing.text,
        line_numbers,
    ));
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::project::{DirectoryFiles, DirectoryProject, Project as _};
    use std::path::{Path, PathBuf};

    #[test]
    fn columns_are_numbered_independently_and_aligned() {
        let out = side_by_side("a\nbb\nccc", "x\ny");
        let lines: Vec<&str> = out.lines().collect();
        assert_eq!(lines.len(), 3);
        assert!(lines[0].starts_with("   1 | a"));
        assert!(lines[0].contains("|     1 | x"));
        assert!(lines[2].contains("   3 | ccc"));
        // right column ran out of lines but the row is still emitted
        assert!(lines[2].trim_end().ends_with('|'));
        // every row's separator is at the same column
        let sep = lines[0].find("  |  ").unwrap();
        for l in &lines {
            assert_eq!(l.find("  |  "), Some(sep));
        }
    }

    #[test]
    fn columns_without_line_numbers_drop_the_gutter_only() {
        let numbered = columns("a\nbb", "x", true);
        let plain = columns("a\nbb", "x", false);
        assert!(numbered.contains("   1 | a"));
        assert!(!plain.contains(" | a"));
        assert!(plain.starts_with("a  "));
        assert!(plain.contains("  |  x"));
    }

    /// Loads `dir` and hands `f` the raw (untransformed) theorem.
    fn with_raw_theorem(dir: &str, name: &str, f: impl FnOnce(&Theorem)) {
        let files = DirectoryFiles::load(Path::new(dir)).unwrap();
        let project = DirectoryProject::load(PathBuf::from(dir), &files).unwrap();
        let theorem = project.get_theorem(name).unwrap();
        f(theorem);
    }

    #[test]
    fn hello_world_header_and_left_line_numbers_match_labels() {
        with_raw_theorem("example-projects/hello-world", "Proof", |theorem| {
            let out = render_side_by_side(theorem, 0, "UsefulOracle", true).unwrap();

            assert!(out.lines().next().unwrap().starts_with(
                "theorem Proof, proofstep 0 \
                 (medium_composition == small_composition), oracle UsefulOracle"
            ));

            // Body rows start after the header block and its blank separator.
            let body: Vec<&str> = out
                .lines()
                .skip_while(|l| !l.is_empty())
                .skip(1)
                .collect();

            // Re-derive the left listing's sites and check that printed left line
            // `n` really is `Label == n`.
            let (dbg, _) = DebugTransform.transform_theorem(theorem).unwrap();
            let gi = dbg.find_game_instance("medium_composition").unwrap();
            let left = inline_oracle(gi, "UsefulOracle").unwrap();

            for (label, site) in &left.listing.sites {
                let row = body[label - 1];
                let left_cell = row.split("  |  ").next().unwrap();
                let code = left_cell.split_once(" | ").unwrap().1.trim();
                assert_eq!(code, site.line, "printed left line {label} vs site");
            }
        });
    }

    #[test]
    fn no_line_numbers_flag_removes_the_gutter() {
        with_raw_theorem("example-projects/hello-world", "Proof", |theorem| {
            let numbered = render_side_by_side(theorem, 0, "UsefulOracle", true).unwrap();
            let plain = render_side_by_side(theorem, 0, "UsefulOracle", false).unwrap();
            assert!(numbered.contains(" | UsefulOracle("));
            assert!(!plain.contains(" | UsefulOracle("));
            assert!(plain.contains("UsefulOracle()"));
        });
    }

    #[test]
    fn errors_are_specific() {
        with_raw_theorem("example-projects/hello-world", "Proof", |theorem| {
            match render_side_by_side(theorem, 9, "UsefulOracle", true) {
                Err(RenderError::ProofstepOutOfRange { len, .. }) => assert_eq!(len, 2),
                other => panic!("expected ProofstepOutOfRange, got {other:?}"),
            }
            match render_side_by_side(theorem, 1, "UsefulOracle", true) {
                Err(RenderError::ProofstepNotEquivalence { kind, .. }) => {
                    assert_eq!(kind, "reduction")
                }
                other => panic!("expected ProofstepNotEquivalence, got {other:?}"),
            }
            match render_side_by_side(theorem, 0, "NoSuchOracle", true) {
                Err(RenderError::Inline(InlineError::OracleNotExported { .. })) => {}
                other => panic!("expected Inline(OracleNotExported), got {other:?}"),
            }
        });
    }

    #[test]
    fn snapshot_hello_world_useful_oracle() {
        // Fixture regenerated with:
        //   domino inline --proof Proof --proofstep 0 --oracle UsefulOracle \
        //     > testdata/story03/inline-hello-world.txt
        // (run in example-projects/hello-world). Pins the full output, column
        // padding and trailing whitespace included.
        let expected = include_str!("../../testdata/story03/inline-hello-world.txt");
        with_raw_theorem("example-projects/hello-world", "Proof", |theorem| {
            let out = render_side_by_side(theorem, 0, "UsefulOracle", true).unwrap();
            assert_eq!(out, expected);
        });
    }
}
