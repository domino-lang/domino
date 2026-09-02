// SPDX-License-Identifier: MIT OR Apache-2.0

//! Minimal side-by-side rendering of two inlined listings.
//!
//! This is the shared presentation helper the debugger writes to `inlined.txt`.
//! `domino inline` (story 03) is expected to build its full command on top of
//! this; for now it only needs to be enough for `domino debug` to emit a file
//! the `L<n>` path labels index into.
//!
//! The two columns are numbered **independently**: left line `n` is `Label == n`
//! in the left [`crate::debug::ir::InlinedOracle::listing`], and likewise for the
//! right.

/// Render `left` and `right` (each a `\n`-separated listing) into two
/// line-numbered columns joined by ` | `. The left column is padded to the width
/// of its widest (numbered) line.
pub fn side_by_side(left: &str, right: &str) -> String {
    let number = |text: &str| -> Vec<String> {
        text.lines()
            .enumerate()
            .map(|(i, line)| format!("{:>4} | {}", i + 1, line))
            .collect()
    };

    let left_lines = number(left);
    let right_lines = number(right);

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

#[cfg(test)]
mod tests {
    use super::*;

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
}
