use crate::source::{FileId, SourceLocation};

/// This predicate checks that the char is neither tab nor space, i.e. the characters we defined as
/// WHITESPACE in our grammar.
fn is_neither_tab_nor_space(c: char) -> bool {
    !is_tab_or_space(c)
}

/// This predicate checks that the char is either tab or space, i.e. the characters we defined as
/// WHITESPACE in our grammar.
fn is_tab_or_space(c: char) -> bool {
    matches!(c, ' ' | '\t')
}

/// A helper for trimming trailing whitespace
pub fn trimmed_loc(file_id: FileId, pair: &crate::Pair) -> SourceLocation {
    let span = pair.as_span();
    let text = pair.as_str();

    // (requires)
    // if the span is not empty, it doesn't only consist of Rule::WHITESPACE.
    // This should be guaranteed by pest.
    debug_assert!(
        text.is_empty() || text.contains(is_neither_tab_nor_space),
        "expected pest to guarantee that if span is not empty, it doesn't only consist of Rule::WHITESPACE: {text}"
    );

    // index logic below requires non-empty spans, so we need to handle that case first
    if text.is_empty() {
        return SourceLocation {
            file_id,
            start: span.start() as u32,
            end: span.end() as u32,
        };
    }

    // find the length, i.e. first trailing whitespace char.
    let len = text.trim_end_matches(is_tab_or_space).len();
    let end = len + span.start();

    // (ensures)
    // we don't grow the span accidentally
    debug_assert!(end <= span.end());

    SourceLocation {
        file_id,
        start: span.start() as u32,
        end: end as u32,
    }
}
