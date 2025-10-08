// These contain testdata
pub(crate) mod games;
pub(crate) mod packages;
pub(crate) mod theorems;

// these contain tests:

/// The complete module contains tests whether things that are supposed to parse actually parse
/// into what is expected.
mod complete;

/// The sound module contains tests whether things that are not supposed to parse actually produce
/// errors - and the right ones.
mod sound;

const TESTDATA_SSPCODE_PATH: &str = "testdata/ssp-code/";

fn slice_source_span<'a>(
    source: &'a miette::NamedSource<String>,
    span: &'a miette::SourceSpan,
) -> &'a str {
    let out = &source.inner().as_str()[span.offset()..(span.offset() + span.len())];

    println!("slice result: `{out}`");

    out
}
