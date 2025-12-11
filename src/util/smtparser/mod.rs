// use crate::debug_assert_matches;

mod implementation;

mod model;
mod sampleid;

use implementation::SmtParser;
pub use model::parse as parse_model;
pub use sampleid::extract as extract_sampleid;

#[cfg(test)]
mod test;
