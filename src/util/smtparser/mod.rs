// use crate::debug_assert_matches;

pub(crate) mod implementation;

mod functions;
mod model;
mod sampleid;

pub use functions::extract as extract_functions;
pub(crate) use implementation::SmtParser;
pub use model::parse as parse_model;
pub use sampleid::extract as extract_sampleid;

pub use functions::ExtractedFunction;

pub type Error = implementation::Error<implementation::Rule>;
pub type Result<T> = std::result::Result<T, Error>;

#[cfg(test)]
mod test;
