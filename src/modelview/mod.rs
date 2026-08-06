// SPDX-License-Identifier: MIT OR Apache-2.0

//! Parses `cvc5` countermodels for Domino proof obligations and renders them in terms of the
//! Domino project they came from (theorem / proof step / oracle / claim, package states, oracle
//! arguments, return values, sampled randomness), instead of raw SMT names.
//!
//! Entry point: [`analyze`].

pub mod ctors;
pub mod render;
pub mod trace;
pub mod value;

use crate::project::Project;
use crate::util::smtmodel::SmtModel;

#[derive(Debug, thiserror::Error, miette::Diagnostic)]
pub enum Error {
    #[error("failed to parse model: {0:?}")]
    ParseError(String),
}

pub type Result<T> = std::result::Result<T, Error>;

pub fn analyze<P: Project>(project: Option<&P>, model_src: &str) -> Result<render::Report> {
    let model = SmtModel::from_string(model_src)
        .ok_or_else(|| Error::ParseError("could not parse model file as an SMT model".into()))?;

    let trace = trace::identify(project, &model);
    Ok(render::render(&trace, &model))
}
