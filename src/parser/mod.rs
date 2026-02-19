// SPDX-License-Identifier: MIT OR Apache-2.0

#![allow(clippy::result_large_err)]
// miette currently gives a lot of warnings if we don't have that allows in here
#![allow(unused_assignments)]

pub mod common;
pub mod composition;
pub mod package;

pub mod error;
pub mod theorem;

pub mod ast;
pub mod reduction;

use pest::Parser;
extern crate pest;

use pest::error::Error;
use pest::iterators::Pairs;

use crate::util::scope::Scope;

#[derive(Parser)]
#[grammar = "parser/ssp.pest"]
pub struct SspParser;

#[derive(Debug, Clone)]
pub struct ParseContext<'src> {
    pub file_name: &'src str,
    pub file_content: &'src str,

    pub scope: Scope,
    pub types: Vec<(&'src str, pest::Span<'src>)>,
    pub abstract_types: Vec<(&'src str, pest::Span<'src>)>,
}

impl<'src> ParseContext<'src> {
    pub fn new(file_name: &'src str, file_content: &'src str) -> Self {
        let mut scope = Scope::new();
        scope.enter();
        let types = vec![];
        let abstract_types = vec![];

        Self {
            file_name,
            file_content,
            scope,
            types,
            abstract_types,
        }
    }

    pub fn named_source(&self) -> miette::NamedSource<String> {
        miette::NamedSource::new(self.file_name, self.file_content.to_string())
    }
}

impl SspParser {
    pub fn parse_package<'src>(contents: &'src str) -> Result<Pairs<'src, Rule>, Error<Rule>> {
        SspParser::parse(Rule::package, contents)
    }

    pub fn parse_composition<'src>(contents: &'src str) -> Result<Pairs<'src, Rule>, Error<Rule>> {
        SspParser::parse(Rule::composition, contents)
    }

    pub fn parse_theorem<'src>(contents: &'src str) -> Result<Pairs<'src, Rule>, Error<Rule>> {
        SspParser::parse(Rule::theorem, contents)
    }
}

#[cfg(test)]
pub(crate) mod tests;
