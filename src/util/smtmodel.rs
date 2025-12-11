// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::debug_assert_matches;
use crate::writers::smt::exprs::SmtExpr;

use pest::Parser;
extern crate pest;

#[derive(Parser)]
#[grammar = "util/smtmodel.pest"]
struct SmtModelParser;

impl SmtModelParser {
    pub fn parse_model(content: &str) -> Vec<(String, String, String)> {
        let mut ast = SmtModelParser::parse(Rule::model, content).unwrap();
        let ast = ast.next().unwrap();
        debug_assert_matches!(ast.as_rule(), Rule::model);

        ast.into_inner()
            .map(|line| {
                let mut inner = line.into_inner();
                let name = inner.next().unwrap();
                debug_assert_matches!(name.as_rule(), Rule::name);
                let ty = inner.next().unwrap();
                debug_assert_matches!(ty.as_rule(), Rule::ty);
                let value = inner.next().unwrap();
                debug_assert_matches!(value.as_rule(), Rule::value);
                (
                    String::from(name.as_str()),
                    String::from(ty.as_str()),
                    String::from(value.as_str()),
                )
            })
            .collect()
    }
}

#[derive(Debug, Clone)]
pub enum SmtModelEntry {
    IntEntry {
        name: String,
        value: i32,
    },
    BoolEntry {
        name: String,
        value: bool,
    },
    UnknownEntry {
        name: String,
        value: SmtExpr,
        ty: String,
    },
}

impl SmtModelEntry {
    pub fn name(&self) -> &str {
        match &self {
            SmtModelEntry::IntEntry { name, .. } => name,
            SmtModelEntry::BoolEntry { name, .. } => name,
            SmtModelEntry::UnknownEntry { name, .. } => name,
        }
    }
}

#[derive(Debug, Clone)]
pub struct SmtModel {
    pub(super) values: Vec<SmtModelEntry>,
}

impl SmtModel {
    pub fn from_string(from: &str) -> Self {
        let parsed = SmtModelParser::parse_model(from);
        let transformed = parsed
            .into_iter()
            .map(|(name, ty, value)| match ty.as_str() {
                "Int" => SmtModelEntry::IntEntry {
                    name,
                    value: value.parse().unwrap(),
                },
                _ => unimplemented!(),
            })
            .collect();
        Self {
            values: transformed,
        }
    }

    pub fn get_value(&self, name: &str) -> Option<SmtModelEntry> {
        self.values
            .iter()
            .find(|entry| entry.name() == name)
            .cloned()
    }

    pub fn get_value_as_int(&self, name: &str) -> Option<i32> {
        if let Some(SmtModelEntry::IntEntry { value, .. }) = self.get_value(name) {
            Some(value)
        } else {
            None
        }
    }
    pub fn get_value_as_bool(&self, name: &str) -> Option<bool> {
        if let Some(SmtModelEntry::BoolEntry { value, .. }) = self.get_value(name) {
            Some(value)
        } else {
            None
        }
    }
}
