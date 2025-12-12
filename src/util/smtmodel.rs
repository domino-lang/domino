// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::util::smtparser::parse_model;
use crate::writers::smt::exprs::SmtExpr;

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
    pub fn from_string(from: &str) -> Option<Self> {
        if let Ok((model, _len)) = parse_model(from) {
            Some(model)
        } else {
            None
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
