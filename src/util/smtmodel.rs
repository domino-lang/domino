// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::util::smtparser::parse_model;
use crate::writers::smt::exprs::SmtExpr;

/// name and rendered sort of a `define-fun` argument, e.g. `("_arg_1", "Bits_n")`.
pub type SmtModelEntryArg = (String, String);

#[derive(Debug, Clone)]
pub enum SmtModelEntry {
    IntEntry {
        name: String,
        args: Vec<SmtModelEntryArg>,
        value: i32,
    },
    BoolEntry {
        name: String,
        args: Vec<SmtModelEntryArg>,
        value: bool,
    },
    UnknownEntry {
        name: String,
        args: Vec<SmtModelEntryArg>,
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

    /// The `define-fun` argument list. Empty for plain constants.
    pub fn args(&self) -> &[SmtModelEntryArg] {
        match &self {
            SmtModelEntry::IntEntry { args, .. } => args,
            SmtModelEntry::BoolEntry { args, .. } => args,
            SmtModelEntry::UnknownEntry { args, .. } => args,
        }
    }

    /// The raw value expression, regardless of entry kind.
    pub fn value_expr(&self) -> SmtExpr {
        match self {
            SmtModelEntry::IntEntry { value, .. } => SmtExpr::Atom(value.to_string()),
            SmtModelEntry::BoolEntry { value, .. } => SmtExpr::Atom(value.to_string()),
            SmtModelEntry::UnknownEntry { value, .. } => value.clone(),
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

    pub fn entries(&self) -> impl Iterator<Item = &SmtModelEntry> {
        self.values.iter()
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

    /// Unwraps a `String`-sorted entry, stripping the surrounding quotes that
    /// `SmtParser::handle_string` adds around string literals.
    pub fn get_value_as_string(&self, name: &str) -> Option<String> {
        if let Some(SmtModelEntry::UnknownEntry { ty, value, .. }) = self.get_value(name) {
            if ty != "String" {
                return None;
            }

            let rendered = value.to_string();
            let unquoted = rendered.strip_prefix('"')?.strip_suffix('"')?;
            Some(unquoted.to_string())
        } else {
            None
        }
    }
}
