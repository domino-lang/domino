use std::collections::HashMap;

use crate::{BuiltinType, BuiltinValue};

/// Each context allows different binders for identifiers.
pub trait Declaration: From<BuiltinType> + From<BuiltinValue> {
    fn decl_type(&self) -> DeclarationType;
}

/// What sort of object an identifier refers to
#[derive(Debug, Clone, Copy)]
pub enum DeclarationType {
    Game,
    Package,
    PackageInstance,
    Oracle,
    Type,
    PureValue,
    Value,
}

#[derive(Default, Debug, Clone)]
pub(crate) struct Frame<Decl>(HashMap<String, Decl>);

impl<Decl: Declaration> Frame<Decl> {
    fn base() -> Self {
        let mut frame = Self::new();

        frame.set("Integer", BuiltinType::Integer.into());
        frame.set("Bool", BuiltinType::Bool.into());
        frame.set("Maybe", BuiltinType::Maybe.into());
        frame.set("Bits", BuiltinType::Bits.into());
        frame.set("Table", BuiltinType::Table.into());

        frame.set("true", crate::BuiltinValue::True.into());
        frame.set("false", crate::BuiltinValue::False.into());
        frame.set("None", crate::BuiltinValue::None.into());
        frame.set("Some", crate::BuiltinValue::Some.into());

        frame
    }

    fn new() -> Self {
        Self(HashMap::new())
    }

    pub(crate) fn set(&mut self, name: &str, decl: Decl) -> Option<Decl> {
        self.0.insert(name.to_string(), decl)
    }

    pub(crate) fn get(&self, name: &str) -> Option<&Decl> {
        self.0.get(name)
    }
}

#[derive(Debug, Clone)]
pub(crate) struct Scope<Decl>(Vec<Frame<Decl>>);

impl<Decl: Declaration> Scope<Decl> {
    pub(crate) fn new() -> Self {
        Self(vec![Frame::base()])
    }

    pub(crate) fn enter(&mut self) {
        self.0.push(Frame::new());
    }

    pub(crate) fn leave(&mut self) {
        self.0.pop();
    }

    pub(crate) fn declare(&mut self, name: &str, decl: Decl) -> Option<Decl> {
        // Ensure the name is a plausible identifier. This helps catching bugs early.
        // Three checks:
        // 1. first is ascii alphabetic or underscore
        // 2. first exists (.unwrap_or(false)), i.e. name not the empty string
        // 3. all are underscore or ascii alphanumeric
        debug_assert!({
            let mut chars = name.chars().peekable();
            let first = chars.peek();

            let nonempty_and_first_is_no_number =
                first.map(|c| !c.is_ascii_digit()).unwrap_or(false);
            let all_are_alnum_or_underscore =
                chars.all(|c: char| c.is_ascii_alphanumeric() || c == '_');

            nonempty_and_first_is_no_number && all_are_alnum_or_underscore
        });

        // XXX: should we really just write to the first frame here? This means we only report
        // re-definitions of they happen in the same frame, not if we shadow.
        self.0.last_mut().unwrap().set(name, decl)
    }

    pub(crate) fn lookup(&self, name: &str) -> Option<&Decl> {
        self.0.iter().rev().find_map(|f| f.get(name))
    }
}

impl core::fmt::Display for DeclarationType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DeclarationType::Package => f.write_str("package"),
            DeclarationType::PackageInstance => f.write_str("package instance"),
            DeclarationType::Game => f.write_str("game"),
            DeclarationType::Oracle => f.write_str("oracle"),

            DeclarationType::Type => f.write_str("type"),
            DeclarationType::PureValue => f.write_str("pure value"),
            DeclarationType::Value => f.write_str("value"),
        }
    }
}
