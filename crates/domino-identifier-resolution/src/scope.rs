// TODO: define default frame. should probably contain builtins

use std::collections::HashMap;

use crate::{BuiltinType, Declaration};

#[derive(Default)]
pub(crate) struct Frame(HashMap<String, Declaration>);

impl Frame {
    fn base() -> Self {
        let mut frame = Self::new();

        frame.set("Integer", Declaration::BuiltinType(BuiltinType::Integer));
        frame.set("Bool", Declaration::BuiltinType(BuiltinType::Bool));
        frame.set("Maybe", Declaration::BuiltinType(BuiltinType::Maybe));
        frame.set("Bits", Declaration::BuiltinType(BuiltinType::Bits));
        frame.set("Table", Declaration::BuiltinType(BuiltinType::Table));

        frame.set("true", Declaration::BuiltinValue(crate::BuiltinValue::True));
        frame.set(
            "false",
            Declaration::BuiltinValue(crate::BuiltinValue::False),
        );
        frame.set("None", Declaration::BuiltinValue(crate::BuiltinValue::None));
        frame.set("Some", Declaration::BuiltinValue(crate::BuiltinValue::Some));

        frame
    }
    fn new() -> Self {
        Self(HashMap::new())
    }
    pub(crate) fn set(&mut self, name: &str, decl: Declaration) {
        self.0.insert(name.to_string(), decl);
    }

    pub(crate) fn get(&self, name: &str) -> Option<&Declaration> {
        self.0.get(name)
    }
}

pub(crate) struct Scope(Vec<Frame>);

impl Scope {
    pub(crate) fn new() -> Self {
        Self(vec![Frame::base()])
    }

    pub(crate) fn enter(&mut self) {
        self.0.push(Frame::new());
    }

    pub(crate) fn leave(&mut self) {
        self.0.pop();
    }

    pub(crate) fn declare(&mut self, name: &str, decl: Declaration) {
        self.0.last_mut().unwrap().set(name, decl);
    }

    pub(crate) fn lookup(&self, name: &str) -> Option<&Declaration> {
        self.0.iter().rev().find_map(|f| f.get(name))
    }
}
