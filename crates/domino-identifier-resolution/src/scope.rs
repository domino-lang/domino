// TODO: define default frame. should probably contain builtins

use std::collections::HashMap;

use crate::{BuiltinType, Declaration};

#[derive(Default)]
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
    pub(crate) fn set(&mut self, name: &str, decl: Decl) {
        self.0.insert(name.to_string(), decl);
    }

    pub(crate) fn get(&self, name: &str) -> Option<&Decl> {
        self.0.get(name)
    }
}

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

    pub(crate) fn declare(&mut self, name: &str, decl: Decl) {
        self.0.last_mut().unwrap().set(name, decl);
    }

    pub(crate) fn lookup(&self, name: &str) -> Option<&Decl> {
        self.0.iter().rev().find_map(|f| f.get(name))
    }
}
