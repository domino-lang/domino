use std::fmt::Display;

use crate::{
    package::OracleDef,
    writers::python::{
        identifier::{OracleFunctionName, VariableName},
        statement::PyStatement,
        ty::PyType,
    },
};

pub(crate) struct OracleFunction<'a> {
    oracle: &'a OracleDef,
}

impl<'a> OracleFunction<'a> {
    pub(crate) fn new(oracle: &'a OracleDef) -> Self {
        Self { oracle }
    }
}

pub(crate) enum OracleFunctionArg<'a> {
    GameState,
    OracleArg(&'a str),
}

impl<'a> super::FunctionName for OracleFunctionName<'a> {}
impl<'a> super::FunctionArgName for OracleFunctionArg<'a> {}

impl<'a> Display for OracleFunctionArg<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OracleFunctionArg::GameState => write!(f, "game_state"),
            OracleFunctionArg::OracleArg(variable_name) => write!(f, "{variable_name}"),
        }
    }
}

impl<'a> super::Function<'a> for OracleFunction<'a> {
    type Name = OracleFunctionName<'a>;
    type ArgName = OracleFunctionArg<'a>;

    fn name(&self) -> OracleFunctionName<'a> {
        OracleFunctionName(&self.oracle.sig.name)
    }

    fn args(&self) -> impl IntoIterator<Item = (Self::ArgName, PyType<'a>)> {
        self.oracle.sig.args.iter().map(|(name, ty)| {
            (
                OracleFunctionArg::OracleArg(name.as_str()),
                ty.clone().try_into().unwrap(),
            )
        })
    }

    fn body(&self) -> impl IntoIterator<Item = crate::writers::python::statement::PyStatement<'a>> {
        self.oracle
            .code
            .0
            .iter()
            .map(|stmt| stmt.try_into().unwrap())
    }
}
