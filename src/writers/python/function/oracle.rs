use std::fmt::Display;

use pretty::RcDoc;

use crate::{
    package::OracleDef,
    writers::python::{
        identifier::{OracleFunctionArg, OracleFunctionName},
        ty::PyType,
        util::ToDoc,
    },
};

#[derive(Clone, Debug, Copy)]
pub(crate) struct OracleFunction<'a> {
    oracle: &'a OracleDef,
}

impl<'a> OracleFunction<'a> {
    pub(crate) fn new(oracle: &'a OracleDef) -> Self {
        Self { oracle }
    }
}

impl<'a> super::FunctionName for OracleFunctionName<'a> {}
impl<'a> super::FunctionArgName for OracleFunctionArg<'a> {}

impl<'a> Display for OracleFunctionArg<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OracleFunctionArg::GameState => write!(f, "game_state"),
            OracleFunctionArg::PackageInstanceName => write!(f, "pkg_inst_name"),
            OracleFunctionArg::OracleArg(variable_name) => write!(f, "{variable_name}"),
        }
    }
}

impl<'a> ToDoc<'a> for OracleFunctionArg<'a> {
    fn to_doc(&self) -> RcDoc<'a> {
        match self {
            OracleFunctionArg::GameState => RcDoc::text("game_state"),
            OracleFunctionArg::PackageInstanceName => RcDoc::text("pkg_inst_name"),
            OracleFunctionArg::OracleArg(variable_name) => RcDoc::text(*variable_name),
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
        core::iter::once((OracleFunctionArg::GameState, PyType::Any)).chain(
            self.oracle.sig.args.iter().map(|(name, ty)| {
                (
                    OracleFunctionArg::OracleArg(name.as_str()),
                    ty.try_into().unwrap(),
                )
            }),
        )
    }

    fn body(&self) -> impl IntoIterator<Item = crate::writers::python::statement::PyStatement<'a>> {
        self.oracle
            .code
            .0
            .iter()
            .map(|stmt| stmt.try_into().unwrap())
    }
}
