use crate::writers::python::identifier::{PureFunctionArg, PureFunctionName};

#[derive(Clone, Debug, Copy)]
pub(crate) struct PureFunction<'a> {
    name: &'a str,
    args: &'a [crate::types::Type],
}

impl<'a> super::FunctionName for PureFunctionName<'a> {}
impl<'a> super::FunctionArgName for PureFunctionArg<'a> {}

impl<'a> super::Function<'a> for PureFunction<'a> {
    type Name = PureFunctionName<'a>;

    type ArgName = PureFunctionArg<'a>;

    fn name(&self) -> Self::Name {
        todo!()
    }

    fn args(
        &self,
    ) -> impl IntoIterator<Item = (Self::ArgName, crate::writers::python::ty::PyType<'a>)> {
        todo!();
        None
    }

    fn body(&self) -> impl IntoIterator<Item = crate::writers::python::statement::PyStatement<'a>> {
        todo!();
        None
    }
}
