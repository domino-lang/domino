use core::fmt::Display;
use std::marker::PhantomData;

use pretty::RcDoc;

use crate::writers::python::{statement::PyStatement, ty::PyType};

use super::util::{commasep::CommaSep, ToDoc};

pub(crate) mod oracle;
pub(crate) mod pure;

pub(crate) trait Function<'a> {
    type Name: FunctionName;
    type ArgName: FunctionArgName;

    fn name(&self) -> Self::Name;
    fn args(&self) -> impl IntoIterator<Item = (Self::ArgName, PyType<'a>)>;
    fn body(&self) -> impl IntoIterator<Item = PyStatement<'a>>;
}

/// a marker trait
pub(crate) trait FunctionName: Display + core::fmt::Debug {}

/// a marker trait
pub(crate) trait FunctionArgName: Display {}

pub(crate) struct FunctionDefinitionWriter<'a, Fun: Function<'a>>(pub Fun, PhantomData<&'a ()>);

impl<'a, Fun: Function<'a>> FunctionDefinitionWriter<'a, Fun> {
    pub(crate) fn new(function: Fun) -> Self {
        Self(function, PhantomData)
    }
}

impl<'a, Fun: Function<'a>> Display for FunctionDefinitionWriter<'a, Fun> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.to_doc().render_fmt(100, f)
    }
}

impl<'a, Fun: Function<'a>> ToDoc<'a> for FunctionDefinitionWriter<'a, Fun> {
    fn to_doc(&self) -> pretty::RcDoc<'a> {
        let Self(fun, _) = self;
        let args = fun
            .args()
            .into_iter()
            .map(|(name, _)| RcDoc::as_string(name));
        let body = fun.body().into_iter().map(PyStatement::into_doc);

        RcDoc::text("fun ")
            .append(RcDoc::as_string(fun.name()))
            .append(RcDoc::text("("))
            .append(RcDoc::intersperse(args, ", "))
            .append(RcDoc::text("):"))
            .append(
                RcDoc::line()
                    .append(RcDoc::intersperse(body, RcDoc::line()))
                    .nest(2),
            )
    }
}
