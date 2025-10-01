use std::fmt::Display;

use pretty::RcDoc;

use crate::{
    statement::Statement,
    writers::python::{expression::PyExpression, identifier::VariableName},
};

use super::util::ToDoc;

#[derive(Clone, Copy, Debug)]
pub(crate) struct PyAssignment<'a> {
    lhs: VariableName<'a>,
    rhs: PyExpression<'a>,
}

impl<'a> Display for PyAssignment<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} = {}", self.lhs, self.rhs)
    }
}

impl<'a> ToDoc<'a> for PyAssignment<'a> {
    fn to_doc(&self) -> RcDoc<'a> {
        RcDoc::as_string(&self.lhs)
            .append(RcDoc::text(" = "))
            .append(self.rhs.to_doc())
    }
}

#[derive(Clone, Debug)]
struct PyIfThenElse<'a> {
    cond: PyExpression<'a>,
    then: Vec<PyStatement<'a>>,
    els: Vec<PyStatement<'a>>,
}

impl<'a> ToDoc<'a> for PyIfThenElse<'a> {
    fn to_doc(&self) -> RcDoc<'a> {
        let then = self.then.iter().map(PyStatement::to_doc);
        let doc = RcDoc::text("if ")
            .append(self.cond.to_doc())
            .append(RcDoc::text(":"))
            .append(
                RcDoc::line()
                    .append(RcDoc::intersperse(then, RcDoc::line()))
                    .nest(2),
            );

        if self.els.is_empty() {
            return doc;
        }

        let els = self.els.iter().map(PyStatement::to_doc);

        doc.append(RcDoc::line())
            .append(RcDoc::text("else:"))
            .append(
                RcDoc::line()
                    .append(RcDoc::intersperse(els, RcDoc::line()))
                    .nest(2),
            )
    }
}

#[derive(Clone, Debug)]
pub(crate) enum PyStatement<'a> {
    Assignment(PyAssignment<'a>),
    Return(PyExpression<'a>),
    IfThenElse(PyIfThenElse<'a>),
}

impl<'a> ToDoc<'a> for PyStatement<'a> {
    fn to_doc(&self) -> RcDoc<'a> {
        match self {
            PyStatement::Assignment(py_assignment) => py_assignment.to_doc(),
            PyStatement::Return(py_expression) => {
                RcDoc::text("return ").append(py_expression.to_doc())
            }
            PyStatement::IfThenElse(py_if_then_else) => py_if_then_else.to_doc(),
        }
        .append(RcDoc::line())
    }
}

impl<'a> PyStatement<'a> {
    pub(crate) fn into_doc(self) -> RcDoc<'a> {
        match self {
            PyStatement::Assignment(py_assignment) => py_assignment.to_doc(),
            PyStatement::Return(py_expression) => {
                RcDoc::text("return ").append(py_expression.to_doc())
            }
            PyStatement::IfThenElse(py_if_then_else) => py_if_then_else.to_doc(),
        }
    }
}

impl<'a> TryFrom<&'a Statement> for PyStatement<'a> {
    type Error = ();

    fn try_from(stmt: &'a Statement) -> Result<Self, Self::Error> {
        match stmt {
            Statement::Return(expression, source_span) => Ok(PyStatement::Return(
                expression.as_ref().unwrap().try_into()?,
            )),
            Statement::Assign(identifier, expression, expression1, source_span) => todo!(),
            Statement::IfThenElse(ite) => Ok(PyStatement::IfThenElse(PyIfThenElse {
                cond: PyExpression::try_from(&ite.cond)?,
                then: (&ite.then_block)
                    .0
                    .iter()
                    .map(|stmt| stmt.try_into())
                    .collect::<Result<Vec<_>, _>>()?,
                els: (&ite.else_block)
                    .0
                    .iter()
                    .map(|stmt| stmt.try_into())
                    .collect::<Result<Vec<_>, _>>()?,
            })),
            other => todo!("PyStatement::try_from not yet implemented: {other:?}"),
        }
    }
}

impl<'a> Into<RcDoc<'a>> for PyStatement<'a> {
    fn into(self) -> RcDoc<'a> {
        self.into_doc()
    }
}

impl<'a> Display for PyStatement<'a> {
    fn fmt(&self, w: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.to_doc().render_fmt(100, w)
    }
}
