use std::{fmt::Display, marker::PhantomData};

use pretty::RcDoc;

use crate::{
    expressions::Expression,
    statement::Statement,
    writers::python::{expression::PyExpression, identifier::VariableName},
};

use super::{expression::PyFunctionCall, identifier::OracleFunctionName, ty::PyType, util::ToDoc};

const GAME_STATE_ARGNAME: &str = "game_state";

#[derive(Clone, Debug)]
pub(crate) enum PyPattern<'a> {
    Simple(VariableName<'a>),
    Tuple(Vec<VariableName<'a>>),
}

#[derive(Clone, Debug)]
pub(crate) struct PyAssignment<'a> {
    lhs: PyPattern<'a>,
    rhs: PyExpression<'a>,
}

impl<'a> ToDoc<'a> for PyPattern<'a> {
    fn to_doc(&self) -> RcDoc<'a> {
        match self {
            PyPattern::Simple(variable_name) => RcDoc::as_string(variable_name),
            PyPattern::Tuple(variable_names) => {
                let vars = variable_names.iter().map(RcDoc::as_string);
                RcDoc::text("(")
                    .append(RcDoc::intersperse(vars, ", "))
                    .append(RcDoc::text(")"))
            }
        }
    }
}

impl<'a> ToDoc<'a> for PyAssignment<'a> {
    fn to_doc(&self) -> RcDoc<'a> {
        self.lhs
            .to_doc()
            .append(RcDoc::text(" = "))
            .append(self.rhs.to_doc())
    }
}

#[derive(Clone, Debug)]
pub(crate) struct PyIfThenElse<'a> {
    cond: PyExpression<'a>,
    then: Vec<PyStatement<'a>>,
    els: Vec<PyStatement<'a>>,
}

impl<'a> ToDoc<'a> for PyIfThenElse<'a> {
    fn to_doc(&self) -> RcDoc<'a> {
        let then: Vec<_> = if self.then.is_empty() {
            vec![RcDoc::text("pass")]
        } else {
            self.then.iter().map(PyStatement::to_doc).collect()
        };

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
struct PySample<'a> {
    varname: &'a str,
    ty: PyType<'a>,
}

impl<'a> ToDoc<'a> for PySample<'a> {
    fn to_doc(&self) -> RcDoc<'a> {
        let samplecall = match &self.ty {
            PyType::BitVec(_) => "secrets.token_bytes(32)",
            PyType::Int => "secrets.randbits(256)",
            other => todo!("haven't implemented sampling for type {other:?}"),
        };

        RcDoc::as_string(self.varname)
            .append(RcDoc::text("="))
            .append(samplecall)
    }
}

#[derive(Clone, Debug)]
pub(crate) enum PyStatement<'a> {
    Assignment(PyAssignment<'a>),
    Return(PyExpression<'a>),
    IfThenElse(PyIfThenElse<'a>),
    Abort,
}

impl<'a> ToDoc<'a> for PyStatement<'a> {
    fn to_doc(&self) -> RcDoc<'a> {
        match self {
            PyStatement::Assignment(py_assignment) => py_assignment.to_doc(),
            PyStatement::Return(py_expression) => {
                RcDoc::text("return ").append(py_expression.to_doc())
            }
            PyStatement::IfThenElse(py_if_then_else) => py_if_then_else.to_doc(),
            PyStatement::Abort => RcDoc::text(r#"raise Exception("abort")"#),
        }
    }
}

impl<'a> TryFrom<(&'a str, &'a Statement)> for PyStatement<'a> {
    type Error = ();

    fn try_from(value: (&'a str, &'a Statement)) -> Result<Self, Self::Error> {
        let (pkg_name, stmt) = value;
        match stmt {
            Statement::Return(expression, source_span) => Ok(PyStatement::Return(
                expression.as_ref().unwrap().try_into()?,
            )),
            Statement::Assign(identifier, _, expr, _) => {
                Ok(PyStatement::Assignment(PyAssignment {
                    lhs: PyPattern::Simple(VariableName(identifier.ident_ref())),
                    rhs: expr.try_into()?,
                }))
            }
            Statement::IfThenElse(ite) => Ok(PyStatement::IfThenElse(PyIfThenElse {
                cond: PyExpression::try_from(&ite.cond)?,
                then: (&ite.then_block)
                    .0
                    .iter()
                    .map(|stmt| (pkg_name, stmt).try_into())
                    .collect::<Result<Vec<_>, _>>()?,
                els: (&ite.else_block)
                    .0
                    .iter()
                    .map(|stmt| (pkg_name, stmt).try_into())
                    .collect::<Result<Vec<_>, _>>()?,
            })),
            Statement::Sample(name, _, _, ty, _, _) => Ok(PyStatement::Assignment(PyAssignment {
                lhs: PyPattern::Simple(VariableName(name.ident_ref())),
                rhs: PyExpression::Sample(ty.try_into()?),
            })),
            Statement::InvokeOracle(invoke) => {
                let args: Vec<PyExpression<'a>> =
                    Some(PyExpression::LocalIdentifier(GAME_STATE_ARGNAME))
                        .into_iter()
                        .chain(Some(PyExpression::LocalIdentifier(
                            invoke
                                .target_inst_name
                                .as_ref()
                                .map(String::as_str)
                                .unwrap_or(r#""?? no target instance name set ??""#),
                        )))
                        .chain(invoke.args.iter().map(|expr| expr.try_into().unwrap()))
                        .collect();

                Ok(PyStatement::Assignment(PyAssignment {
                    lhs: PyPattern::Simple(VariableName(invoke.id.ident_ref())),
                    rhs: PyExpression::OracleCall(PyFunctionCall {
                        fun_name: OracleFunctionName {
                            pkg_name,
                            oracle_name: &invoke.name,
                        },
                        args,
                        _phantom: PhantomData,
                    }),
                }))
            }
            Statement::Parse(names, expr, _) => Ok(PyStatement::Assignment(PyAssignment {
                lhs: PyPattern::Tuple(
                    names
                        .iter()
                        .map(|id| VariableName(id.ident_ref()))
                        .collect(),
                ),
                rhs: expr.try_into()?,
            })),
            Statement::Abort(_) => Ok(PyStatement::Abort),
            other => todo!("PyStatement::try_from not yet implemented: {other:?}"),
        }
    }
}

// this is here because it's handy for mapping owned values
impl<'a> PyStatement<'a> {
    pub fn into_doc(self) -> RcDoc<'a> {
        self.to_doc()
    }
}

impl<'a> Into<RcDoc<'a>> for PyStatement<'a> {
    fn into(self) -> RcDoc<'a> {
        self.to_doc()
    }
}

impl<'a> Display for PyStatement<'a> {
    fn fmt(&self, w: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.to_doc().render_fmt(100, w)
    }
}

fn all_unwraps(expr: &Expression) -> Vec<Expression> {
    expr.mapfold(vec![], |mut out, expr| {
        if let Expression::Unwrap(expr) = &expr {
            out.push(expr.as_ref().clone())
        };
        (out, expr)
    })
    .0
}
