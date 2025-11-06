use std::{fmt::Display, marker::PhantomData};

use itertools::Itertools;
use pretty::RcDoc;

use crate::{
    expressions::Expression,
    identifier::{pkg_ident::PackageIdentifier, Identifier},
};

use super::{
    dataclass::game_state,
    identifier::{GameStateFieldName, OracleFunctionArg, PackageStateFieldName, PureFunctionName},
    ty::PyType,
    util::ToDoc,
};

#[derive(Clone, Debug)]
pub struct PyFunctionCall<'a, Fun: super::function::Function<'a>> {
    pub(super) fun_name: Fun::Name,
    pub(super) args: Vec<PyExpression<'a>>,
    pub(super) _phantom: PhantomData<Fun>,
}

impl<'a, Fun: super::function::Function<'a>> Display for PyFunctionCall<'a, Fun> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let name = &self.fun_name;
        let comma_separated_args = super::util::commasep::CommaSep::new(self.args.iter());

        write!(f, "{name}({comma_separated_args})")
    }
}

impl<'a, Fun: super::function::Function<'a>> ToDoc<'a> for PyFunctionCall<'a, Fun> {
    fn to_doc(&self) -> RcDoc<'a> {
        let args = self.args.iter().map(PyExpression::to_doc);
        RcDoc::as_string(&self.fun_name)
            .append(RcDoc::text("("))
            .append(RcDoc::intersperse(args, ", "))
            .append(RcDoc::text(")"))
    }
}

#[derive(Clone, Debug)]
pub enum PyExpression<'a> {
    IntLiteral(isize),
    BoolLiteral(bool),
    None,
    OracleCall(PyFunctionCall<'a, super::function::oracle::OracleFunction<'a>>),
    PureFunctionCall(PyFunctionCall<'a, super::function::pure::PureFunction<'a>>),
    PackageStateIdentifier(&'a str),
    ConstIdentifier(&'a str),
    LocalIdentifier(&'a str),
    Equals(Box<Self>, Box<Self>),
    Add(Box<Self>, Box<Self>),
    Not(Box<Self>),
    Sample(PyType<'a>),
    TableAccess(Box<Self>, Box<Self>),
    Tuple(Vec<Self>),
}

impl<'a> Display for PyExpression<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.to_doc().render_fmt(100, f)
    }
}

impl<'a> ToDoc<'a> for PyExpression<'a> {
    fn to_doc(&self) -> RcDoc<'a> {
        match self {
            PyExpression::IntLiteral(i) => RcDoc::as_string(i),
            PyExpression::BoolLiteral(true) => RcDoc::text("True"),
            PyExpression::BoolLiteral(false) => RcDoc::text("False"),
            PyExpression::None => RcDoc::text("None"),
            PyExpression::OracleCall(py_function_call) => py_function_call.to_doc(),
            PyExpression::PureFunctionCall(py_function_call) => py_function_call.to_doc(),
            PyExpression::PackageStateIdentifier(ident) => game_state::package_state(
                OracleFunctionArg::GameState.to_doc(),
                OracleFunctionArg::PackageInstanceName.to_doc(),
            )
            .append(".")
            .append(RcDoc::text(*ident)),
            PyExpression::ConstIdentifier(name) => RcDoc::as_string(OracleFunctionArg::GameState)
                .append(RcDoc::text("."))
                .append(RcDoc::as_string(GameStateFieldName::PackageConstParams(
                    name,
                ))),
            PyExpression::LocalIdentifier(name) => RcDoc::text(*name),
            PyExpression::Equals(left, right) => {
                left.to_doc().append(" == ").append(right.to_doc())
            }
            PyExpression::Add(left, right) => left.to_doc().append(" + ").append(right.to_doc()),
            PyExpression::Not(expr) => RcDoc::text("not ").append(expr.to_doc()),
            PyExpression::Sample(ty) => match ty {
                PyType::BitVec(_) => RcDoc::text("secrets.token_bytes(32)"),
                PyType::Int => RcDoc::text("secrets.randbits(256)"),
                other => todo!("haven't implemented sampling for type {other:?}"),
            },
            PyExpression::TableAccess(expr, idx) => {
                expr.to_doc().append("[").append(idx.to_doc()).append("]")
            }
            PyExpression::Tuple(exprs) => RcDoc::text("(")
                .append(RcDoc::intersperse(
                    exprs.iter().map(PyExpression::to_doc),
                    ", ",
                ))
                .append(")"),
        }
    }
}

impl<'a> TryFrom<&'a Expression> for PyExpression<'a> {
    type Error = ();

    fn try_from(expr: &'a Expression) -> Result<Self, Self::Error> {
        match expr {
            Expression::Bot => Ok(PyExpression::None),
            Expression::None(_) => Ok(PyExpression::None),
            Expression::IntegerLiteral(i) => Ok(PyExpression::IntLiteral(*i as isize)),
            Expression::BooleanLiteral(bit) if bit.as_str() == "true" => {
                Ok(PyExpression::BoolLiteral(true))
            }
            Expression::BooleanLiteral(bit) if bit.as_str() == "false" => {
                Ok(PyExpression::BoolLiteral(false))
            }
            Expression::Some(expression) => expression.as_ref().try_into(),

            Expression::BooleanLiteral(bit) => unreachable!(),

            Expression::Identifier(Identifier::PackageIdentifier(PackageIdentifier::State(
                ident,
            ))) => Ok(PyExpression::PackageStateIdentifier(&ident.name)),

            Expression::Identifier(Identifier::PackageIdentifier(PackageIdentifier::Const(
                ident,
            ))) => Ok(PyExpression::ConstIdentifier(ident.ident_ref())),

            Expression::Identifier(Identifier::PackageIdentifier(PackageIdentifier::Local(
                ident,
            ))) => Ok(PyExpression::LocalIdentifier(ident.ident_ref())),
            Expression::Identifier(Identifier::PackageIdentifier(
                PackageIdentifier::OracleArg(ident),
            )) => Ok(PyExpression::LocalIdentifier(ident.ident_ref())),

            Expression::Equals(items) => {
                assert_eq!(items.len(), 2);

                Ok(PyExpression::Equals(
                    Box::new(items.get(0).unwrap().try_into()?),
                    Box::new(items.get(1).unwrap().try_into()?),
                ))
            }
            Expression::Add(lhs, rhs) => Ok(PyExpression::Add(
                Box::new((&**lhs).try_into()?),
                Box::new((&**rhs).try_into()?),
            )),
            Expression::Not(expr) => Ok(PyExpression::Not(Box::new(PyExpression::try_from(
                &**expr,
            )?))),
            Expression::FnCall(name, args) => Ok(PyExpression::PureFunctionCall(PyFunctionCall {
                fun_name: PureFunctionName(name.ident_ref()),
                args: args.iter().map(|arg| arg.try_into().unwrap()).collect(),
                _phantom: PhantomData,
            })),
            Expression::Unwrap(expr) => PyExpression::try_from(&**expr),
            Expression::TableAccess(ident, idx) => {
                let expr = match ident {
                    Identifier::PackageIdentifier(PackageIdentifier::State(ident)) => {
                        PyExpression::PackageStateIdentifier(&ident.name)
                    }

                    Identifier::PackageIdentifier(PackageIdentifier::Const(ident)) => {
                        PyExpression::ConstIdentifier(ident.ident_ref())
                    }

                    Identifier::PackageIdentifier(PackageIdentifier::Local(ident)) => {
                        PyExpression::LocalIdentifier(ident.ident_ref())
                    }

                    other => todo!("identifier type not handled in table access: {other:?}"),
                };
                Ok(PyExpression::TableAccess(
                    Box::new(expr),
                    Box::new(idx.as_ref().try_into()?),
                ))
            }
            Expression::Tuple(exprs) => Ok(PyExpression::Tuple(
                exprs.iter().map(PyExpression::try_from).try_collect()?,
            )),

            other => todo!("PyExpression::try_from not yet implemented: {other:?}"),
        }
    }
}
