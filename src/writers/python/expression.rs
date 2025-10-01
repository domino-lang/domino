use std::fmt::{write, Display};

use pretty::RcDoc;

use crate::expressions::Expression;

use super::util::ToDoc;

#[derive(Clone, Copy, Debug)]
pub struct PyFunctionCall<'a> {
    fun_name: &'a dyn super::function::FunctionName,
    args: &'a [PyExpression<'a>],
}

impl<'a> Display for PyFunctionCall<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let name = self.fun_name;
        let comma_separated_args = super::util::commasep::CommaSep::new(self.args.iter());

        write!(f, "{name}({comma_separated_args})")
    }
}

impl<'a> ToDoc<'a> for PyFunctionCall<'a> {
    fn to_doc(&self) -> RcDoc<'a> {
        let args = self.args.iter().map(PyExpression::to_doc);
        RcDoc::as_string(self.fun_name)
            .append(RcDoc::text("("))
            .append(RcDoc::intersperse(args, ", "))
            .append(RcDoc::text(")"))
    }
}

#[derive(Clone, Copy, Debug)]
pub enum PyExpression<'a> {
    IntLiteral(isize),
    BoolLiteral(bool),
    None,
    FunctionCall(PyFunctionCall<'a>),
}

impl<'a> Display for PyExpression<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PyExpression::IntLiteral(i) => write!(f, "{i}"),
            PyExpression::BoolLiteral(true) => write!(f, "True"),
            PyExpression::BoolLiteral(false) => write!(f, "False"),
            PyExpression::None => write!(f, "None"),
            PyExpression::FunctionCall(py_function_call) => write!(f, "{py_function_call}"),
        }
    }
}

impl<'a> ToDoc<'a> for PyExpression<'a> {
    fn to_doc(&self) -> RcDoc<'a> {
        match self {
            PyExpression::IntLiteral(i) => RcDoc::as_string(i),
            PyExpression::BoolLiteral(true) => RcDoc::text("True"),
            PyExpression::BoolLiteral(false) => RcDoc::text("False"),
            PyExpression::None => RcDoc::text("None"),
            PyExpression::FunctionCall(py_function_call) => py_function_call.to_doc(),
        }
    }
}

impl<'a> TryFrom<&'a Expression> for PyExpression<'a> {
    type Error = ();

    fn try_from(expr: &'a Expression) -> Result<Self, Self::Error> {
        match expr {
            Expression::Bot => Ok(PyExpression::None),
            Expression::None(_) => Ok(PyExpression::None),
            Expression::IntegerLiteral(i) => todo!(),
            Expression::BooleanLiteral(bit) if bit.as_str() == "true" => {
                Ok(PyExpression::BoolLiteral(true))
            }
            Expression::BooleanLiteral(bit) if bit.as_str() == "false" => {
                Ok(PyExpression::BoolLiteral(false))
            }
            Expression::Some(expression) => expression.as_ref().try_into(),

            Expression::BooleanLiteral(bit) => unreachable!(),

            other => todo!("PyExpression::try_from not yet implemented: {other:?}"),
        }
    }
}
