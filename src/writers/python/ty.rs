use core::fmt::Display;

use pretty::RcDoc;

static UNIT: () = ();

use super::util::ToDoc;
use crate::writers::python::identifier::*;

#[derive(Clone, Copy, Debug)]
pub(super) struct BitVecLength<'a>(&'a ());

#[derive(Clone, Debug)]
pub(super) enum PyType<'a> {
    BitVec(BitVecLength<'a>),
    Int,
    Bool,

    Any,
    List(Box<Self>),
    Dict(Box<Self>, Box<Self>),

    PackageState(PackageStateTypeName<'a>),
    PackageConstParams(PackageConstParamsTypeName<'a>),
    GameState(GameStateTypeName<'a>),
}

impl<'a> ToDoc<'a> for PyType<'a> {
    fn to_doc(&self) -> RcDoc<'a> {
        match self {
            PyType::BitVec(_bit_vec_length) => RcDoc::as_string("bytes"),
            PyType::Int => RcDoc::as_string("int"),
            PyType::Bool => RcDoc::as_string("bool"),

            PyType::Any => RcDoc::as_string("Any"),
            PyType::List(py_type) => RcDoc::text("List[")
                .append(py_type.to_doc())
                .append(RcDoc::text("]")),
            PyType::Dict(k, v) => RcDoc::text("dict[")
                .append(k.to_doc())
                .append(RcDoc::text(", "))
                .append(v.to_doc())
                .append(RcDoc::text("]")),

            PyType::PackageState(name) => RcDoc::as_string(name),
            PyType::PackageConstParams(name) => RcDoc::as_string(name),
            PyType::GameState(name) => RcDoc::as_string(name),
        }
    }
}

impl<'a> Display for PyType<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.to_doc().render_fmt(100, f)
    }
}

impl<'a> TryFrom<&'a crate::types::Type> for PyType<'a> {
    type Error = ();

    fn try_from(value: &'a crate::types::Type) -> Result<Self, Self::Error> {
        match value {
            crate::types::Type::Integer => Ok(PyType::Int),
            crate::types::Type::Boolean => Ok(PyType::Bool),
            crate::types::Type::Bits(_count_spec) => Ok(PyType::BitVec(BitVecLength(&UNIT))),
            crate::types::Type::List(ty) => PyType::try_from(&**ty).map(Box::new).map(PyType::List),
            crate::types::Type::Maybe(ty) => PyType::try_from(&**ty),
            crate::types::Type::Table(k, v) => Ok(PyType::Dict(
                Box::new(PyType::try_from(&**k)?),
                Box::new(PyType::try_from(&**v)?),
            )),
            other => todo!("not implemented yet: {other:?}"),
        }
    }
}
