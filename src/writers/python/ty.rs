use core::fmt::Display;

static UNIT: () = ();

use crate::writers::python::identifier::*;

pub(super) struct BitVecLength<'a>(&'a ());

pub(super) enum PyType<'a> {
    BitVec(BitVecLength<'a>),
    Int,
    Bool,
    List(Box<Self>),
    PackageState(&'a str),
}

impl<'a> Display for PyType<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PyType::BitVec(_bit_vec_length) => todo!(),
            PyType::Int => write!(f, "int"),
            PyType::Bool => write!(f, "bool"),
            PyType::List(py_type) => write!(f, "List[{py_type}]"),
            PyType::PackageState(name) => write!(f, "{}", PackageStateTypeName(name)),
        }
    }
}

impl<'a> TryFrom<crate::types::Type> for PyType<'a> {
    type Error = ();

    fn try_from(value: crate::types::Type) -> Result<Self, Self::Error> {
        match value {
            crate::types::Type::Integer => Ok(PyType::Int),
            crate::types::Type::Boolean => Ok(PyType::Bool),
            crate::types::Type::Bits(_count_spec) => Ok(PyType::BitVec(BitVecLength(&UNIT))),
            crate::types::Type::List(ty) => PyType::try_from(*ty).map(Box::new).map(PyType::List),
            _ => todo!(),
        }
    }
}
