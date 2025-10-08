use core::fmt::Display;

use crate::{
    package::Package,
    writers::python::{dataclass::Dataclass, identifier::*, ty::PyType},
};

pub struct PackageConstParamsPattern<'a> {
    pkg: &'a Package,
}

impl<'a> PackageConstParamsPattern<'a> {
    pub fn new(pkg: &'a Package) -> Self {
        Self { pkg }
    }
}

impl<'a> Dataclass<'a> for PackageConstParamsPattern<'a> {
    type Name = PackageConstParamsTypeName<'a>;

    fn name(&self) -> PackageConstParamsTypeName<'a> {
        PackageConstParamsTypeName(self.pkg.name())
    }

    fn fields(&self) -> impl IntoIterator<Item = (impl Display, PyType<'a>)> {
        self.pkg.state.iter().map(|(name, ty, _)| {
            (
                PackageConstParamsFieldName(name.as_str()),
                ty.clone().try_into().unwrap(),
            )
        })
    }
}
