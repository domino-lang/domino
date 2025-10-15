use core::fmt::Display;

use crate::{
    package::Package,
    writers::python::{dataclass::Dataclass, identifier::*, ty::PyType},
};

pub struct PackageStatePattern<'a> {
    pkg: &'a Package,
}

impl<'a> PackageStatePattern<'a> {
    pub fn new(pkg: &'a Package) -> Self {
        Self { pkg }
    }
}

impl<'a> Dataclass<'a> for PackageStatePattern<'a> {
    type Name = PackageStateTypeName<'a>;

    fn name(&self) -> PackageStateTypeName<'a> {
        PackageStateTypeName(self.pkg.name())
    }

    fn fields(&self) -> impl IntoIterator<Item = (impl Display, PyType<'a>)> {
        self.pkg
            .state
            .iter()
            .map(|(name, ty, _)| (PackageStateFieldName(name.as_str()), ty.try_into().unwrap()))
    }
}
