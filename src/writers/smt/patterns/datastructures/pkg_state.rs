// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::{
    expressions::Expression,
    identifier::pkg_ident::PackageConstIdentifier,
    package::Package,
    types::Type,
    writers::smt::{
        contexts::PackageInstanceContext,
        names::{FunctionNameBuilder, SortNameBuilder},
        patterns::instance_names::{encode_params, only_ints},
    },
};

use super::{DatastructurePattern, DatastructureSpec, Datatype};

pub struct PackageStatePattern<'a> {
    pub pkg_name: &'a str,
    pub params: &'a [(PackageConstIdentifier, Expression)],
}

#[derive(PartialEq, Eq, Debug)]
pub struct PackageStateSelector<'a> {
    pub name: &'a str,
    pub ty: &'a Type,
}

pub struct PackageStateDatatype<'a>(PackageInstanceContext<'a>);

impl<'a> PackageInstanceContext<'a> {
    pub fn package_state_datatype(self) -> PackageStateDatatype<'a> {
        PackageStateDatatype(self)
    }
}

impl Datatype for PackageStateDatatype<'_> {
    type Constructor = ();

    type Selector = usize;

    const CAMEL_CASE: &'static str = "PackageState";

    const KEBAB_CASE: &'static str = "pkg-state";

    fn sort_symbol(&self) -> sspverif_smtlib::syntax::tokens::Symbol {
        let encoded_params = encode_params(only_ints(self.0.pkg_params()));

        SortNameBuilder::new()
            .push(Self::CAMEL_CASE)
            .push(self.0.pkg_name())
            .maybe_extend(&encoded_params)
            .build()
            .into()
    }

    fn sort_par_sort_symbols(&self) -> Vec<sspverif_smtlib::syntax::tokens::Symbol> {
        vec![]
    }

    fn constructors(&self) -> impl Iterator<Item = Self::Constructor> {
        Some(()).into_iter()
    }

    fn selectors(&self, _con: &Self::Constructor) -> impl Iterator<Item = Self::Selector> {
        0..self.0.pkg().state.len()
    }

    fn constructor_symbol(
        &self,
        _cons: &Self::Constructor,
    ) -> sspverif_smtlib::syntax::tokens::Symbol {
        let encoded_params = encode_params(only_ints(self.0.pkg_params()));

        FunctionNameBuilder::new()
            .push("mk")
            .push(Self::KEBAB_CASE)
            .push(self.0.pkg_name())
            .maybe_extend(&encoded_params)
            .build()
            .into()
    }

    fn selector_symbol(&self, sel: &Self::Selector) -> sspverif_smtlib::syntax::tokens::Symbol {
        let encoded_params = encode_params(only_ints(self.0.pkg_params()));
        let (param_name, _, _) = &self.0.pkg().state[*sel];

        FunctionNameBuilder::new()
            .push(Self::KEBAB_CASE)
            .push(self.0.pkg_name())
            .maybe_extend(&encoded_params)
            .push(param_name)
            .build()
            .into()
    }

    fn selector_sort(&self, sel: &Self::Selector) -> sspverif_smtlib::syntax::sort::Sort {
        let (_, ty, _) = &self.0.pkg().state[*sel];
        ty.into()
    }
}

impl<'a> DatastructurePattern<'a> for PackageStatePattern<'a> {
    type Constructor = ();
    type Selector = PackageStateSelector<'a>;
    type DeclareInfo = Package;

    const CAMEL_CASE: &'static str = "PackageState";

    const KEBAB_CASE: &'static str = "pkg-state";

    fn sort_name(&self) -> String {
        let encoded_params = encode_params(only_ints(self.params));

        SortNameBuilder::new()
            .push(Self::CAMEL_CASE)
            .push(self.pkg_name)
            .maybe_extend(&encoded_params)
            .build()
    }

    fn constructor_name(&self, _cons: &Self::Constructor) -> String {
        let encoded_params = encode_params(only_ints(self.params));

        FunctionNameBuilder::new()
            .push("mk")
            .push(Self::KEBAB_CASE)
            .push(self.pkg_name)
            .maybe_extend(&encoded_params)
            .build()
    }

    fn selector_name(&self, sel: &Self::Selector) -> String {
        let encoded_params = encode_params(only_ints(self.params));

        FunctionNameBuilder::new()
            .push(Self::KEBAB_CASE)
            .push(self.pkg_name)
            .maybe_extend(&encoded_params)
            .push(sel.name)
            .build()
    }

    fn matchfield_name(&self, sel: &Self::Selector) -> String {
        FunctionNameBuilder::new()
            .push("match")
            .push(sel.name)
            .build()
    }

    fn selector_sort(&self, sel: &Self::Selector) -> crate::writers::smt::exprs::SmtExpr {
        let PackageStateSelector { ty, .. } = sel;
        (*ty).into()
    }

    fn datastructure_spec(&self, pkg: &'a Self::DeclareInfo) -> DatastructureSpec<'a, Self> {
        let selectors = pkg
            .state
            .iter()
            .map(|(name, ty, _file_pos)| PackageStateSelector { name, ty });

        DatastructureSpec(vec![((), selectors.collect())])
    }
}
