// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::{
    expressions::Expression,
    identifier::pkg_ident::PackageConstIdentifier,
    package::{Package, PackageInstance},
    types::Type,
    writers::smt::{
        exprs::{SmtExpr, SmtLet},
        names::{FunctionNameBuilder, SortNameBuilder},
        patterns::{
            instance_names::{encode_params, encode_types, only_ints},
            DatastructurePattern, DatastructureSpec,
        },
    },
};

#[derive(Debug)]
pub struct PackageConstsPattern<'a> {
    pub pkg_name: &'a str,
    pub params: &'a [(PackageConstIdentifier, Expression)],
    pub types: &'a [(String, Type)],
}

#[derive(Debug, PartialEq, Eq)]
pub struct PackageConstsSelector<'a> {
    pub(crate) name: &'a str,
    pub(crate) ty: &'a Type,
}

impl<'a> DatastructurePattern<'a> for PackageConstsPattern<'a> {
    type Constructor = ();

    type Selector = PackageConstsSelector<'a>;

    type DeclareInfo = Package;

    const CAMEL_CASE: &'static str = "PackageConsts";

    const KEBAB_CASE: &'static str = "pkg-consts";

    fn sort_name(&self) -> String {
        let encoded_params = encode_params(only_ints(self.params));
        let encoded_types = encode_types(self.types.iter().map(|(_, ty)| ty));

        SortNameBuilder::new()
            .push(Self::CAMEL_CASE)
            .push(self.pkg_name)
            .maybe_extend(&encoded_params)
            .maybe_extend(&encoded_types)
            .build()
    }

    fn constructor_name(&self, _cons: &Self::Constructor) -> String {
        let encoded_params = encode_params(only_ints(self.params));
        let encoded_types = encode_types(self.types.iter().map(|(_, ty)| ty));

        FunctionNameBuilder::new()
            .push("mk")
            .push(Self::KEBAB_CASE)
            .push(self.pkg_name)
            .maybe_extend(&encoded_params)
            .maybe_extend(&encoded_types)
            .build()
    }

    fn selector_name(&self, sel: &Self::Selector) -> String {
        let encoded_params = encode_params(only_ints(self.params));
        let encoded_types = encode_types(self.types.iter().map(|(_, ty)| ty));

        FunctionNameBuilder::new()
            .push(Self::KEBAB_CASE)
            .push(self.pkg_name)
            .maybe_extend(&encoded_params)
            .maybe_extend(&encoded_types)
            .push(sel.name)
            .build()
    }

    fn selector_sort(&self, sel: &Self::Selector) -> crate::writers::smt::exprs::SmtExpr {
        sel.ty.into()
    }

    fn datastructure_spec(&self, info: &'a Self::DeclareInfo) -> DatastructureSpec<'a, Self> {
        let fields = info
            .params
            .iter()
            // function parameters are just declared as smtlib functions globally, so we don't
            // want them to be part of this datatype. This way we also stay compatible with
            // solvers that don't support higher-order functions.
            .filter(|(_name, ty, _)| !matches!(ty.kind(), crate::types::TypeKind::Fn(_, _)))
            .map(|(name, ty, _)| PackageConstsSelector { name, ty })
            .collect();

        DatastructureSpec(vec![((), fields)])
    }

    fn matchfield_name(&self, sel: &Self::Selector) -> String {
        FunctionNameBuilder::new()
            .push("match")
            .push(sel.name)
            .build()
    }
}

pub fn bind_pkg_consts<Inner: Into<SmtExpr>>(
    pkg_inst: &PackageInstance,
    pkg_consts: &SmtExpr,
    inner: Inner,
) -> SmtLet<Inner> {
    let pattern = PackageConstsPattern {
        pkg_name: pkg_inst.pkg_name(),
        params: &pkg_inst.params,
        types: &pkg_inst.types,
    };
    let spec = pattern.datastructure_spec(&pkg_inst.pkg);

    // unpack the only (constructor, selector_list) pair
    let (_, selectors) = &spec.0[0];

    SmtLet {
        bindings: selectors
            .iter()
            .map(|selector| {
                (
                    selector.name.to_string(),
                    pattern.access_unchecked(selector, pkg_consts.clone()),
                )
            })
            .collect(),
        body: inner,
    }
}
