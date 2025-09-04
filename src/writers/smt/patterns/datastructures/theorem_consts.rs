use crate::{
    theorem::Theorem,
    types::Type,
    writers::smt::{
        exprs::SmtExpr,
        names::{FunctionNameBuilder, SortNameBuilder},
        patterns::{DatastructurePattern, DatastructureSpec},
    },
};

#[derive(Debug, Clone)]
pub struct TheoremConstsPattern<'a> {
    pub theorem_name: &'a str,
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct TheoremConstsSelector<'a> {
    pub(crate) name: &'a str,
    pub(crate) ty: &'a Type,
}

impl<'a> DatastructurePattern<'a> for TheoremConstsPattern<'a> {
    type Constructor = ();

    type Selector = TheoremConstsSelector<'a>;

    type DeclareInfo = Theorem<'a>;

    const CAMEL_CASE: &'static str = "TheoremConsts";

    const KEBAB_CASE: &'static str = "theorem-consts";

    fn sort_name(&self) -> String {
        SortNameBuilder::new()
            .push(Self::CAMEL_CASE)
            .push(self.theorem_name)
            .build()
    }

    fn constructor_name(&self, _cons: &Self::Constructor) -> String {
        FunctionNameBuilder::new()
            .push("mk")
            .push(Self::KEBAB_CASE)
            .push(self.theorem_name)
            .build()
    }

    fn selector_name(&self, sel: &Self::Selector) -> String {
        FunctionNameBuilder::new()
            .push(Self::KEBAB_CASE)
            .push(self.theorem_name)
            .push(sel.name)
            .build()
    }

    fn selector_sort(&self, sel: &Self::Selector) -> SmtExpr {
        sel.ty.into()
    }

    fn datastructure_spec(&self, info: &'a Self::DeclareInfo) -> DatastructureSpec<'a, Self> {
        let fields = info
            .consts
            .iter()
            // function parameters are just declared as smtlib functions globally, so we don't
            // want them to be part of this datatype. This way we also stay compatible with
            // solvers that don't support higher-order functions.
            .filter(|(_name, ty)| !matches!(ty, crate::types::Type::Fn(_, _)))
            .map(|(name, ty)| TheoremConstsSelector { name, ty })
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
