// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::{
    types::Type,
    writers::smt::{
        exprs::{SmtAs, SmtExpr},
        sorts::Sort,
    },
};

use super::{DatastructurePattern, DatastructureSpec};

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum ReturnValueConstructor {
    Return,
    Abort,
}

#[derive(PartialEq, Eq, Debug)]
pub struct ReturnValueSelector;

#[derive(PartialEq, Eq)]
pub struct ReturnValue<'a> {
    pub inner_type: &'a Type,
}

impl<'a> ReturnValue<'a> {
    pub fn new(inner_type: &'a Type) -> Self {
        Self { inner_type }
    }
}

impl<'a> DatastructurePattern<'a> for ReturnValue<'a> {
    type Constructor = ReturnValueConstructor;

    type Selector = ReturnValueSelector;

    type DeclareInfo = ();

    const CAMEL_CASE: &'static str = "ReturnValue";

    const KEBAB_CASE: &'static str = "return-value";

    fn sort_name(&self) -> String {
        "ReturnValue".to_string()
    }

    fn sort_par_count(&self) -> usize {
        1
    }

    fn constructor_name(&self, cons: &Self::Constructor) -> String {
        match cons {
            ReturnValueConstructor::Return => "mk-return-value",
            ReturnValueConstructor::Abort => "mk-abort",
        }
        .to_string()
    }

    fn selector_name(&self, _sel: &Self::Selector) -> String {
        "return-value".to_string()
    }

    fn selector_sort(&self, _sel: &Self::Selector) -> crate::writers::smt::exprs::SmtExpr {
        self.inner_type.into()
    }

    fn datastructure_spec(
        &self,
        _info: &'a Self::DeclareInfo,
    ) -> super::DatastructureSpec<'a, Self> {
        DatastructureSpec(vec![
            (ReturnValueConstructor::Return, vec![ReturnValueSelector]),
            (ReturnValueConstructor::Abort, vec![]),
        ])
    }

    fn matchfield_name(&self, _sel: &Self::Selector) -> String {
        "returnvalue".to_string()
    }

    // we need to override the default implementation, because we have to wrap "mk-abort" in an
    // `as`.
    fn call_constructor<F>(
        &self,
        spec: &DatastructureSpec<'a, Self>,
        type_parameters: Vec<Sort>,
        con: &Self::Constructor,
        mut f: F,
    ) -> Option<SmtExpr>
    where
        F: FnMut(&Self::Selector) -> Option<SmtExpr>,
    {
        if *con == ReturnValueConstructor::Abort {
            return Some(
                SmtAs {
                    term: "mk-abort",
                    sort: self.sort(type_parameters),
                }
                .into(),
            );
        }

        let (con, sels) = spec.0.iter().find(|(cur_con, _sels)| con == cur_con)?;

        // smt-lib doesn't like parens around constructors without any fields/selectors
        if sels.is_empty() {
            return Some(self.constructor_name(con).into());
        }

        let mut call = Vec::with_capacity(sels.len() + 1);
        call.push(self.constructor_name(con).into());
        for sel in sels {
            call.push(f(sel)?);
        }

        Some(SmtExpr::List(call))
    }
}
