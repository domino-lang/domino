pub mod game_consts;
pub mod game_state;
//mod intermediate_state;
mod normal_return;
//mod partial_return;
pub mod pkg_consts;
pub mod pkg_state;
mod return_value;
pub mod theorem_consts;

pub use game_state::*;
//pub use intermediate_state::*;
pub use normal_return::*;
//pub use partial_return::*;
pub use pkg_state::*;
pub use return_value::*;

use sspverif_smtlib::syntax::{
    command::{Command, ConstructorDec, DatatypeDec, SelectorDec},
    sort::Sort as SmtlibSort,
    term::Term,
    tokens::Symbol,
};

use crate::writers::smt::{
    declare::declare_datatype as base_declare_datatype,
    exprs::{SmtExpr, SmtMatch, SmtMatchCase},
    sorts::Sort,
};

pub fn declare_datatype<'a, P: DatastructurePattern<'a>>(
    pattern: &P,
    spec: &DatastructureSpec<'a, P>,
) -> SmtExpr {
    let DatastructureSpec(constructors) = spec;
    let constructors = constructors.iter().map(|(con, sels)| {
        (
            pattern.constructor_name(con),
            sels.iter()
                .map(|sel| (pattern.selector_name(sel), pattern.selector_sort(sel)))
                .collect(),
        )
    });

    base_declare_datatype(&pattern.sort_name(), constructors)
}

pub trait DatastructurePattern<'a> {
    type Constructor: Eq;
    type Selector: Eq;
    type DeclareInfo: 'a;

    const CAMEL_CASE: &'static str;
    const KEBAB_CASE: &'static str;

    fn sort_name(&self) -> String;
    fn sort_par_count(&self) -> usize {
        0
    }

    fn constructor_name(&self, cons: &Self::Constructor) -> String;
    fn selector_name(&self, sel: &Self::Selector) -> String;
    fn selector_sort(&self, sel: &Self::Selector) -> SmtExpr;

    fn datastructure_spec(&self, info: &'a Self::DeclareInfo) -> DatastructureSpec<'a, Self>;

    // fn declare_datatype(&self, spec: &DatastructureSpec<'a, Self>) -> SmtExpr {
    //     let DatastructureSpec(constructors) = spec;
    //     let constructors = constructors.iter().map(|(con, sels)| {
    //         (
    //             self.constructor_name(con),
    //             sels.iter()
    //                 .map(|sel| (self.selector_name(sel), self.selector_sort(sel)))
    //                 .collect(),
    //         )
    //     });
    //
    //     base_declare_datatype(&self.sort().sort_name(), constructors)
    // }

    fn sort(&self, type_parameters: Vec<Sort>) -> Sort {
        debug_assert_eq!(type_parameters.len(), self.sort_par_count());
        Sort::Other(self.sort_name(), type_parameters)
    }

    fn access<S: Into<SmtExpr>>(
        &self,
        spec: &DatastructureSpec<'a, Self>,
        selector: &Self::Selector,
        structure: S,
    ) -> Option<SmtExpr> {
        spec.0.iter().find(|(_con, sels)| sels.contains(selector))?;

        Some(self.access_unchecked(selector, structure))
    }

    fn access_unchecked<S: Into<SmtExpr>>(
        &self,
        selector: &Self::Selector,
        structure: S,
    ) -> SmtExpr {
        (self.selector_name(selector), structure).into()
    }

    fn update<S: Into<SmtExpr>, V: Into<SmtExpr>>(
        &self,
        spec: &DatastructureSpec<'a, Self>,
        selector: &Self::Selector,
        structure: S,
        new_value: V,
    ) -> Option<SmtExpr> {
        let (constructor, selectors) =
            spec.0.iter().find(|(_con, sels)| sels.contains(selector))?;

        let structure: SmtExpr = structure.into();
        let new_value: SmtExpr = new_value.into();

        let mut call: Vec<SmtExpr> = vec![self.constructor_name(constructor).into()];

        call.extend(selectors.iter().map(|cur_sel| {
            if cur_sel == selector {
                new_value.clone()
            } else {
                (self.selector_name(cur_sel), structure.clone()).into()
            }
        }));

        Some(call.into())
    }

    fn matchfield_name(&self, sel: &Self::Selector) -> String;

    fn match_expr<E, F>(&self, expr: E, spec: &DatastructureSpec<'a, Self>, f: F) -> SmtExpr
    where
        E: Into<SmtExpr>,
        F: Fn(&Self::Constructor) -> SmtExpr,
    {
        SmtMatch {
            expr,
            cases: spec
                .0
                .iter()
                .map(|(con, sels)| -> SmtMatchCase<_> {
                    SmtMatchCase {
                        constructor: self.constructor_name(con),
                        args: sels.iter().map(|sel| self.matchfield_name(sel)).collect(),
                        body: f(con),
                    }
                })
                .collect(),
        }
        .into()
    }

    // NOTE: ReturnValue has a custom implementation! make sure to also update that
    fn call_constructor<F>(
        &self,
        spec: &DatastructureSpec<'a, Self>,
        _type_parameters: Vec<Sort>,
        con: &Self::Constructor,
        mut f: F,
    ) -> Option<SmtExpr>
    where
        F: FnMut(&Self::Selector) -> Option<SmtExpr>,
    {
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

#[derive(Debug, Clone)]
pub struct DatastructureSpec<'a, P: DatastructurePattern<'a> + ?Sized>(
    pub Vec<(P::Constructor, Vec<P::Selector>)>,
);

pub trait Datatype {
    type Constructor: Eq;
    type Selector: Eq;

    const CAMEL_CASE: &'static str;
    const KEBAB_CASE: &'static str;

    fn sort_symbol(&self) -> Symbol;
    fn sort_par_sort_symbols(&self) -> Vec<Symbol>;

    fn constructors(&self) -> impl Iterator<Item = Self::Constructor>;
    fn selectors(&self, cons: &Self::Constructor) -> impl Iterator<Item = Self::Selector>;

    fn constructor_symbol(&self, cons: &Self::Constructor) -> Symbol;

    fn selector_symbol(&self, sel: &Self::Selector) -> Symbol;
    fn selector_sort(&self, sel: &Self::Selector) -> SmtlibSort;

    fn selector_dec(&self, sel: &Self::Selector) -> SelectorDec {
        SelectorDec::new(self.selector_symbol(sel), self.selector_sort(sel))
    }

    fn constructor_dec(&self, cons: &Self::Constructor) -> ConstructorDec {
        ConstructorDec::new(
            self.constructor_symbol(cons),
            self.selectors(cons).map(|sel| self.selector_dec(&sel)),
        )
    }

    fn datatype_dec(&self) -> DatatypeDec {
        DatatypeDec::new(
            self.sort_par_sort_symbols(),
            self.constructors().map(|con| self.constructor_dec(&con)),
        )
    }

    fn command(&self) -> Command {
        Command::DeclareDatatype(self.sort_symbol(), self.datatype_dec())
    }

    fn call_constructor(
        &self,
        cons: &Self::Constructor,
        args: impl Fn(&Self::Selector) -> Option<Term>,
    ) -> Option<Term> {
        let args: Option<_> = self.selectors(cons).map(|sel| args(&sel)).collect();

        Some(Term::Base(self.constructor_symbol(cons).into(), args?))
    }

    fn call_selector(&self, sel: &Self::Selector, term: impl Into<Term>) -> Term {
        Term::Base(self.selector_symbol(sel).into(), vec![term.into()])
    }
}
