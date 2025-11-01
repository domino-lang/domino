// SPDX-License-Identifier: MIT OR Apache-2.0

use super::{DatastructurePattern, DatastructureSpec};
use crate::expressions::Expression;
use crate::identifier::game_ident::GameConstIdentifier;
use crate::identifier::pkg_ident::PackageConstIdentifier;
use crate::writers::smt::exprs::SmtExpr;
use crate::writers::smt::patterns::instance_names::{encode_params, only_non_function_expression};

pub struct PartialReturnPattern<'a> {
    pub game_name: &'a str,
    pub game_params: &'a [(GameConstIdentifier, Expression)],
    pub pkg_name: &'a str,
    pub pkg_params: &'a [(PackageConstIdentifier, Expression)],
    pub oracle_name: &'a str,
}

#[derive(PartialEq, Eq)]
pub enum PartialReturnConstructor {
    Return,
    Abort,
}

#[derive(PartialEq, Eq)]
pub enum PartialReturnSelector {
    GameState,
    IntermediateState,
}

impl<'a> DatastructurePattern<'a> for PartialReturnPattern<'a> {
    type Constructor = PartialReturnConstructor;
    type Selector = PartialReturnSelector;
    type DeclareInfo = ();

    const CAMEL_CASE: &'static str = "PartialReturn";
    const KEBAB_CASE: &'static str = "partial-return";

    fn sort_name(&self) -> String {
        let camel_case = PartialReturnPattern::CAMEL_CASE;
        let Self {
            game_name,
            game_params,
            pkg_name,
            pkg_params,
            oracle_name,
        } = self;

        let pkg_params = encode_params(only_non_function_expression(*pkg_params));
        let game_params = encode_params(only_non_function_expression(*game_params));

        format!("<{camel_case}_{game_name}_{game_params}_{pkg_name}_{pkg_params}_{oracle_name}>")
    }

    fn constructor_name(&self, cons: &Self::Constructor) -> String {
        let kebab_case = Self::KEBAB_CASE;
        let Self {
            game_name,
            game_params,
            pkg_name,
            pkg_params,
            oracle_name,
        } = self;

        let pkg_params = encode_params(only_non_function_expression(*pkg_params));
        let game_params = encode_params(only_non_function_expression(*game_params));

        let cons_name = match cons {
            PartialReturnConstructor::Return => kebab_case,
            PartialReturnConstructor::Abort => "partial-abort",
        };

        format!("<mk-{cons_name}-{game_name}-{game_params}-{pkg_name}-{pkg_params}-{oracle_name}>")
    }

    fn selector_name(&self, sel: &Self::Selector) -> String {
        let kebab_case = Self::KEBAB_CASE;
        let Self {
            game_name,
            game_params,
            pkg_name,
            pkg_params,
            oracle_name,
        } = self;

        let pkg_params = encode_params(only_non_function_expression(*pkg_params));
        let game_params = encode_params(only_non_function_expression(*game_params));

        let field_name = match sel {
            PartialReturnSelector::GameState => "game-state",
            PartialReturnSelector::IntermediateState => "intermediate-state",
        };

        format!("<{kebab_case}-{game_name}-{game_params}-{pkg_name}-{pkg_params}-{oracle_name}-{field_name}>")
    }

    fn matchfield_name(&self, sel: &Self::Selector) -> String {
        let field_name = match sel {
            PartialReturnSelector::GameState => "game-state",
            PartialReturnSelector::IntermediateState => "intermediate-state",
        };

        format!("match-{field_name}")
    }

    fn datastructure_spec(&self, _info: &'a Self::DeclareInfo) -> DatastructureSpec<'a, Self> {
        DatastructureSpec(vec![
            (
                PartialReturnConstructor::Return,
                vec![
                    PartialReturnSelector::GameState,
                    PartialReturnSelector::IntermediateState,
                ],
            ),
            (PartialReturnConstructor::Abort, vec![]),
        ])
    }

    fn selector_sort(&self, sel: &Self::Selector) -> SmtExpr {
        let Self {
            game_name,
            game_params,
            pkg_name,
            pkg_params,
            oracle_name,
        } = self;

        let game_state_pattern = super::game_state::GameStatePattern {
            game_name,
            params: game_params,
        };
        let intermediate_state_pattern = super::IntermediateStatePattern {
            pkg_name,
            oracle_name,
            params: pkg_params,
        };

        match sel {
            PartialReturnSelector::GameState => game_state_pattern.sort(vec![]),
            PartialReturnSelector::IntermediateState => intermediate_state_pattern.sort(vec![]),
        }
        .into()
    }
}
