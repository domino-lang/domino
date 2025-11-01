// SPDX-License-Identifier: MIT OR Apache-2.0

use super::{DatastructurePattern, DatastructureSpec};
use crate::expressions::Expression;
use crate::identifier::game_ident::GameConstIdentifier;
use crate::identifier::pkg_ident::PackageConstIdentifier;
use crate::types::Type;
use crate::writers::smt::exprs::SmtExpr;
use crate::writers::smt::names::{FunctionNameBuilder, SortNameBuilder};
use crate::writers::smt::patterns::instance_names::{encode_params, only_ints};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ReturnPattern<'a> {
    pub game_name: &'a str,
    pub game_params: &'a [(GameConstIdentifier, Expression)],
    pub pkg_name: &'a str,
    pub pkg_params: &'a [(PackageConstIdentifier, Expression)],
    pub oracle_name: &'a str,
}

#[derive(PartialEq, Eq)]
pub struct ReturnConstructor;

#[derive(PartialEq, Eq, Debug)]
pub enum ReturnSelector<'a> {
    GameState,
    ReturnValueOrAbort { return_type: &'a Type },
}

impl<'a> DatastructurePattern<'a> for ReturnPattern<'a> {
    type Constructor = ReturnConstructor;
    type Selector = ReturnSelector<'a>;
    type DeclareInfo = Type;

    const CAMEL_CASE: &'static str = "OracleReturn";
    const KEBAB_CASE: &'static str = "oracle-return";

    fn sort_name(&self) -> String {
        let game_encoded_params = encode_params(only_ints(self.game_params));
        let pkg_encoded_params = encode_params(only_ints(self.pkg_params));

        SortNameBuilder::new()
            .push(Self::CAMEL_CASE)
            .push(self.game_name)
            .maybe_extend(&game_encoded_params)
            .push(self.pkg_name)
            .maybe_extend(&pkg_encoded_params)
            .push(self.oracle_name)
            .build()
    }

    fn constructor_name(&self, _cons: &Self::Constructor) -> String {
        let game_encoded_params = encode_params(only_ints(self.game_params));
        let pkg_encoded_params = encode_params(only_ints(self.pkg_params));

        FunctionNameBuilder::new()
            .push("mk")
            .push(Self::KEBAB_CASE)
            .push(self.game_name)
            .maybe_extend(&game_encoded_params)
            .push(self.pkg_name)
            .maybe_extend(&pkg_encoded_params)
            .push(self.oracle_name)
            .build()
    }

    fn selector_name(&self, sel: &Self::Selector) -> String {
        let game_encoded_params = encode_params(only_ints(self.game_params));
        let pkg_encoded_params = encode_params(only_ints(self.pkg_params));

        let field_name = match sel {
            ReturnSelector::GameState => "game-state",
            ReturnSelector::ReturnValueOrAbort { .. } => "return-value-or-abort",
        };

        FunctionNameBuilder::new()
            .push(Self::KEBAB_CASE)
            .push(self.game_name)
            .maybe_extend(&game_encoded_params)
            .push(self.pkg_name)
            .maybe_extend(&pkg_encoded_params)
            .push(self.oracle_name)
            .push(field_name)
            .build()
    }

    fn matchfield_name(&self, sel: &Self::Selector) -> String {
        let field_name = match sel {
            ReturnSelector::GameState => "game-state",
            ReturnSelector::ReturnValueOrAbort { .. } => "return-value-or-abort",
        };

        FunctionNameBuilder::new()
            .push("match")
            .push(field_name)
            .build()
    }

    fn datastructure_spec(&self, return_type: &'a Type) -> DatastructureSpec<'a, Self> {
        DatastructureSpec(vec![(
            ReturnConstructor,
            vec![
                ReturnSelector::GameState,
                ReturnSelector::ReturnValueOrAbort { return_type },
            ],
        )])
    }

    fn selector_sort(&self, sel: &Self::Selector) -> SmtExpr {
        let Self {
            game_name,
            game_params,
            ..
        } = self;

        let game_state_pattern = super::game_state::GameStatePattern {
            game_name,
            params: game_params,
        };

        match sel {
            ReturnSelector::GameState => game_state_pattern.sort(vec![]).into(),
            ReturnSelector::ReturnValueOrAbort { return_type } => {
                ("ReturnValue", *return_type).into()
            }
        }
    }
}

impl ReturnPattern<'_> {
    pub fn global_const_name(&self) -> String {
        let game_encoded_params = encode_params(only_ints(self.game_params));
        let pkg_encoded_params = encode_params(only_ints(self.pkg_params));

        FunctionNameBuilder::new()
            .push("!return")
            .push(self.game_name)
            .maybe_extend(&game_encoded_params)
            .push(self.pkg_name)
            .maybe_extend(&pkg_encoded_params)
            .push(self.oracle_name)
            .build()
    }
}
