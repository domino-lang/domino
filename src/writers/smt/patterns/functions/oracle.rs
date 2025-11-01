// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::{
    expressions::Expression,
    identifier::{game_ident::GameConstIdentifier, pkg_ident::PackageConstIdentifier},
    types::Type,
    writers::smt::{
        names::FunctionNameBuilder,
        patterns::{
            self,
            instance_names::{encode_params, only_ints_and_funs},
            oracle_args::OracleArgPattern as _,
            DatastructurePattern as _, FunctionPattern, ReturnPattern,
        },
        sorts::Sort,
    },
};

pub const ORACLE_ARG_GAME_STATE: &str = "<game-state>";
pub const ORACLE_ARG_INTERMEDIATE_STATE: &str = "__intermediate_state";

pub struct OraclePattern<'a> {
    pub game_name: &'a str,
    pub game_inst_name: &'a str,
    pub pkg_name: &'a str,
    pub pkg_inst_name: &'a str,
    pub oracle_name: &'a str,
    pub oracle_args: &'a [(String, Type)],
    pub game_params: &'a [(GameConstIdentifier, Expression)],
    pub pkg_params: &'a [(PackageConstIdentifier, Expression)],
}

impl FunctionPattern for OraclePattern<'_> {
    fn function_name(&self) -> String {
        let pkg_encoded_params = encode_params(only_ints_and_funs(self.pkg_params));

        FunctionNameBuilder::new()
            .push("oracle")
            .push(self.game_name)
            .push(self.game_inst_name)
            .push(self.pkg_name)
            .push(self.pkg_inst_name)
            .maybe_extend(&pkg_encoded_params)
            .push(self.oracle_name)
            .build()
    }

    fn function_args(&self) -> Vec<(String, Sort)> {
        let Self {
            game_name,
            game_params,
            oracle_args,
            ..
        } = self;

        let game_state = patterns::oracle_args::GameStatePattern {
            game_name,
            game_params,
        };

        let game_consts = patterns::oracle_args::GameConstsPattern { game_name };

        let game_state_pair = (game_state.local_arg_name(), game_state.sort());
        let game_const_pair = (game_consts.local_arg_name(), game_consts.sort());

        vec![game_state_pair, game_const_pair]
            .into_iter()
            .chain(
                oracle_args
                    .iter()
                    .cloned()
                    .map(|(name, ty)| (name, ty.into())),
            )
            .collect()
    }

    fn function_args_count(&self) -> usize {
        // game state, game consts, args
        2 + self.oracle_args.len()
    }

    fn function_return_sort(&self) -> Sort {
        let Self {
            game_name,
            pkg_name,
            oracle_name,
            game_params,
            pkg_params,
            ..
        } = self;

        ReturnPattern {
            game_name,
            pkg_name,
            oracle_name,
            game_params,
            pkg_params,
        }
        .sort(vec![])
    }
}
