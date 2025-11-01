// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::{
    expressions::Expression,
    identifier::{game_ident::GameConstIdentifier, pkg_ident::PackageConstIdentifier},
    package::OracleSig,
    writers::smt::{
        patterns::{
            self,
            instance_names::{encode_params, only_non_function_expression},
            oracle_args::OracleArgPattern as _,
            DatastructurePattern as _, FunctionPattern, IntermediateStatePattern,
            PartialReturnPattern,
        },
        sorts::Sort,
    },
};

use super::oracle::ORACLE_ARG_INTERMEDIATE_STATE;

pub struct DispatchOraclePattern<'a> {
    pub game_name: &'a str,
    pub game_params: &'a [(GameConstIdentifier, Expression)],
    pub pkg_name: &'a str,
    pub pkg_params: &'a [(PackageConstIdentifier, Expression)],
    pub oracle_sig: &'a OracleSig,
}

impl<'a> FunctionPattern for DispatchOraclePattern<'a> {
    fn function_name(&self) -> String {
        let Self {
            game_name,
            pkg_name,
            oracle_sig,
            ..
        } = self;

        let game_params = encode_params(only_non_function_expression(self.game_params));
        let pkg_params = encode_params(only_non_function_expression(self.pkg_params));

        let oracle_name = &oracle_sig.name;
        format!("oracle-{game_name}-{game_params}-{pkg_name}-{pkg_params}-{oracle_name}")
    }

    fn function_args(&self) -> Vec<(String, Sort)> {
        let DispatchOraclePattern {
            oracle_sig:
                OracleSig {
                    name: oracle_name,
                    args: oracle_args,
                    ..
                },
            game_name,
            game_params,
            pkg_name,
            pkg_params,
            ..
        } = self;

        let intermediate_state_pattern = IntermediateStatePattern {
            pkg_name,
            params: pkg_params,
            oracle_name,
        };

        let game_state = patterns::oracle_args::GameStatePattern {
            game_name,
            game_params,
        };

        let game_consts = patterns::oracle_args::GameConstsPattern { game_name };

        let game_state_pair = (game_state.local_arg_name(), game_state.sort().into());
        let game_const_pair = (game_consts.local_arg_name(), game_consts.sort().into());

        vec![
            game_state_pair,
            game_const_pair,
            (
                ORACLE_ARG_INTERMEDIATE_STATE.to_string(),
                intermediate_state_pattern.sort(vec![]).into(),
            ),
        ]
        .into_iter()
        .chain(
            oracle_args
                .iter()
                .cloned()
                .map(|(name, ty)| (name, ty.into())),
        )
        .collect()
    }

    fn function_return_sort(&self) -> Sort {
        let Self {
            game_name,
            game_params,
            pkg_name,
            pkg_params,
            oracle_sig,
            ..
        } = self;

        let partial_return_pattern = PartialReturnPattern {
            game_name,
            game_params,
            pkg_name,
            pkg_params,
            oracle_name: &oracle_sig.name,
        };

        partial_return_pattern.sort(vec![])
    }

    fn function_args_count(&self) -> usize {
        todo!()
    }
}
