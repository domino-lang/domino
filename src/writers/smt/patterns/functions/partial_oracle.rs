// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::{
    expressions::Expression,
    identifier::{game_ident::GameConstIdentifier, pkg_ident::PackageConstIdentifier},
    split::SplitPath,
    writers::smt::{
        patterns::{
            instance_names::{encode_params, only_non_function_expression},
            DatastructurePattern as _, FunctionPattern, PartialReturnPattern,
        },
        sorts::Sort,
    },
};

pub struct PartialOraclePattern<'a> {
    pub game_name: &'a str,
    pub pkg_name: &'a str,
    pub game_params: &'a [(GameConstIdentifier, Expression)],
    pub pkg_params: &'a [(PackageConstIdentifier, Expression)],
    pub oracle_name: &'a str,
    pub split_path: &'a SplitPath,
}

impl<'a> FunctionPattern for PartialOraclePattern<'a> {
    fn function_name(&self) -> String {
        let PartialOraclePattern {
            game_name,
            pkg_name,
            oracle_name,
            split_path,
            game_params,
            pkg_params,
        } = self;

        let game_params = encode_params(only_non_function_expression(*game_params));
        let pkg_params = encode_params(only_non_function_expression(*pkg_params));

        let path = split_path.smt_name();
        format!("<oracle-{game_name}-{game_params}-{pkg_name}-{pkg_params}-{oracle_name}-{path}>")
    }

    fn function_args(&self) -> Vec<(String, Sort)> {
        todo!()
    }

    fn function_args_count(&self) -> usize {
        todo!()
    }

    fn function_return_sort(&self) -> Sort {
        let Self {
            game_name,
            game_params,
            pkg_name,
            pkg_params,
            oracle_name,
            ..
        } = self;
        let partial_return_pattern = PartialReturnPattern {
            game_name,
            game_params,
            pkg_name,
            pkg_params,
            oracle_name,
        };

        partial_return_pattern.sort(vec![])
    }
}
