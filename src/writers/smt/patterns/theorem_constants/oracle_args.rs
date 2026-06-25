// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::{
    types::Type,
    writers::smt::{patterns::theorem_constants::ConstantPattern, sorts::Sort},
};

#[derive(Clone, Debug)]
pub struct OracleArgs<'a> {
    pub oracle_name: &'a str,
    pub game_name: &'a str,
    pub arg_name: &'a str,
    pub arg_type: &'a Type,
}

impl ConstantPattern for OracleArgs<'_> {
    fn name(&self) -> String {
        let Self {
            oracle_name,
            game_name,
            arg_name,
            ..
        } = self;

        format!("<arg-{game_name}-{oracle_name}-{arg_name}>")
    }

    fn sort(&self) -> Sort {
        self.arg_type.clone().into()
    }
}
