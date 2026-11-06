// SPDX-License-Identifier: MIT OR Apache-2.0

mod emit;

use crate::{
    package::{OracleDef, OracleSig},
    types::Type,
    writers::smt::{
        contexts::{GameInstanceContext, PackageInstanceContext},
        patterns::{oracle_args, OraclePattern, ReturnPattern, ReturnValue},
    },
};

#[derive(Copy, Clone, Debug)]
pub struct OracleContext<'a> {
    game_inst_context: GameInstanceContext<'a>,
    pkg_inst_offs: usize,
    oracle_offs: usize,
    renamed: Option<&'a str>,
}

impl<'a> OracleContext<'a> {
    pub(crate) fn new(
        game_inst_context: GameInstanceContext<'a>,
        pkg_inst_offs: usize,
        oracle_offs: usize,
    ) -> Self {
        Self {
            game_inst_context,
            pkg_inst_offs,
            oracle_offs,
            renamed: None,
        }
    }

    pub(crate) fn set_renamed(&mut self, renamed: Option<&'a str>) {
        self.renamed = renamed;
    }
}

// Patterns
impl<'a> OracleContext<'a> {
    pub(crate) fn oracle_pattern(&self) -> OraclePattern<'a> {
        let gctx: GameInstanceContext<'a> = self.game_inst_ctx();
        let pctx: PackageInstanceContext<'a> = self.pkg_inst_ctx();

        let game_name: &'a _ = gctx.game_name();
        let game_inst_name: &'a _ = gctx.game_inst_name();
        let pkg_name: &'a _ = pctx.pkg_name();
        let pkg_inst_name: &'a _ = pctx.pkg_inst_name();
        let oracle_name: &'a _ = self.oracle_name();
        let oracle_args: &'a _ = self.oracle_args();
        let game_params: &'a _ = gctx.game_params();
        let pkg_params: &'a _ = pctx.pkg_params();

        OraclePattern {
            game_name,
            game_inst_name,
            pkg_name,
            pkg_inst_name,
            oracle_name,
            oracle_args,
            game_params,
            pkg_params,
        }
    }

    pub(crate) fn return_pattern(&self) -> ReturnPattern<'a> {
        let gctx: GameInstanceContext<'a> = self.game_inst_ctx();
        let pctx: PackageInstanceContext<'a> = self.pkg_inst_ctx();

        let game_name: &'a _ = gctx.game_name();
        let pkg_name: &'a _ = pctx.pkg_name();
        let oracle_name: &'a _ = self.oracle_name();
        let game_params: &'a _ = gctx.game_params();
        let pkg_params: &'a _ = pctx.pkg_params();

        ReturnPattern {
            game_name,
            pkg_name,
            oracle_name,
            game_params,
            pkg_params,
        }
    }

    pub(crate) fn return_value_pattern(&self) -> ReturnValue<'a> {
        ReturnValue {
            inner_type: self.return_type(),
        }
    }

    pub(crate) fn oracle_arg_game_consts_pattern(&self) -> oracle_args::GameConstsPattern<'a> {
        oracle_args::GameConstsPattern {
            game_name: self.game_inst_ctx().game().name(),
        }
    }

    pub(crate) fn oracle_arg_game_state_pattern(&self) -> oracle_args::GameStatePattern<'a> {
        oracle_args::GameStatePattern {
            game_name: self.game_inst_ctx().game().name(),
            game_params: &self.game_inst_ctx().game_inst().consts,
        }
    }

    // TODO: (2024-10-09): oracle arg patterns for value args
}

// Getters
impl<'a> OracleContext<'a> {
    fn return_type(&self) -> &'a Type {
        &self.oracle_def().sig.ty
    }

    pub(crate) fn oracle_def(&self) -> &'a OracleDef {
        &self.game_inst_context.game_inst().game().pkgs[self.pkg_inst_offs]
            .pkg
            .oracles[self.oracle_offs]
    }

    pub(crate) fn oracle_sig(&self) -> &'a OracleSig {
        &self.game_inst_context.game_inst().game().pkgs[self.pkg_inst_offs]
            .pkg
            .oracles[self.oracle_offs]
            .sig
    }
}

// Contexts
impl<'a> OracleContext<'a> {
    pub(crate) fn game_inst_ctx(&self) -> GameInstanceContext<'a> {
        self.game_inst_context
    }

    pub(crate) fn pkg_inst_ctx(&self) -> PackageInstanceContext<'a> {
        PackageInstanceContext::new(self.game_inst_context, self.pkg_inst_offs)
    }

    pub(crate) fn oracle_name(&self) -> &'a str {
        let oracle_def: &'a _ = self.oracle_def();
        &oracle_def.sig.name
    }

    pub(crate) fn oracle_args(&self) -> &'a [(String, Type)] {
        &self.oracle_def().sig.args
    }

    pub(crate) fn oracle_return_type(&self) -> &'a Type {
        &self.oracle_def().sig.ty
    }
}
