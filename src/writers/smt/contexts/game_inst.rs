// SPDX-License-Identifier: MIT OR Apache-2.0

mod emit;

use crate::{
    expressions::Expression,
    identifier::game_ident::GameConstIdentifier,
    package::Composition,
    theorem::GameInstance,
    transforms::samplify::SampleInfo,
    writers::smt::patterns::{
        self, game_consts::GameConstsPattern, GameStateDeclareInfo, GameStatePattern,
    },
};

use super::{OracleContext, PackageInstanceContext};

#[derive(Clone, Debug, Copy)]
pub struct GameInstanceContext<'a> {
    game_inst: &'a GameInstance,
    sample_info: &'a SampleInfo,
}

impl<'a> GameInstanceContext<'a> {
    pub(crate) fn new(game_inst: &'a GameInstance, sample_info: &'a SampleInfo) -> Self {
        GameInstanceContext {
            game_inst,
            sample_info,
        }
    }

    pub(crate) fn pkg_inst_contexts(self) -> impl Iterator<Item = PackageInstanceContext<'a>> {
        self.game()
            .ordered_pkgs_idx()
            .into_iter()
            .map(move |i| self.pkg_inst_ctx_by_offs(i).unwrap())
    }

    pub(crate) fn game_inst(self) -> &'a GameInstance {
        self.game_inst
    }

    pub(crate) fn sample_info(self) -> &'a SampleInfo {
        self.sample_info
    }

    pub(crate) fn game(self) -> &'a Composition {
        self.game_inst().game()
    }

    pub(crate) fn game_name(self) -> &'a str {
        self.game().name()
    }

    pub(crate) fn game_inst_name(self) -> &'a str {
        self.game_inst().name()
    }

    pub(crate) fn game_params(self) -> &'a [(GameConstIdentifier, Expression)] {
        self.game_inst().consts.as_slice()
    }
}

// Patterns
impl<'a> GameInstanceContext<'a> {
    pub(crate) fn oracle_arg_game_state_pattern(
        &self,
    ) -> patterns::oracle_args::GameStatePattern<'a> {
        patterns::oracle_args::GameStatePattern {
            game_name: self.game_name(),
            game_params: self.game_params(),
        }
    }

    pub(crate) fn datastructure_game_state_pattern(self) -> GameStatePattern<'a> {
        let game_name = self.game_name();
        let params = &self.game_inst.consts;

        GameStatePattern { game_name, params }
    }

    pub(crate) fn datastructure_game_consts_pattern(self) -> GameConstsPattern<'a> {
        let game_name = self.game_name();

        GameConstsPattern { game_name }
    }

    pub(crate) fn game_state_declare_info(&self) -> GameStateDeclareInfo<'a> {
        let game_inst = self.game_inst;
        let sample_info = self.sample_info;
        GameStateDeclareInfo {
            game_inst,
            sample_info,
        }
    }
}

// Contexts
impl<'a> GameInstanceContext<'a> {
    pub(crate) fn pkg_inst_ctx_by_name(
        &self,
        inst_name: &str,
    ) -> Option<PackageInstanceContext<'a>> {
        self.game_inst
            .game()
            .pkgs // we only want a single package, no sorting needed
            .iter()
            .position(|pkg| pkg.name == inst_name)
            .map(|inst_offs| PackageInstanceContext::new(*self, inst_offs))
    }

    pub(crate) fn pkg_inst_ctx_by_offs(
        self,
        inst_offs: usize,
    ) -> Option<PackageInstanceContext<'a>> {
        if inst_offs >= self.game_inst.game().pkgs.len() {
            return None;
        }

        Some(PackageInstanceContext::new(self, inst_offs))
    }

    pub(crate) fn exported_oracle_ctx_by_name(
        &self,
        oracle_name: &str,
    ) -> Option<OracleContext<'a>> {
        let export = self
            .game_inst
            .game()
            .exports
            .iter()
            .find(|export| export.name() == oracle_name)?;

        let inst_ctx = PackageInstanceContext::new(*self, export.to());

        inst_ctx.oracle_ctx_by_name(&export.sig().name)
    }
}
