// SPDX-License-Identifier: MIT OR Apache-2.0

mod emit;

use crate::{
    expressions::Expression,
    identifier::pkg_ident::PackageConstIdentifier,
    package::{Composition, Package, PackageInstance},
    theorem::GameInstance,
    writers::smt::{
        contexts::{GameInstanceContext, OracleContext},
        patterns::{self, PackageConstsPattern, PackageStatePattern, PackageStateSelector},
    },
};

#[derive(Clone, Debug, Copy)]
pub struct PackageInstanceContext<'a> {
    game_ctx: GameInstanceContext<'a>,
    inst_offs: usize,
}

impl<'a> PackageInstanceContext<'a> {
    pub(crate) fn new(game_inst_ctx: GameInstanceContext<'a>, pkg_inst_offs: usize) -> Self {
        Self {
            game_ctx: game_inst_ctx,
            inst_offs: pkg_inst_offs,
        }
    }
    pub(crate) fn game_inst_ctx(&self) -> GameInstanceContext<'a> {
        self.game_ctx
    }

    pub(crate) fn game_inst(&self) -> &'a GameInstance {
        self.game_inst_ctx().game_inst()
    }

    pub(crate) fn game(&self) -> &'a Composition {
        self.game_inst().game()
    }

    pub(crate) fn game_name(&self) -> &'a str {
        self.game_inst().game_name()
    }

    pub(crate) fn oracle_contexts(self) -> impl Iterator<Item = OracleContext<'a>> {
        (0..self.pkg().oracles.len()).map(move |i| self.oracle_ctx_by_oracle_offs(i).unwrap())
    }

    pub(crate) fn oracle_ctx_by_name(&self, oracle_name: &str) -> Option<OracleContext<'a>> {
        let inst_offs = self.inst_offs;
        let inst = &self.game().pkgs[inst_offs];
        let oracle_offs = inst
            .pkg
            .oracles
            .iter()
            .position(|odef| odef.sig.name == oracle_name)?;

        Some(OracleContext::new(
            self.game_inst_ctx(),
            inst_offs,
            oracle_offs,
        ))
    }

    pub(crate) fn oracle_ctx_by_oracle_offs(
        &self,
        oracle_offs: usize,
    ) -> Option<OracleContext<'a>> {
        let oracle_count = self.game().pkgs[self.inst_offs].pkg.oracles.len();
        if oracle_offs >= oracle_count {
            return None;
        }

        let game_ctx = self.game_inst_ctx();
        let inst_offs = self.inst_offs;

        Some(OracleContext::new(game_ctx, inst_offs, oracle_offs))
    }

    pub(crate) fn pkg_inst(&self) -> &'a PackageInstance {
        &self.game().pkgs[self.inst_offs]
    }

    pub(crate) fn pkg(&self) -> &'a Package {
        &self.pkg_inst().pkg
    }

    pub(crate) fn pkg_inst_name(&self) -> &'a str {
        &self.pkg_inst().name
    }

    pub(crate) fn pkg_name(&self) -> &'a str {
        &self.pkg().name
    }

    pub(crate) fn pkg_params(&self) -> &'a [(PackageConstIdentifier, Expression)] {
        &self.pkg_inst().params
    }

    pub(crate) fn datastructure_pkg_consts_pattern(&self) -> PackageConstsPattern<'a> {
        PackageConstsPattern {
            pkg_name: &self.pkg_inst().pkg.name,
        }
    }

    pub(crate) fn function_pkg_const_pattern(
        &self,
    ) -> patterns::functions::const_mapping::PackageConstMappingFunction<'a> {
        patterns::functions::const_mapping::PackageConstMappingFunction {
            game_name: self.game_name(),
            pkg_name: self.pkg_name(),
            pkg_inst_name: self.pkg_inst_name(),
        }
    }

    pub(crate) fn pkg_state_pattern(&self) -> PackageStatePattern<'a> {
        let pkg_name = &self.pkg_inst().pkg.name;

        let params = &self.pkg_inst().params;

        PackageStatePattern { pkg_name, params }
    }

    fn field_selector(&self, field_name: &'a str) -> Option<PackageStateSelector<'a>> {
        let pkg_inst = &self.game().pkgs[self.inst_offs];

        // return none if no field with that name exists
        let (_, ty, _) = pkg_inst
            .pkg
            .state
            .iter()
            .find(|(name, _ty, _file_pos)| name == field_name)?;

        Some(PackageStateSelector {
            name: field_name,
            ty,
        })
    }
}
