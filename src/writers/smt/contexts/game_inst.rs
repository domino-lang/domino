// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::{
    expressions::Expression,
    identifier::game_ident::GameConstIdentifier,
    package::{Composition, Export},
    theorem::GameInstance,
    transforms::samplify::{Position as SamplePosition, SampleInfo},
    types::Type,
    writers::smt::{
        exprs::SmtExpr,
        names,
        patterns::{
            self, game_consts::GameConstsPattern, DatastructurePattern, GameStateDeclareInfo,
            GameStatePattern, GameStateSelector,
        },
    },
};

use super::{OracleContext, PackageInstanceContext};

#[derive(Clone, Debug, Copy)]
pub struct GameInstanceContext<'a> {
    game_inst: &'a GameInstance,
}

impl<'a> GameInstanceContext<'a> {
    pub(crate) fn new(game_inst: &'a GameInstance) -> Self {
        GameInstanceContext { game_inst }
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

    fn game_state_declare_info(&self, sample_info: &'a SampleInfo) -> GameStateDeclareInfo<'a> {
        let game_inst = self.game_inst;
        GameStateDeclareInfo {
            game_inst,
            sample_info,
        }
    }
}

// SMT Code generation
impl GameInstanceContext<'_> {
    pub(crate) fn smt_access_gamestate_pkgstate<S: Into<SmtExpr>>(
        &self,
        state: S,
        pkg_inst_name: &str,
    ) -> Option<SmtExpr> {
        let pkg_ctx = self.pkg_inst_ctx_by_name(pkg_inst_name)?;

        // TODO/HACK: we don't have access to the sample info here, but we also don't really need
        //            it for accessing package state. we'll just pretend that the package doesn't
        //            sample. while the spec is "wrong" in that it won't contain the data based
        //            for sample instuctions, it should still behave correctly when queried for
        //            package state.
        let sample_info = SampleInfo {
            tys: vec![],
            count: 0,
            positions: vec![],
        };

        let declare_info = self.game_state_declare_info(&sample_info);
        let spec = self
            .datastructure_game_state_pattern()
            .datastructure_spec(&declare_info);
        let selector = GameStateSelector::PackageInstance {
            pkg_inst_name,
            sort: pkg_ctx.pkg_state_pattern().sort(vec![]),
        };

        self.datastructure_game_state_pattern()
            .access(&spec, &selector, state)
    }

    pub(crate) fn smt_access_gamestate_rand<S: Into<SmtExpr>>(
        &self,
        sample_info: &SampleInfo,
        state: S,
        sample_id: usize,
    ) -> Option<SmtExpr> {
        let declare_info = self.game_state_declare_info(sample_info);
        let spec = self
            .datastructure_game_state_pattern()
            .datastructure_spec(&declare_info);
        let selector = GameStateSelector::Randomness {
            sample_pos: Box::new(sample_info.positions[sample_id].clone()),
        };

        self.datastructure_game_state_pattern()
            .access(&spec, &selector, state)
    }

    pub(crate) fn smt_update_gamestate_pkgstate<S, V>(
        &self,
        gamestate: S,
        sample_info: &SampleInfo,
        target_name: &str,
        new_pkgstate: V,
    ) -> Option<SmtExpr>
    where
        S: Clone + Into<SmtExpr>,
        V: Clone + Into<SmtExpr>,
    {
        let pkg_ctx = self.pkg_inst_ctx_by_name(target_name).unwrap();

        let declare_info = self.game_state_declare_info(sample_info);
        let spec = self
            .datastructure_game_state_pattern()
            .datastructure_spec(&declare_info);
        let pkgstate_selector = GameStateSelector::PackageInstance {
            pkg_inst_name: target_name,
            sort: pkg_ctx.pkg_state_pattern().sort(vec![]),
        };

        self.datastructure_game_state_pattern().update(
            &spec,
            &pkgstate_selector,
            gamestate,
            new_pkgstate,
        )
    }

    pub(crate) fn smt_update_gamestate_rand<S, V>(
        &self,
        state: S,
        sample_info: &SampleInfo,
        sample_id: usize,
        new_value: V,
    ) -> Option<SmtExpr>
    where
        S: Clone + Into<SmtExpr>,
        V: Clone + Into<SmtExpr>,
    {
        let declare_info = self.game_state_declare_info(sample_info);
        let spec = self
            .datastructure_game_state_pattern()
            .datastructure_spec(&declare_info);
        let selector = GameStateSelector::Randomness {
            sample_pos: Box::new(sample_info.positions[sample_id].clone()),
        };

        self.datastructure_game_state_pattern()
            .update(&spec, &selector, state, new_value)
    }

    pub(crate) fn smt_increment_gamestate_rand<S>(
        &self,
        state: S,
        sample_info: &SampleInfo,
        target_sample_id: usize,
    ) -> Option<SmtExpr>
    where
        S: Clone + Into<SmtExpr>,
    {
        let old_value =
            self.smt_access_gamestate_rand(sample_info, state.clone(), target_sample_id)?;
        let new_value = ("+", 1, old_value);
        self.smt_update_gamestate_rand(state, sample_info, target_sample_id, new_value)
    }

    pub(crate) fn smt_eval_randfn<CTR: Into<SmtExpr>>(
        &self,
        sample_pos: &SamplePosition,
        ctr: CTR,
        ty: &Type,
    ) -> SmtExpr {
        let rand_fn_name = names::fn_sample_rand_name(&self.game_inst.name, ty);
        (rand_fn_name, sample_pos, ctr).into()
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
        let Export(inst_offs, _) = *self
            .game_inst
            .game()
            .exports
            .iter()
            .find(|Export(_, osig)| osig.name == oracle_name)?;

        let inst_ctx = PackageInstanceContext::new(*self, inst_offs);

        inst_ctx.oracle_ctx_by_name(oracle_name)
    }

    // pub(crate) fn exported_split_oracle_ctx_by_name(
    //     &self,
    //     oracle_name: &str,
    //     partials: &'a PartialsDatatype,
    // ) -> Option<SplitOracleContext<'a>> {
    //     let inst_ctx = self.pkg_inst_ctx_by_exported_split_oracle_name(oracle_name)?;
    //
    //     inst_ctx.split_oracle_ctx_by_name(oracle_name, partials)
    // }
    //
    // pub(crate) fn pkg_inst_ctx_by_exported_split_oracle_name(
    //     &self,
    //     oracle_name: &str,
    // ) -> Option<PackageInstanceContext<'a>> {
    //     self.game_inst
    //         .game()
    //         .split_exports
    //         .iter()
    //         .find(|SplitExport(_inst_offs, osig)| osig.name == oracle_name)
    //         .map(|SplitExport(inst_offs, _osig)| PackageInstanceContext {
    //             game_ctx: *self,
    //             inst_offs: *inst_offs,
    //         })
    // }
}
