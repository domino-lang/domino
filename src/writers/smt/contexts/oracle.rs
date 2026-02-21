// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::package::{OracleDef, OracleSig};
use crate::transforms::samplify::SampleInfo;
use crate::types::Type;
use crate::writers::smt::names::FunctionNameBuilder;
use crate::writers::smt::patterns::oracle_args::OracleArgPattern;
use crate::writers::smt::patterns::theorem_constants::ReturnValueConst;
use crate::writers::smt::patterns::FunctionPattern;
use crate::writers::smt::patterns::{
    oracle_args, DatastructurePattern, OraclePattern, ReturnConstructor, ReturnPattern,
    ReturnSelector, ReturnValue, ReturnValueConstructor,
};

use super::super::exprs::SmtExpr;

use super::{GameInstanceContext, GenericOracleContext, PackageInstanceContext};

#[derive(Copy, Clone, Debug)]
pub struct OracleContext<'a> {
    game_inst_context: GameInstanceContext<'a>,
    pkg_inst_offs: usize,
    oracle_offs: usize,
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
        }
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

    // pub(crate) fn dispatch_oracle_pattern(&self) -> DispatchOraclePattern<'a> {
    //     let gctx: GameInstanceContext<'a> = self.game_inst_ctx();
    //     let pctx: PackageInstanceContext<'a> = self.pkg_inst_ctx();
    //
    //     let game_name: &'a _ = gctx.game_name();
    //     let pkg_name: &'a _ = pctx.pkg_name();
    //     let oracle_sig: &'a _ = self.oracle_sig();
    //     let game_params: &'a _ = gctx.game_params();
    //     let pkg_params: &'a _ = pctx.pkg_params();
    //
    //     DispatchOraclePattern {
    //         game_name,
    //         game_params,
    //         pkg_name,
    //         pkg_params,
    //         oracle_sig,
    //     }
    // }

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

    pub(crate) fn return_value_const_pattern(&self, oracle_name: &'a str) -> ReturnValueConst<'a> {
        let game_inst_name = self.game_inst_ctx().game_inst_name();
        let pkg_inst_name = self.pkg_inst_ctx().pkg_inst_name();
        let ty = self.return_type();

        ReturnValueConst {
            game_inst_name,
            pkg_inst_name,
            oracle_name,
            ty,
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
// SMT Code Generation
impl OracleContext<'_> {
    pub(crate) fn smt_arg_name(&self, arg_name: &str) -> SmtExpr {
        let game = self.game_inst_context.game_inst().game();
        let pkg_inst = &game.pkgs[self.pkg_inst_offs];
        let odef = &pkg_inst.pkg.oracles[self.oracle_offs];

        FunctionNameBuilder::new()
            .push("arg")
            .push(&odef.sig.name)
            .push(arg_name)
            .build()
            .into()
    }

    pub(crate) fn smt_construct_return<S, V>(&self, state: S, value: V) -> SmtExpr
    where
        S: Into<SmtExpr>,
        V: Into<SmtExpr>,
    {
        let game_inst = self.game_inst_context.game_inst();
        let pkg_inst = &game_inst.game().pkgs[self.pkg_inst_offs];
        let odef = &pkg_inst.pkg.oracles[self.oracle_offs];
        let osig = &odef.sig;
        let return_type = &osig.ty;

        let return_value_pattern = ReturnValue {
            inner_type: return_type,
        };
        let return_value_spec = return_value_pattern.datastructure_spec(&());

        // we do this here so we can clone the smt expression in the closure below
        // and don't have to require a `Clone` constraint from `value_smt`.
        let value_smt: SmtExpr = value.into();

        let return_value = return_value_pattern
            .call_constructor(
                &return_value_spec,
                vec![return_type.clone().into()],
                &ReturnValueConstructor::Return,
                |_| Some(value_smt.clone()),
            )
            .unwrap();

        let return_pattern = self.return_pattern();

        let return_spec = return_pattern.datastructure_spec(return_type);

        let state_smt: SmtExpr = state.into();

        return_pattern
            .call_constructor(
                &return_spec,
                vec![return_type.clone().into()],
                &ReturnConstructor,
                |sel: &ReturnSelector| {
                    Some(match sel {
                        ReturnSelector::GameState => state_smt.clone(),
                        ReturnSelector::ReturnValueOrAbort {
                            return_type: spec_return_type,
                        } => {
                            assert_eq!(*spec_return_type, return_type);
                            return_value.clone()
                        }
                    })
                },
            )
            .unwrap()
    }

    pub(crate) fn smt_access_return_state<R>(&self, ret: R) -> SmtExpr
    where
        R: Into<SmtExpr>,
    {
        let game_inst = self.game_inst_context.game_inst();
        let pkg_inst = &game_inst.game().pkgs[self.pkg_inst_offs];
        let osig = &pkg_inst.pkg.oracles[self.oracle_offs].sig;
        let return_type = &osig.ty;

        let pattern = self.return_pattern();
        let spec = pattern.datastructure_spec(return_type);

        pattern
            .access(&spec, &ReturnSelector::GameState, ret)
            .unwrap()
    }

    pub(crate) fn smt_access_return_is_abort<R: Into<SmtExpr>>(&self, ret: R) -> SmtExpr {
        let return_type = &self.return_type();
        let return_pattern = self.return_pattern();
        let return_spec = return_pattern.datastructure_spec(return_type);
        let return_value = return_pattern
            .access(
                &return_spec,
                &ReturnSelector::ReturnValueOrAbort { return_type },
                ret,
            )
            .unwrap();

        ("=", return_value, self.smt_construct_abort_return_value()).into()
    }

    pub(crate) fn smt_construct_abort_return_value(&self) -> SmtExpr {
        let return_type = self.return_type();
        let pattern = self.return_value_pattern();
        let spec = pattern.datastructure_spec(&());
        pattern
            .call_constructor(
                &spec,
                vec![return_type.clone().into()],
                &ReturnValueConstructor::Abort,
                |_| None,
            )
            .unwrap()
    }

    pub(crate) fn smt_access_return_value<R: Into<SmtExpr>>(&self, ret: R) -> SmtExpr {
        let game_inst = self.game_inst_context.game_inst();
        let pkg_inst = &game_inst.game().pkgs[self.pkg_inst_offs];
        let osig = &pkg_inst.pkg.oracles[self.oracle_offs].sig;
        let return_type = &osig.ty;

        let pattern = self.return_pattern();
        let spec = pattern.datastructure_spec(return_type);

        pattern
            .access(
                &spec,
                &ReturnSelector::ReturnValueOrAbort { return_type },
                ret,
            )
            .unwrap()
    }

    /// writes the changes we made to local package state variables back into the package and game state
    pub(crate) fn smt_write_back_state(&self, sample_info: &SampleInfo) -> SmtExpr {
        let game_inst_ctx = self.game_inst_ctx();
        let pkg_inst_ctx = self.pkg_inst_ctx();
        let pkg_inst = self.pkg_inst_ctx().pkg_inst();
        let game_state = oracle_args::GameStatePattern {
            game_name: game_inst_ctx.game_name(),
            game_params: game_inst_ctx.game_params(),
        };

        game_inst_ctx
            .smt_update_gamestate_pkgstate(
                game_state.local_arg_name(),
                sample_info,
                &pkg_inst.name,
                pkg_inst_ctx.smt_update_pkgstate_from_locals().unwrap(),
            )
            .unwrap()
    }
}

// Contexts
impl<'a> GenericOracleContext<'a> for OracleContext<'a> {
    fn game_inst_ctx(&self) -> GameInstanceContext<'a> {
        self.game_inst_context
    }

    fn pkg_inst_ctx(&self) -> PackageInstanceContext<'a> {
        PackageInstanceContext::new(self.game_inst_context, self.pkg_inst_offs)
    }

    fn oracle_name(&self) -> &'a str {
        let oracle_def: &'a _ = self.oracle_def();
        &oracle_def.sig.name
    }

    fn oracle_args(&self) -> &'a [(String, Type)] {
        &self.oracle_def().sig.args
    }

    fn oracle_return_type(&self) -> &'a Type {
        &self.oracle_def().sig.ty
    }

    fn smt_write_back_state(&self, sample_info: &SampleInfo) -> SmtExpr {
        self.smt_write_back_state(sample_info)
    }

    fn smt_game_state(&self) -> SmtExpr {
        "<game-state>".into()
    }

    fn smt_construct_abort<S: Into<SmtExpr>>(&self, game_state: S) -> SmtExpr {
        let game_inst = self.game_inst_context.game_inst();
        let pkg_inst = &game_inst.game().pkgs[self.pkg_inst_offs];
        let osig = &pkg_inst.pkg.oracles[self.oracle_offs].sig;

        let return_type = self.return_type();

        let return_value_pattern = ReturnValue {
            inner_type: &osig.ty,
        };
        let return_value_spec = return_value_pattern.datastructure_spec(&());

        let abort = return_value_pattern
            .call_constructor(
                &return_value_spec,
                vec![return_type.clone().into()],
                &ReturnValueConstructor::Abort,
                |_| unreachable!(),
            )
            .unwrap();

        let return_pattern = self.return_pattern();

        let return_spec = return_pattern.datastructure_spec(return_type);

        let game_state = game_state.into();
        return_pattern
            .call_constructor(
                &return_spec,
                vec![return_type.clone().into()],
                &ReturnConstructor,
                |sel: &ReturnSelector| {
                    Some(match sel {
                        ReturnSelector::GameState => game_state.clone(),
                        ReturnSelector::ReturnValueOrAbort { .. } => abort.clone(),
                    })
                },
            )
            .unwrap()
    }

    // returns none if the wrong number of arguments were provided
    fn smt_call_oracle_fn<
        GameState: Into<SmtExpr>,
        GameConsts: Into<SmtExpr>,
        Args: IntoIterator<Item = SmtExpr>,
    >(
        &self,
        game_state: GameState,
        game_consts: GameConsts,
        args: Args,
    ) -> Option<SmtExpr> {
        let pattern = self.oracle_pattern();

        let base_args = [game_state.into(), game_consts.into()].into_iter();
        let call_args: Vec<_> = base_args.chain(args).collect();

        pattern.call(&call_args)
    }
}
