// SPDX-License-Identifier: MIT OR Apache-2.0

use std::collections::HashSet;

use itertools::Itertools;

use crate::{
    theorem::GameInstance,
    transforms::samplify::SampleInfo,
    writers::smt::{
        contexts::GameInstanceContext,
        declare::declare_const,
        exprs::{SmtAssert, SmtEq2, SmtExpr},
        patterns::{
            self,
            const_mapping::{define_pkg_const_mapping_fun, GameConstMappingFunction},
            declare_datatype,
            oracle_args::{
                GameStateOracleArgPattern, GameStateOracleArgVariant, OracleArgPattern,
                UnitOracleArgPattern,
            },
            theorem_constants::ConstantPattern,
            DatastructurePattern, FunctionPattern, GameStateDeclareInfo, GameStateSelector,
            ReturnIsAbortConst,
        },
        sorts::Sort,
    },
};

impl<'a> GameInstanceContext<'a> {
    pub(crate) fn emit_constant_declarations(&self, theorem_name: &str) -> Vec<SmtExpr> {
        let mut out = Vec::new();

        let game_state = self.oracle_arg_game_state_pattern();
        out.push(game_state.declare_old(self.game_inst_name()));

        // the interface requires us to pass in a game instance name, but for the theorem constants
        // that gets ignored. We use a name here that would for sure cause trouble if it were
        // included.
        let hack_this_should_be_ignored = "this is being ignored anyway, but let's make sure it fails if it gets included )))))))))))))";

        let theorem_game_const_mapping = GameConstMappingFunction {
            theorem_name,
            game_name: self.game_name(),
            game_inst_name: self.game_inst_name(),
        };

        let game_consts = patterns::oracle_args::GameConstsPattern {
            game_name: self.game_name(),
        };

        let theorem_consts = patterns::oracle_args::TheoremConstsPattern { theorem_name };

        let theorem_game_const_mapping_call = theorem_game_const_mapping.call(&[theorem_consts
            .unit_global_const_name(hack_this_should_be_ignored)
            .into()]);

        out.push(
            game_consts
                .unit_define(
                    self.game_inst_name(),
                    theorem_game_const_mapping_call.unwrap(),
                )
                .into(),
        );

        for (decl_ret, constrain) in build_returns(self.game_inst(), self.sample_info) {
            out.push(decl_ret);
            out.push(constrain);
        }

        for (decl_ctr, assert_ctr, assert_zero_ctr) in
            build_rands(self.sample_info, self.game_inst())
        {
            out.push(decl_ctr);
            out.push(assert_ctr);
            // For offset-based randomness mapping, we treat the user-provided
            // counters as actual randomness counters instead of adding them to
            // the old counters (base counters). This requires asserting that
            // old counters are zero and makes the SMT code simpler.
            out.push(assert_zero_ctr);
        }

        out
    }

    pub(crate) fn emit_game_initial_state_values(&self) -> Vec<SmtExpr> {
        let game_inst_name = self.game_inst_name();
        let initial_state = self
            .oracle_arg_game_state_pattern()
            .global_const_name(game_inst_name, &GameStateOracleArgVariant::Initial);

        let mut out = Vec::new();
        out.push(
            self.oracle_arg_game_state_pattern()
                .declare_initial(game_inst_name),
        );

        for pctx in self.pkg_inst_contexts() {
            let pkg_state = self
                .smt_access_gamestate_pkgstate(&initial_state, pctx.pkg_inst_name())
                .unwrap();

            for (field_name, field_ty, _) in &pctx.pkg().state {
                let field = pctx
                    .smt_access_pkgstate(pkg_state.clone(), field_name)
                    .unwrap();

                out.push(
                    SmtAssert(SmtEq2 {
                        lhs: field,
                        rhs: SmtExpr::from(&field_ty.default_expression()),
                    })
                    .into(),
                );
            }
        }

        out
    }

    pub(in super::super) fn named_smt_game_const_definition(self) -> (String, SmtExpr) {
        let pattern = self.datastructure_game_consts_pattern();
        let spec = pattern.datastructure_spec(self.game());

        (pattern.sort_name(), declare_datatype(&pattern, &spec))
    }

    pub(in super::super) fn named_smt_oracle_function_definitions(
        self,
    ) -> impl Iterator<Item = (String, SmtExpr)> + 'a {
        self.pkg_inst_contexts()
            .flat_map(|pctx| pctx.oracle_contexts())
            .map(move |octx| {
                let pctx = octx.pkg_inst_ctx();
                let pattern = octx.oracle_pattern();

                (
                    pattern.function_name(),
                    pctx.smt_define_oracle_fn(octx.oracle_def()),
                )
            })
    }

    pub(in super::super) fn named_smt_game_state_definition(self) -> (String, SmtExpr) {
        let declare_info = GameStateDeclareInfo {
            game_inst: self.game_inst(),
            sample_info: self.sample_info,
        };

        let pattern = self.datastructure_game_state_pattern();
        let spec = pattern.datastructure_spec(&declare_info);
        let datatype = declare_datatype(&pattern, &spec);

        (pattern.sort_name(), datatype)
    }

    pub(in super::super) fn named_smt_package_return_definitions(
        self,
    ) -> impl Iterator<Item = (String, SmtExpr)> + 'a {
        self.pkg_inst_contexts()
            .flat_map(|pctx| pctx.oracle_contexts())
            .map(move |octx| {
                let pattern = octx.return_pattern();
                let spec = pattern.datastructure_spec(&octx.oracle_sig().ty);

                (pattern.sort_name(), declare_datatype(&pattern, &spec))
            })
    }

    pub(in super::super) fn named_smt_package_state_definitions(
        self,
    ) -> impl Iterator<Item = (String, SmtExpr)> + 'a {
        self.pkg_inst_contexts().map(|pctx| {
            let pattern = pctx.pkg_state_pattern();
            let spec = pattern.datastructure_spec(pctx.pkg());

            (pattern.sort_name(), declare_datatype(&pattern, &spec))
        })
    }

    pub(in super::super) fn named_smt_package_const_definitions(
        self,
    ) -> impl Iterator<Item = (String, SmtExpr)> + 'a {
        self.pkg_inst_contexts().map(|pctx| {
            let pattern = pctx.datastructure_pkg_consts_pattern();
            let spec = pattern.datastructure_spec(pctx.pkg());

            (pattern.sort_name(), declare_datatype(&pattern, &spec))
        })
    }

    pub(crate) fn smt_access_gamestate_pkgstate<S: Into<SmtExpr>>(
        &self,
        state: S,
        pkg_inst_name: &str,
    ) -> Option<SmtExpr> {
        let pkg_ctx = self.pkg_inst_ctx_by_name(pkg_inst_name)?;

        let declare_info = self.game_state_declare_info();
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
        state: S,
        sample_id: usize,
    ) -> Option<SmtExpr> {
        let declare_info = self.game_state_declare_info();
        let spec = self
            .datastructure_game_state_pattern()
            .datastructure_spec(&declare_info);
        let selector = GameStateSelector::Randomness {
            sample_pos: Box::new(self.sample_info.positions[sample_id].clone()),
        };

        self.datastructure_game_state_pattern()
            .access(&spec, &selector, state)
    }

    pub(crate) fn smt_update_gamestate_pkgstate<S, V>(
        &self,
        gamestate: S,
        target_name: &str,
        new_pkgstate: V,
    ) -> Option<SmtExpr>
    where
        S: Clone + Into<SmtExpr>,
        V: Clone + Into<SmtExpr>,
    {
        let pkg_ctx = self.pkg_inst_ctx_by_name(target_name).unwrap();

        let declare_info = self.game_state_declare_info();
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
        let declare_info = self.game_state_declare_info();
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
        let old_value = self.smt_access_gamestate_rand(state.clone(), target_sample_id)?;
        let new_value = ("+", 1, old_value);
        self.smt_update_gamestate_rand(state, sample_info, target_sample_id, new_value)
    }

    pub(crate) fn smt_composition_randomness(self) -> impl Iterator<Item = SmtExpr> {
        let game_inst = self.game_inst();

        // ensure the sorts are unique so they all just exist once
        let smt_sorts: HashSet<SmtExpr> = self
            .sample_info
            .tys
            .iter()
            .map(|ty| ty.clone().into())
            .collect();

        // turn them to function declarations
        smt_sorts
            .into_iter()
            .map(|smt_sort| {
                (
                    "declare-fun",
                    format!(
                        "__sample-rand-{game_inst_name}-{smt_sort}",
                        game_inst_name = game_inst.name
                    ),
                    (
                        SmtExpr::Atom("SampleId".into()),
                        SmtExpr::Atom("Int".into()),
                    ),
                    smt_sort,
                )
                    .into()
            })
            .sorted()
    }

    pub(crate) fn smt_game_pkg_const_mapping_definitions(
        self,
    ) -> impl Iterator<Item = SmtExpr> + 'a {
        self.game().pkgs.iter().flat_map(move |pkg_inst| {
            define_pkg_const_mapping_fun(self.game(), &pkg_inst.pkg, &pkg_inst.name)
                .map(SmtExpr::from)
        })
    }
}

fn build_returns(game_inst: &GameInstance, sample_info: &SampleInfo) -> Vec<(SmtExpr, SmtExpr)> {
    let gctx = GameInstanceContext::new(game_inst, sample_info);
    let game_name = &game_inst.game().name;
    let game_inst_name = &game_inst.name();
    let game_params = &game_inst.consts;

    // write declarations of right return constants and constrain them
    let mut out = vec![];
    for export in &game_inst.game().exports {
        let pkg_inst = &game_inst.game().pkgs[export.to()];
        let sig = export.sig();

        let pkg_inst_name = &pkg_inst.name;
        let pkg_params = &pkg_inst.params;
        let pkg_name = &pkg_inst.pkg.name;
        let oracle_name = &sig.name;
        let oracle_import_name = export.name();
        let return_type = &sig.ty;

        let mut octx = gctx
            .exported_oracle_ctx_by_name(export.name())
            .unwrap_or_else(|| {
                panic!(
                    "error looking up exported oracle with name {oracle_name} in game {game_name}"
                )
            });
        octx.set_renamed(export.alias());

        let return_const = patterns::ReturnConst {
            game_inst_name,
            game_name,
            game_params,
            pkg_name,
            pkg_params,
            oracle_name,
            oracle_import_name,
        };

        let return_value_const = patterns::ReturnValueConst {
            game_inst_name,
            pkg_inst_name,
            oracle_name: oracle_import_name,
            ty: &sig.ty,
        };

        let is_abort_const_pattern = ReturnIsAbortConst {
            game_inst_name,
            pkg_inst_name,
            oracle_name: oracle_import_name,
            ty: &sig.ty,
        };

        let state = octx.oracle_arg_game_state_pattern();
        let consts = octx.oracle_arg_game_consts_pattern();

        let old_state_const = state.old_global_const_name(game_inst_name);
        let new_state_const =
            state.new_global_const_name(game_inst_name, oracle_import_name.to_string());
        let consts_const = consts.unit_global_const_name(game_inst_name);

        let args = sig
            .args
            .iter()
            .map(|(arg_name, _)| octx.smt_arg_name(arg_name));

        let oracle_func_evaluation = octx
            .smt_call_oracle_fn(old_state_const, consts_const, args)
            .unwrap();

        let return_pattern = octx.return_pattern();
        let return_spec = return_pattern.datastructure_spec(return_type);

        let access_returnvalue = return_pattern
            .access(
                &return_spec,
                &patterns::ReturnSelector::ReturnValueOrAbort {
                    return_type: &sig.ty,
                },
                return_const.name(),
            )
            .unwrap();

        let access_new_state = return_pattern
            .access(
                &return_spec,
                &patterns::ReturnSelector::GameState,
                return_const.name(),
            )
            .unwrap();

        let constrain_return = SmtAssert(SmtEq2 {
            lhs: return_const.name(),
            rhs: oracle_func_evaluation,
        });

        let constrain_return_value = SmtAssert(SmtEq2 {
            lhs: return_value_const.name(),
            rhs: access_returnvalue,
        });

        let constrain_new_state = SmtAssert(SmtEq2 {
            lhs: new_state_const,
            rhs: access_new_state,
        });

        let constrain_is_abort = SmtAssert(SmtEq2 {
            lhs: is_abort_const_pattern.name(),
            rhs: is_abort_const_pattern.value(return_value_const.name()),
        });

        out.push((return_const.declare(), constrain_return.into()));
        out.push((return_value_const.declare(), constrain_return_value.into()));
        out.push((is_abort_const_pattern.declare(), constrain_is_abort.into()));
        out.push((
            state.declare_new(game_inst_name, oracle_import_name.to_string()),
            constrain_new_state.into(),
        ));
    }

    out
}

fn build_rands(
    sample_info: &SampleInfo,
    game_inst: &GameInstance,
) -> Vec<(SmtExpr, SmtExpr, SmtExpr)> {
    let gctx = GameInstanceContext::new(game_inst, sample_info);

    sample_info
        .positions
        .iter()
        .map(|sample_item| {
            let sample_id = sample_item.sample_id;
            let game_inst_name = game_inst.name();

            let state = gctx
                .oracle_arg_game_state_pattern()
                .old_global_const_name(game_inst_name);

            let randctr_name = format!("randctr-{game_inst_name}-{sample_id}");

            let decl_randctr = declare_const(randctr_name.clone(), Sort::Int);

            // pull randomness counter for given sample_id out of the gamestate
            let randctr = gctx.smt_access_gamestate_rand(state, sample_id).unwrap();

            let constrain_randctr: SmtExpr = SmtAssert(SmtEq2 {
                lhs: randctr_name.as_str(),
                rhs: randctr.clone(),
            })
            .into();

            let zero_constrain_randctr: SmtExpr = SmtAssert(SmtEq2 {
                lhs: randctr_name.as_str(),
                rhs: 0,
            })
            .into();

            (decl_randctr, constrain_randctr, zero_constrain_randctr)
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::fmt::Write;
    use std::string::FromUtf8Error;
    use thiserror::Error;

    use crate::{expressions::Expression, writers::smt::exprs::SmtLet};

    #[derive(Error, Debug)]
    enum TestError {
        #[error("Error parsing the utf8: {0}")]
        Utf8DecodeError(#[from] FromUtf8Error),
        #[error("Error Writing: {0}")]
        WriteError(#[from] std::io::Error),
    }

    type TestResult = std::result::Result<(), TestError>;

    #[test]
    fn test_smtlet() -> TestResult {
        let l = SmtLet {
            bindings: vec![("x".into(), (&Expression::integer(42)).into())],
            body: SmtExpr::Atom(String::from("x")),
        };

        let out: SmtExpr = l.into();
        let mut str = String::new();

        write!(&mut str, "{out}").unwrap();

        assert_eq!(str, "(let ((x 42))\n     x)\n");

        Ok(())
    }
}
