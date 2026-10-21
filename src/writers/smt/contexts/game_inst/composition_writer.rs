// SPDX-License-Identifier: MIT OR Apache-2.0

use std::collections::HashSet;

use itertools::Itertools;

use crate::expressions::Expression;
use crate::expressions::ExpressionKind;
use crate::identifier::Identifier;
use crate::package::{Edge, OracleDef, PackageInstance};
use crate::statement::InvokeOracle;
use crate::statement::{Assignment, AssignmentRhs, CodeBlock, Pattern, Statement};
use crate::theorem::GameInstance;
use crate::transforms::samplify::SampleInfo;
use crate::types::Type;

use crate::types::TypeKind;
use crate::writers::smt::exprs::{SmtAs, SmtEq2, SmtExpr, SmtIte, SmtLet};

use crate::writers::smt::contexts::{
    GameInstanceContext, GenericOracleContext, OracleContext, PackageInstanceContext,
};
use crate::writers::smt::names;
use crate::writers::smt::patterns::oracle_args::{GameConstsPattern, OracleArgPattern};
use crate::writers::smt::patterns::{
    variables::GameStatePattern, variables::VariablePattern, FunctionPattern, ReturnValue,
    ReturnValueSelector,
};

use crate::writers::smt::patterns;
use patterns::DatastructurePattern;

pub(crate) struct CompositionSmtWriter<'a> {
    game_inst: &'a GameInstance,

    sample_info: &'a SampleInfo,
}

impl<'a> CompositionSmtWriter<'a> {
    pub(crate) fn new(
        game_inst: &'a GameInstance,
        sample_info: &'a SampleInfo,
    ) -> CompositionSmtWriter<'a> {
        CompositionSmtWriter {
            game_inst,
            sample_info,
        }
    }

    fn context(&self) -> GameInstanceContext<'a> {
        GameInstanceContext::new(self.game_inst)
    }

    fn get_package_instance_context(&self, inst_name: &str) -> Option<PackageInstanceContext<'a>> {
        self.context().pkg_inst_ctx_by_name(inst_name)
    }

    fn this_oracle_ctx(&self, inst_name: &str, oracle_name: &str) -> Option<OracleContext<'a>> {
        self.get_package_instance_context(inst_name)?
            .oracle_ctx_by_name(oracle_name)
    }

    fn get_randomness<GS: Into<SmtExpr>>(
        &self,
        gamestate: GS,
        sample_id: usize,
    ) -> Option<SmtExpr> {
        let game_context = self.context();

        game_context.smt_access_gamestate_rand(self.sample_info, gamestate, sample_id)
    }

    fn smt_codeblock(&self, oracle_ctx: &OracleContext, block: CodeBlock) -> SmtExpr {
        let game_inst_ctx = self.context();
        let game_inst = game_inst_ctx.game_inst();
        let game = game_inst_ctx.game();

        let mut stmts = block.0.iter().rev();

        let innermost = stmts.next();
        let mut result = self.smt_build_innermost_nonsplit(oracle_ctx, innermost.unwrap());

        for stmt in stmts {
            result = match stmt {
                Statement::IfThenElse(ite) => SmtIte {
                    cond: &ite.cond,
                    then: self.smt_codeblock(oracle_ctx, ite.then_block.clone()),
                    els: self.smt_codeblock(oracle_ctx, ite.else_block.clone()),
                }
                .into(),
                Statement::Return(None, _) => {
                    // (mk-return-{name} statevarname expr)
                    self.smt_build_return_none_nonsplit(oracle_ctx)
                }
                Statement::Return(Some(expr), _) => {
                    // (mk-return-{name} statevarname expr)
                    self.smt_build_return_some_nonsplit(oracle_ctx, expr)
                }
                Statement::Abort(_) => {
                    // mk-abort-{name}
                    self.smt_build_abort(oracle_ctx)
                }
                Statement::For(_, _, _, _, _) => {
                    let game_inst_name = game_inst.name();
                    let _game_name = game.name();
                    let pkg_inst_name = &oracle_ctx.pkg_inst_ctx().pkg_inst().name;
                    let pkg_name = &oracle_ctx.pkg_inst_ctx().pkg_inst().pkg.name;
                    let oracle_name = oracle_ctx.oracle_name();
                    unreachable!("found a for statement in the smt writer stage. \
                                 this should have been eliminated by now and can't be handled here. \
                                 game:{game_inst_name}(game_name) pkg:{pkg_inst_name}({pkg_name}) oracle:{oracle_name}", game_inst_name = game_inst_name, pkg_inst_name = pkg_inst_name, pkg_name = pkg_name, oracle_name = oracle_name)
                }
                Statement::InvokeOracle(InvokeOracle { edge: None, .. }) => {
                    panic!("found an unresolved standalone oracle invocation: {stmt:#?}");
                }
                Statement::InvokeOracle(InvokeOracle {
                    args,
                    edge: Some(edge),
                    ..
                }) => {
                    let discard_ident = Identifier::Generated("_".to_string(), Type::empty());
                    self.smt_build_invoke(oracle_ctx, result, &discard_ident, None, args, edge)
                }
                Statement::Assignment(Assignment { pattern, rhs }, _) => {
                    match (pattern, rhs) {
                        (Pattern::Tuple(idents), AssignmentRhs::Expression(expr)) => {
                            self.smt_build_parse(oracle_ctx, result, idents, expr)
                        }
                        (Pattern::Tuple(_), _) => {
                            unreachable!("tuple pattern with non-expression rhs")
                        }
                        (pat, rhs) => {
                            let (ident, opt_idx) = match pat {
                                Pattern::Ident(id) => (id, None),
                                Pattern::Table { ident, index } => (ident, Some(index.clone())),
                                Pattern::Tuple(_) => unreachable!(),
                            };
                            match rhs {
                                // TODO actually use the type that we sample to know how far to advance the randomness tape
                                AssignmentRhs::Sample {
                                    sample_id,
                                    ty,
                                    sample_name,
                                } => self.smt_build_sample(
                                    oracle_ctx,
                                    result,
                                    ident,
                                    opt_idx.as_ref(),
                                    *sample_id,
                                    ty,
                                    sample_name.as_ref(),
                                ),
                                AssignmentRhs::Invoke { edge: None, .. } => {
                                    panic!("found an unresolved oracle invocation: {stmt:#?}");
                                }
                                AssignmentRhs::Invoke {
                                    return_type: None, ..
                                } => {
                                    panic!("found an oracle invocation with unknown return type: {stmt:#?}");
                                }
                                AssignmentRhs::Invoke {
                                    args,
                                    edge: Some(edge),
                                    return_type: Some(_),
                                    ..
                                } => self.smt_build_invoke(
                                    oracle_ctx,
                                    result,
                                    ident,
                                    opt_idx.as_ref(),
                                    args,
                                    edge,
                                ),
                                AssignmentRhs::Expression(expr) => self.smt_build_assign(
                                    oracle_ctx,
                                    result,
                                    ident,
                                    opt_idx.as_ref(),
                                    expr,
                                ),
                            }
                        }
                    }
                }
            };
        }
        result
    }

    fn smt_build_innermost_nonsplit(
        &self,
        oracle_ctx: &OracleContext,
        stmt: &Statement,
    ) -> SmtExpr {
        match stmt {
            Statement::IfThenElse(ite) => SmtIte {
                cond: &ite.cond,
                then: self.smt_codeblock(oracle_ctx, ite.then_block.clone()),
                els: self.smt_codeblock(oracle_ctx, ite.else_block.clone()),
            }
            .into(),
            Statement::Return(None, _) => {
                // (mk-return-{name} statevarname expr)
                self.smt_build_return_none_nonsplit(oracle_ctx)
            }
            Statement::Return(Some(expr), _) => {
                // (mk-return-{name} statevarname expr)
                self.smt_build_return_some_nonsplit(oracle_ctx, expr)
            }
            Statement::Abort(_) => {
                // mk-abort-{name}
                self.smt_build_abort(oracle_ctx)
            }
            _ => unreachable!("found invalid statement at end of oracle: {:#?}", stmt),
        }
    }

    fn smt_build_return_none_nonsplit(&self, oracle_ctx: &OracleContext) -> SmtExpr {
        let new_game_state = oracle_ctx.smt_write_back_state(self.sample_info);
        oracle_ctx.smt_construct_return(new_game_state, "mk-empty")
    }

    fn smt_build_return_some_nonsplit(
        &self,
        oracle_ctx: &OracleContext,
        expr: &Expression,
    ) -> SmtExpr {
        let new_game_state = oracle_ctx.smt_write_back_state(self.sample_info);
        oracle_ctx.smt_construct_return(new_game_state, expr)
    }

    fn smt_build_abort<OCTX: GenericOracleContext<'a>>(&self, oracle_ctx: &OCTX) -> SmtExpr {
        let new_game_state = oracle_ctx.smt_write_back_state(self.sample_info);
        let var_game_state = &GameStatePattern;
        let body = oracle_ctx.smt_construct_abort(var_game_state);
        let bindings = vec![(var_game_state.name(), new_game_state)];
        SmtLet { bindings, body }.into()
    }

    /*
     *   1. get counter
     *   2. assign ident
     *   3. overwrite state
     *   4. continue
     *
     * let
     *   ident = sample(ctr)
     *   __global = mk-compositionState ( mk-randomndess-state (ctr + 1) ... )
     *
     *
     * ,
     *   let (ident = rand(access(counter)) (
     *       // TODO update this to the new context-based helpers structure
     *       comp_helper.smt_set(counter, counter+1, body)
     * ))
     * )
     *
     */

    fn smt_build_sample<OCTX: GenericOracleContext<'a>>(
        &self,
        oracle_ctx: &OCTX,
        result: SmtExpr,
        ident: &Identifier,
        opt_idx: Option<&Expression>,
        sample_id: Option<usize>,
        ty: &Type,
        sample_name: Option<&String>,
    ) -> SmtExpr {
        let sample_id = sample_id.expect("found a None sample_id");
        let sample_pos = &self.sample_info.positions[sample_id];
        debug_assert!(sample_name.is_some_and(|name| *name == sample_pos.sample_name));

        let game_inst_ctx = self.context();

        let game_inst_name = game_inst_ctx.game_inst_name();

        let gamestate = oracle_ctx.smt_game_state();
        // ctr is the current "i-th sampling for sample id sample_id"
        let ctr = self
            .get_randomness(gamestate, sample_id)
            .unwrap_or_else(|| {
                let max_known_sample_id = self.sample_info.count;
                panic!(
                    "found sample id {sample_id} that exceeds highest expected {max_known_sample_id}"
                )
            });

        let rand_fn_name = names::fn_sample_rand_name(game_inst_name, ty);

        let rand_val: SmtExpr = (rand_fn_name, sample_pos, ctr.clone()).into();

        let new_val = if let Some(idx) = opt_idx {
            ("store", ident, idx, rand_val.clone()).into()
        } else {
            rand_val
        };

        let bindings = vec![(ident.ident(), new_val)]
            .into_iter()
            .filter(|(x, _)| x != "_")
            .collect();

        let var_gamestate = &GameStatePattern;
        let new_gamestate = game_inst_ctx
            .smt_increment_gamestate_rand(var_gamestate, self.sample_info, sample_id)
            .unwrap();

        SmtLet {
            bindings,
            body: SmtLet {
                bindings: vec![(var_gamestate.name(), new_gamestate)],
                body: result,
            },
        }
        .into()
    }

    fn smt_build_parse<OCTX: GenericOracleContext<'a>>(
        &self,
        _oracle_ctx: &OCTX,
        result: SmtExpr,
        idents: &[Identifier],
        expr: &Expression,
    ) -> SmtExpr {
        let TypeKind::Tuple(types) = expr.get_type().into_kind() else {
            unreachable!("if this wasn't a tuple type, the type checker would have complained")
        };
        let bindings = idents
            .iter()
            .enumerate()
            .filter(|(_, ident)| ident.ident_ref() != "_")
            .map(|(i, ident)| {
                (
                    ident.ident(),
                    (format!("el{}-{}", types.len(), i + 1), expr).into(),
                )
            })
            .collect();

        SmtLet {
            bindings,
            body: result,
        }
        .into()
    }

    #[allow(clippy::too_many_arguments)]
    fn smt_build_invoke<OCTX: GenericOracleContext<'a>>(
        &self,
        this_oracle_ctx: &OCTX,
        body: SmtExpr,
        assignee_ident: &Identifier,
        opt_idx: Option<&Expression>,
        args: &[Expression],
        edge: &Edge,
    ) -> SmtExpr {
        let pkg_inst_ctx = this_oracle_ctx.pkg_inst_ctx();
        let game_inst_ctx = pkg_inst_ctx.game_inst_ctx();

        let pkg_inst = pkg_inst_ctx.pkg_inst();
        let game_name = game_inst_ctx.game_name();

        let target = &self.game_inst.game.pkgs[edge.to()];

        let called_oracle_context = self
            .this_oracle_ctx(&target.name, &edge.sig().name)
            .unwrap();

        let var_gamestate = &GameStatePattern;
        let var_gameconsts = GameConstsPattern { game_name };

        let updated_pkgstate = pkg_inst_ctx.smt_update_pkgstate_from_locals().unwrap();
        let updated_game_state = game_inst_ctx
            .smt_update_gamestate_pkgstate(
                var_gamestate,
                self.sample_info,
                &pkg_inst.name,
                updated_pkgstate,
            )
            .unwrap();

        let abort_body = this_oracle_ctx.smt_construct_abort(updated_game_state);

        let let_bindings = vec![(
            var_gamestate.name(),
            called_oracle_context.smt_access_return_state(names::var_ret_name()),
        )];

        let return_value_pattern = ReturnValue::new(this_oracle_ctx.oracle_return_type());
        let return_value_spec = return_value_pattern.datastructure_spec(&());

        let call_result = called_oracle_context
            .smt_call_oracle_fn(
                var_gamestate,
                var_gameconsts.local_arg_name(),
                args.iter().map(|expr| expr.into()),
            )
            .unwrap();

        let smt_expr = SmtLet {
            bindings: vec![(names::var_ret_name(), call_result)],
            body: SmtIte {
                cond: called_oracle_context.smt_access_return_is_abort(names::var_ret_name()),
                then: SmtLet {
                    bindings: let_bindings.clone(),
                    body: abort_body,
                },
                els: SmtLet {
                    bindings: {
                        let mut bindings = let_bindings.clone();

                        if assignee_ident.ident() != "_" {
                            bindings.push((
                                assignee_ident.smt_identifier_string(),
                                return_value_pattern
                                    .access(
                                        &return_value_spec,
                                        &ReturnValueSelector,
                                        called_oracle_context
                                            .smt_access_return_value(names::var_ret_name()),
                                    )
                                    .unwrap(),
                            ));
                        }

                        bindings
                    },
                    body,
                },
            },
        };

        if let Some(opt_idx) = opt_idx {
            ("store", assignee_ident, opt_idx, smt_expr).into()
        } else {
            smt_expr.into()
        }
    }

    fn smt_build_assign<OCTX: GenericOracleContext<'a>>(
        &self,
        oracle_ctx: &OCTX,
        result: SmtExpr,
        ident: &Identifier,
        opt_idx: Option<&Expression>,
        expr: &Expression,
    ) -> SmtExpr {
        let t = expr.get_type();

        //eprintln!(r#"DEBUG code_smt_helper Assign {expr:?} to identifier {ident:?}")"#);

        // first build the unwrap expression, if we have to
        let outexpr = if let ExpressionKind::Unwrap(inner) = expr.kind() {
            ("maybe-get", &**inner).into()
        } else {
            expr.into()
        };

        // then build the table store smt expression, in case we have to
        let outexpr = if let Some(idx) = opt_idx {
            let oldvalue: SmtExpr = ident.smt_identifier_string().into();

            ("store", oldvalue, idx, outexpr).into()
        } else {
            outexpr
        };

        // build the actual smt assignment
        let smtout = SmtLet {
            bindings: vec![(ident.smt_identifier_string(), outexpr)],
            body: { result },
        }
        .into();

        // if it's an unwrap, also wrap it with the unwrap check.
        if let ExpressionKind::Unwrap(inner) = expr.kind() {
            SmtIte {
                cond: SmtEq2 {
                    lhs: &**inner,
                    rhs: SmtAs {
                        term: "mk-none",
                        sort: Type::maybe(t).into(),
                    },
                },
                then: oracle_ctx.smt_construct_abort(&GameStatePattern),
                els: smtout,
            }
            .into()
        } else {
            smtout
        }
    }

    pub(crate) fn smt_define_oracle_fn(&self, inst: &PackageInstance, def: &OracleDef) -> SmtExpr {
        let pkg_inst_name = &inst.name;
        let oracle_sig = &def.sig;
        let oracle_name = &oracle_sig.name;

        let game_inst_ctx = self.context();
        let pkg_inst_ctx = game_inst_ctx
            .pkg_inst_ctx_by_name(pkg_inst_name)
            .expect("couldn't find package instance with name {inst_name}");
        let octx = pkg_inst_ctx
            .oracle_ctx_by_name(oracle_name)
            .expect("couldn't find oracle with name {oracle_name}");

        let var_globalstate = &GameStatePattern;
        let pkg_state = game_inst_ctx
            .smt_access_gamestate_pkgstate(var_globalstate, pkg_inst_name)
            .unwrap();

        let inner = self.smt_codeblock(&octx, def.code.clone());

        let pkgstate_bindings = inst.pkg.state.iter().map(|(name, _ty, _)| {
            (
                name.clone(),
                pkg_inst_ctx
                    .smt_access_pkgstate(pkg_state.clone(), name)
                    .unwrap(),
            )
        });

        let pkg_consts = pkg_inst_ctx
            .function_pkg_const_pattern()
            .call(&["<game-consts>".into()])
            .unwrap();

        let const_bindwrapped = patterns::datastructures::pkg_consts::bind_pkg_consts(
            pkg_inst_ctx.pkg(),
            &pkg_consts,
            inner,
        );

        let state_bindwrapped = SmtLet {
            bindings: pkgstate_bindings.collect(),
            body: const_bindwrapped,
        };

        log::debug!("pkg inst params: {:?}", inst.params);

        octx.oracle_pattern().define_fun(state_bindwrapped).into()
    }

    pub(crate) fn smt_composition_randomness(&mut self) -> impl Iterator<Item = SmtExpr> {
        let game_inst_ctx = self.context();
        let game_inst = game_inst_ctx.game_inst();

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
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::fmt::Write;
    use std::string::FromUtf8Error;
    use thiserror::Error;

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
