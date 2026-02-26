// SPDX-License-Identifier: MIT OR Apache-2.0

use std::collections::HashSet;

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
use crate::writers::smt::exprs::{SmtExpr, SmtIte, SmtLet};

use super::contexts::{
    GameInstanceContext, GenericOracleContext, OracleContext, PackageInstanceContext,
};
use super::exprs::{SmtAs, SmtEq2};
use super::names;
use super::patterns::oracle_args::{GameConstsPattern, OracleArgPattern};
use super::patterns::{
    variables::GameStatePattern, variables::VariablePattern, FunctionPattern, ReturnValue,
    ReturnValueSelector,
};

use super::patterns;
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

    fn this_normal_oracle_ctx(
        &self,
        inst_name: &str,
        oracle_name: &str,
    ) -> Option<OracleContext<'a>> {
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

    fn smt_codeblock_nonsplit(&self, oracle_ctx: &OracleContext, block: CodeBlock) -> SmtExpr {
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
                    then: self.smt_codeblock_nonsplit(oracle_ctx, ite.then_block.clone()),
                    els: self.smt_codeblock_nonsplit(oracle_ctx, ite.else_block.clone()),
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

    // fn smt_codeblock_split(&self, oracle_ctx: &SplitOracleContext, block: CodeBlock) -> SmtExpr {
    //     let game_inst_ctx = self.context();
    //     let game_inst = game_inst_ctx.game_inst();
    //     let game = game_inst_ctx.game();
    //
    //     let mut stmts = block.0.iter().rev();
    //
    //     let innermost = stmts.next();
    //     let mut result = self.smt_build_innermost_split(oracle_ctx, innermost.unwrap());
    //
    //     for stmt in stmts {
    //         result = match stmt {
    //             Statement::IfThenElse(ite) => SmtIte {
    //                 cond: ite.cond.clone(),
    //                 then: self.smt_codeblock_split(oracle_ctx, ite.then_block.clone()),
    //                 els: self.smt_codeblock_split(oracle_ctx, ite.else_block.clone()),
    //             }
    //             .into(),
    //             Statement::Return(None, _) => {
    //                 // (mk-return-{name} statevarname expr)
    //                 todo!();
    //                 //self.smt_build_return_none_nonsplit(oracle_ctx)
    //             }
    //             Statement::Return(Some(_expr), _) => {
    //                 // (mk-return-{name} statevarname expr)
    //                 todo!();
    //                 //self.smt_build_return_some_nonsplit(oracle_ctx, expr)
    //             }
    //             Statement::Abort(_) => {
    //                 // mk-abort-{name}
    //                 self.smt_build_abort(oracle_ctx)
    //             }
    //             Statement::For(_, _, _, _, _) => {
    //                 let game_inst_name = game_inst.name();
    //                 let _game_name = game.name();
    //                 let pkg_inst_name = &oracle_ctx.pkg_inst_ctx().pkg_inst().name;
    //                 let pkg_name = &oracle_ctx.pkg_inst_ctx().pkg_inst().pkg.name;
    //                 let oracle_name = oracle_ctx.oracle_name();
    //                 unreachable!("found a for statement in the smt writer stage. \
    //                              this should have been eliminated by now and can't be handled here. \
    //                              game:{game_inst_name}(game_name) pkg:{pkg_inst_name}({pkg_name}) oracle:{oracle_name}", game_inst_name = game_inst_name, pkg_inst_name = pkg_inst_name, pkg_name =pkg_name, oracle_name = oracle_name)
    //             }
    //             // TODO actually use the type that we sample to know how far to advance the randomness tap
    //             Statement::Sample(ident, opt_idx, sample_id, ty, _) => {
    //                 self.smt_build_sample(oracle_ctx, result, ident, opt_idx, sample_id, ty)
    //             }
    //             Statement::Parse(idents, expr, _) => {
    //                 self.smt_build_parse(oracle_ctx, result, idents, expr)
    //             }
    //             Statement::InvokeOracle(InvokeOracleStatement {
    //                 target_inst_name: None,
    //                 ..
    //             }) => {
    //                 panic!("found an unresolved oracle invocation: {:#?}", stmt);
    //             }
    //             Statement::InvokeOracle(InvokeOracleStatement { ty: None, .. }) => {
    //                 panic!("found an unresolved oracle invocation: {:#?}", stmt);
    //             }
    //             Statement::InvokeOracle(InvokeOracleStatement {
    //                 id,
    //                 opt_idx,
    //                 name,
    //                 args,
    //                 target_inst_name: Some(target),
    //                 ty: Some(_),
    //                 ..
    //             }) => self.smt_build_invoke(oracle_ctx, result, id, opt_idx, name, args, target),
    //             Statement::Assign(ident, opt_idx, expr, _) => {
    //                 self.smt_build_assign(oracle_ctx, result, ident, opt_idx, expr)
    //             }
    //         };
    //     }
    //     result
    // }

    fn smt_build_innermost_nonsplit(
        &self,
        oracle_ctx: &OracleContext,
        stmt: &Statement,
    ) -> SmtExpr {
        match stmt {
            Statement::IfThenElse(ite) => SmtIte {
                cond: &ite.cond,
                then: self.smt_codeblock_nonsplit(oracle_ctx, ite.then_block.clone()),
                els: self.smt_codeblock_nonsplit(oracle_ctx, ite.else_block.clone()),
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

    /*
     *
     * what is it that we have to do here?
     * - build either an abort or a return
     * - a return needs to contain the correct partial state for the next partial oracle invocation
     *
     * q: when we have progressed to this place, the code has already been rewritten
     *    by the partial split transform and if-then-elses that need to have
     *    been split have been removed. what is it then that is at the end of the oracles?
     * a: code now panics because the oracle codeblock ends in an assign, so maybe it can be
     *    anything? that's weird though, because the split partial transform is before the
     *    returnify transform. whatever code was returned by splitpartial should have been
     *    returnified...
     *    oh wait! the returnify transform does not operate on split oracles, only regulare ones!
     *    this seems to be a problem with separating the two that we hadn't factored in yet :(
     *    that could be fixed by just also looping over the code of the split_oracles. glad it was
     *    that easy!
     *
     * log: we still have the problem that, when sampling, we try to access the gamestate by
    // *      doing (select __global_state __state_length), which won't work here: we only have
     *      one game state here.
     *      maybe we need to add a method to the GenericOracleContext trait that returns the
     *      SmtExpr that evaluates to the gamestate in the context of the oracle.
     * log: okay, looks like i have removed a lot of instances where this is a problem. now
     *      this happens when _storing_ something in the gamestate variable. but i'll call it a
     *      night for now :)
     * log: new day!
     *      we have started migrating the nonsplit return to also just have a single game state.
     *      that should make things simpler, hopefully!
     *      now it fails at the return statement below again
     *
     * what to do on return?
     * - figure out next state. how?
     *   - current path type
     *     - ifcond => if cond, then next, else elsenext
     *     - forstep => if still in range next, else elsenext
     *     - _ => next
     *
     * - how do we get the path type?
     *    - ofthen there is a trailing /plain
     *    - just start with last and go back until we find the right one
     *
     *
     *
     * */

    // fn smt_build_next_intermediate_state(
    //     &self,
    //     oracle_ctx: &SplitOracleContext,
    // ) -> Option<SmtExpr> {
    //     // println!("building next state");
    //     // println!("split oracle name: {}", oracle_ctx.split_path().smt_name());
    //
    //     let path = oracle_ctx.split_path();
    //     let entry = self
    //         .split_info
    //         .iter()
    //         .find(|entry| entry.path() == path)
    //         .unwrap();
    //     let branches = entry.branches();
    //     // println!("branches: {branches:?}");
    //
    //     let first_true = branches
    //         .iter()
    //         .position(|(cond, _)| cond == &Expression::BooleanLiteral("true".to_string()))
    //         .unwrap_or_else(|| panic!("branches: {:?}", branches));
    //
    //     let (_, elsepath) = &branches[first_true];
    //     let mut block: SmtExpr = self.smt_build_intermediate_state_from_path(oracle_ctx, elsepath);
    //
    //     for i in (0..=first_true).rev().skip(1) {
    //         let (cond, ifpath) = &branches[i];
    //         let ifblock = self.smt_build_intermediate_state_from_path(oracle_ctx, ifpath);
    //
    //         block = SmtIte {
    //             cond: cond.clone(),
    //             then: ifblock,
    //             els: block,
    //         }
    //         .into();
    //     }
    //
    //     // println!("block: {block}");
    //
    //     Some(block)
    // }
    //
    // fn smt_build_intermediate_state_from_path(
    //     &self,
    //     oracle_ctx: &SplitOracleContext,
    //     path: &SplitPath,
    // ) -> SmtExpr {
    //     let pkg_inst = oracle_ctx.pkg_inst_ctx().pkg_inst();
    //
    //     let params = &pkg_inst.params;
    //     let pkg_name = &pkg_inst.pkg.name;
    //     let oracle_name = oracle_ctx.oracle_name();
    //
    //     let pattern = IntermediateStatePattern {
    //         pkg_name,
    //         params,
    //         oracle_name,
    //     };
    //
    //     let spec = pattern.datastructure_spec(oracle_ctx.partials_dtype());
    //
    //     let common_prefix = oracle_ctx.split_path().common_prefix(path);
    //     let common_loopvars =
    //         common_prefix
    //             .path()
    //             .iter()
    //             .filter_map(|elem| match elem.split_type() {
    //                 SplitType::ForStep(name, start, _) => Some((name, start)),
    //                 _ => None,
    //             });
    //
    //     let their_loopvars = path
    //         .path()
    //         .iter()
    //         .filter_map(|elem| match elem.split_type() {
    //             SplitType::ForStep(name, start, _) => Some((name, start)),
    //             _ => None,
    //         });
    //
    //     let is_next_iteration = path < oracle_ctx.split_path();
    //
    //     let mut next_loopvar_values = vec![];
    //
    //     for (name, start) in their_loopvars {
    //         let is_common = common_loopvars
    //             .clone()
    //             .any(|(their_name, _)| name == their_name);
    //
    //         next_loopvar_values.push(match (is_common, is_next_iteration) {
    //             (true, true) => (
    //                 name.ident(),
    //                 (
    //                     "+",
    //                     1,
    //                     pattern
    //                         .access(
    //                             &spec,
    //                             &IntermediateStateSelector::LoopVar(path, name.ident_ref()),
    //                             "__intermediate_state",
    //                         )
    //                         .unwrap(),
    //                 )
    //                     .into(),
    //             ),
    //             (true, false) => (
    //                 name.ident(),
    //                 pattern
    //                     .access(
    //                         &spec,
    //                         &IntermediateStateSelector::LoopVar(path, name.ident_ref()),
    //                         "__intermediate_state",
    //                     )
    //                     .unwrap(),
    //             ),
    //             (false, _) => (name.ident(), start.clone().into()),
    //         })
    //     }
    //
    //     pattern
    //         .call_constructor(
    //             &spec,
    //             vec![],
    //             &IntermediateStateConstructor::OracleState(path),
    //             |sel| {
    //                 Some(match sel {
    //                     IntermediateStateSelector::Arg(_, name, _)
    //                     | IntermediateStateSelector::Local(_, name, _) => (*name).into(),
    //                     IntermediateStateSelector::LoopVar(_, name) => {
    //                         let (_, next_value) = next_loopvar_values
    //                             .iter()
    //                             .find(|(lv_name, _next_value)| lv_name == name)
    //                             .unwrap();
    //                         next_value.clone()
    //                     }
    //                     IntermediateStateSelector::Child(_) => "mk-child-this-is-wrong".into(),
    //                     IntermediateStateSelector::Return(_) => unreachable!(),
    //                 })
    //             },
    //         )
    //         .unwrap()
    //
    //     // let constructor = IntermediateStateConstructor::OracleState(path);
    //     // let constructor_name = pattern.constructor_name(&constructor);
    //     //
    //     // let entry = self
    //     //     .split_info
    //     //     .iter()
    //     //     .find(|entry| entry.path() == path)
    //     //     .unwrap();
    //     //
    //     // let mut locals: Vec<SmtExpr> = entry
    //     //     .locals()
    //     //     .iter()
    //     //     .map(|(name, _)| name.clone().into())
    //     //     .collect();
    //     //
    //     // let mut fn_call = vec![constructor_name.into()];
    //     // fn_call.append(&mut locals);
    //     //
    //     // SmtExpr::List(fn_call)
    // }
    //
    // fn smt_build_innermost_split(
    //     &self,
    //     oracle_ctx: &SplitOracleContext,
    //     stmt: &Statement,
    // ) -> SmtExpr {
    //     //let odef = oracle_ctx.oracle_def();
    //     let game_inst_ctx = oracle_ctx.game_inst_ctx();
    //     let pkg_inst = oracle_ctx.pkg_inst_ctx().pkg_inst();
    //
    //     let game_name = game_inst_ctx.game().name();
    //     let game_params = &game_inst_ctx.game_inst().consts;
    //
    //     let pkg_name = &pkg_inst.pkg.name;
    //     let pkg_params = &pkg_inst.params;
    //
    //     let oracle_name = oracle_ctx.oracle_name();
    //
    //     //("todo_build_innermost_split",).into();
    //     match stmt {
    //         Statement::IfThenElse(cond, ifcode, elsecode, _) => SmtIte {
    //             cond: cond.clone(),
    //             then: self.smt_codeblock_split(oracle_ctx, ifcode.clone()),
    //             els: self.smt_codeblock_split(oracle_ctx, elsecode.clone()),
    //         }
    //         .into(),
    //         // this is probably wrong because we don't have any selectors, but maybe it's ok idk:
    //         Statement::Abort(_) => {
    //             let partial_return_pattern = PartialReturnPattern {
    //                 game_name,
    //                 game_params,
    //                 pkg_name,
    //                 pkg_params,
    //                 oracle_name,
    //             };
    //             let spec = partial_return_pattern.datastructure_spec(&());
    //             partial_return_pattern
    //                 .call_constructor(
    //                     &spec,
    //                     vec![],
    //                     &PartialReturnConstructor::Abort,
    //                     |_| unreachable!(),
    //                 )
    //                 .unwrap()
    //         }
    //         Statement::Return(None, _) => {
    //             let partial_return_pattern = PartialReturnPattern {
    //                 game_name,
    //                 game_params,
    //                 pkg_name,
    //                 pkg_params,
    //                 oracle_name,
    //             };
    //
    //             let spec = partial_return_pattern.datastructure_spec(&());
    //             partial_return_pattern
    //                 .call_constructor(&spec, vec![], &PartialReturnConstructor::Return, |sel| {
    //                     Some(match sel {
    //                         patterns::PartialReturnSelector::GameState => "__global_state".into(),
    //                         patterns::PartialReturnSelector::IntermediateState => {
    //                             let ipattern = oracle_ctx.intermediate_state_pattern();
    //                             let ispec =
    //                                 ipattern.datastructure_spec(oracle_ctx.partials_dtype());
    //                             ipattern
    //                                 .call_constructor(
    //                                     &ispec,
    //                                     vec![],
    //                                     &IntermediateStateConstructor::End,
    //                                     |sel| {
    //                                         Some(match sel {
    //                                             IntermediateStateSelector::Arg(_, _, _)
    //                                             | IntermediateStateSelector::LoopVar(_, _)
    //                                             | IntermediateStateSelector::Local(_, _, _)
    //                                             | IntermediateStateSelector::Child(_) => {
    //                                                 unreachable!()
    //                                             }
    //                                             IntermediateStateSelector::Return(_) => {
    //                                                 "mk-empty".into()
    //                                             }
    //                                         })
    //                                     },
    //                                 )
    //                                 .unwrap()
    //                         }
    //                     })
    //                 })
    //                 .unwrap()
    //         }
    //         Statement::Return(Some(_expr), _) => {
    //             // (mk-return-{name} statevarname expr)
    //             // self.smt_build_return_some(oracle_ctx, expr)
    //
    //             // this is also a real return
    //             ("todo_build_innermost_split_some_return",).into()
    //         }
    //         _ => {
    //             // build the generic partialreturn and let the caller know that this statment still
    //             // needs to be processed
    //
    //             let next_state =
    //                 if let Some(next_state) = self.smt_build_next_intermediate_state(oracle_ctx) {
    //                     next_state
    //                 } else {
    //                     let constructor_name = IntermediateStatePattern {
    //                         pkg_name,
    //                         params: pkg_params,
    //                         oracle_name,
    //                     }
    //                     .constructor_name(&IntermediateStateConstructor::End);
    //
    //                     (constructor_name, "mk-empty").into()
    //                 };
    //             // let split_path = oracle_ctx.split_path();
    //             // let this_entry = self
    //             //     .split_info
    //             //     .iter()
    //             //     .find(|entry| entry.path() == split_path)
    //             //     .unwrap();
    //             // println!("{} -- {:#?}", split_path.smt_name(), this_entry);
    //
    //             let partial_return_pattern = PartialReturnPattern {
    //                 game_name,
    //                 game_params,
    //                 pkg_name,
    //                 pkg_params,
    //                 oracle_name,
    //             };
    //
    //             let constructor_name =
    //                 partial_return_pattern.constructor_name(&PartialReturnConstructor::Return);
    //
    //             (constructor_name, "<game-state>", next_state).into()
    //         }
    //     }
    // }

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
            .this_normal_oracle_ctx(&target.name, &edge.sig().name)
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

    // fn smt_next_gamestate<S: Into<SmtExpr>>(
    //     oracle_ctx: &OracleContext,
    //     entry: &SplitInfoEntry,
    //     ret_stmt: &Statement,
    //     old_gamestate: S,
    // ) -> SmtExpr {
    //     let oracle_name = &oracle_ctx.oracle_def().sig.name;
    //     let pkg_inst_name = oracle_ctx.pkg_inst_ctx().pkg_inst_name();
    //
    //     let mut cur_path = entry.path();
    //
    //     // we need to figure out the gamestates for both next and elsenext
    //
    //     let shared_prefix_next = entry
    //         .next()
    //         .map(|next| cur_path.longest_shared_prefix(next));
    //
    //     let shared_prefix_elsenext = entry
    //         .elsenext()
    //         .map(|next| cur_path.longest_shared_prefix(next));
    //
    //     let shared_prefix_next = match shared_prefix_next {
    //         None => return oracle_ctx.smt_access_intermediate_parent(old_gamestate),
    //         Some(x) => x,
    //     };
    //
    //     todo!()
    //
    //     // x <- Foo() ---
    //     // ----------   | next
    //     // return x   <--
    //
    //     // .../Invoc():
    //     //     invoke Oracle
    //     //
    //     // .../Plain
    //     // .../Invoc/...
    //     // .../Invoc/...
    //     // .../Plain
    //
    //     // We are in a partial function!
    //     //
    //     // what now?
    //     // -> construct next partial state!
    //     //    what is the next parent?
    //     //    enter function: push!
    //     //    leave function: pop!
    //     //    else:           copy!
    //     //
    //     // complications:
    //     // - next or elsenext?
    //     // - what if we leave multiple functions at once?
    //     //   - this can't happen: after an invoc there definitely is a plain block
    //     //     with a return statement
    //     //     - TODO: partial_split transform: make sure there the is a return if
    //     //             invoc is last statement
    //     // - we also can't leave and enter at the same time
    //     //
    //     // so: same as determine_next, but return actual smt expression for the
    //     // next partial state?
    //     // - find common prefix path
    //     // - pop path until common prefix
    //     //   - match popped path element
    //     //     - plain: skip
    //     //     - ifcond:
    //     //     - ifbranch
    //     //     - elsebranch
    //     //     - invoc
    //     //     - forstep
    //     // - go down to next
    //     //
    // }

    /* example
        (define-fun
            stored_key_equals_k
            ((state_all State_composition) (k Key))
            Return_stored-key-equals-k
            (let
                (state_key (state-composition-key state_all))
                (mk-stored-key-equals-k
                    state-all
                    (=
                        (state-key-k state_key)
                        k
                    )
                )
            )
        )
    */

    pub(crate) fn smt_define_nonsplit_oracle_fn(
        &self,
        inst: &PackageInstance,
        def: &OracleDef,
    ) -> SmtExpr {
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

        let inner = self.smt_codeblock_nonsplit(&octx, def.code.clone());

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

        log::debug!("pkg inst params: {:?}", &inst.params);

        octx.oracle_pattern().define_fun(state_bindwrapped).into()
    }

    // fn smt_define_split_oracle_fn(&self, split_oracle_ctx: &SplitOracleContext) -> SmtExpr {
    //     let game_inst_ctx = self.context();
    //     let game_name = game_inst_ctx.game().name();
    //     let game_params = &game_inst_ctx.game_inst().consts;
    //     let def = split_oracle_ctx.oracle_def();
    //     let pkg_inst = split_oracle_ctx.pkg_inst_ctx().pkg_inst();
    //     let pkg_name = &pkg_inst.pkg.name;
    //     let pkg_params = &pkg_inst.params;
    //
    //     let code = &def.code;
    //     let mut args = vec![
    //         (
    //             names::var_globalstate_name(),
    //             names::gamestate_sort_name(game_name),
    //         )
    //             .into(),
    //         (
    //             "__intermediate_state",
    //             split_oracle_ctx.intermediate_state_pattern().sort(vec![]),
    //         )
    //             .into(),
    //     ];
    //
    //     //args.extend(split_oracle_ctx.oracle_def().sig.path.additional_args());
    //
    //     let rest_args = def.sig.args.iter().cloned().map(|arg| arg.into());
    //     args.extend(rest_args);
    //
    //     let pkg_inst_name = &pkg_inst.name;
    //     let oracle_name = &split_oracle_ctx.oracle_def().sig.name;
    //     //let oracle_name = split_oracle_ctx.oracle_def().sig.name_with_path();
    //
    //     let split_path = &split_oracle_ctx.oracle_def().sig.path;
    //
    //     let partial_oracle_function_pattern = PartialOraclePattern {
    //         game_name,
    //         game_params,
    //         pkg_name,
    //         pkg_params,
    //         oracle_name,
    //         split_path,
    //     };
    //
    //     let pattern = split_oracle_ctx.intermediate_state_pattern();
    //     let dtype = split_oracle_ctx.partials_dtype();
    //     let spec = pattern.datastructure_spec(dtype);
    //     let intermediate_state_constructor = IntermediateStateConstructor::OracleState(split_path);
    //     let bindings = vec![(
    //         names::var_selfstate_name(),
    //         game_inst_ctx
    //             .smt_access_gamestate_pkgstate(names::var_globalstate_name(), pkg_inst_name)
    //             .unwrap(),
    //     )];
    //
    //     (
    //         "define-fun",
    //         partial_oracle_function_pattern.function_name(),
    //         SmtExpr::List(args.clone()),
    //         partial_oracle_function_pattern.function_return_sort(),
    //         SmtLet {
    //             bindings,
    //             body: pattern
    //                 .recover_variables(
    //                     &spec,
    //                     &intermediate_state_constructor,
    //                     self.smt_codeblock_split(split_oracle_ctx, code.clone()),
    //                 )
    //                 .unwrap(),
    //         },
    //     )
    //         .into()
    // }

    pub(crate) fn smt_composition_randomness(&mut self) -> Vec<SmtExpr> {
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
        let mut result: Vec<_> = smt_sorts
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
            .collect();

        // sort them so the order is deterministic
        result.sort();
        result
    }

    // pub(crate) fn smt_composition_partial_stuff(&self) -> Vec<SmtExpr> {
    //     let game_inst_ctx = self.context();
    //     let game = game_inst_ctx.game();
    //
    //     let partial_dtpes = into_partial_dtypes(self.split_info);
    //
    //     let mut return_typedefs = vec![];
    //     let mut intermediate_state_typedefs = vec![];
    //     let mut dispatch_fndefs = vec![];
    //     let mut split_oracle_fndefs = vec![];
    //
    //     for dtype in &partial_dtpes {
    //         let pkg_inst_name = &dtype.pkg_inst_name;
    //         let oracle_name = &dtype.real_oracle_sig.name;
    //         let _game_name = &game.name;
    //         let pkg_inst_ctx = game_inst_ctx.pkg_inst_ctx_by_name(pkg_inst_name).unwrap();
    //         let params = &pkg_inst_ctx.pkg_inst().params;
    //         let pkg_name = &pkg_inst_ctx.pkg_inst().pkg.name;
    //
    //         let intermediate_state_pattern = IntermediateStatePattern {
    //             pkg_name,
    //             params,
    //             oracle_name,
    //         };
    //         let intermediate_state_spec = intermediate_state_pattern.datastructure_spec(dtype);
    //
    //         // this can't work, because it looks for an existing oracle. but it doesn't exist
    //         // anymore
    //         //let oracle_ctx = pkg_inst_ctx.oracle_ctx_by_name(oracle_name).unwrap();
    //
    //         for step in &dtype.partial_steps {
    //             let orig_oracle_sig = &dtype.real_oracle_sig;
    //             let oname = &orig_oracle_sig.name;
    //             let opath = step.path().smt_name();
    //             let split_oracle_ctx = pkg_inst_ctx
    //                 .split_oracle_ctx_by_name_and_path(&orig_oracle_sig.name, step.path(), dtype)
    //                 .unwrap_or_else(|| {
    //                     panic!(
    //                         "couldn't find split oracle context for ({oname}, {opath}) in {:?}",
    //                         pkg_inst_ctx.pkg_inst().pkg.split_oracles
    //                     )
    //                 });
    //             split_oracle_fndefs.push(self.smt_define_split_oracle_fn(&split_oracle_ctx));
    //         }
    //
    //         return_typedefs.push(self.smt_declare_partial_return_datatype(dtype));
    //         intermediate_state_typedefs.push(declare_datatype(
    //             &intermediate_state_pattern,
    //             &intermediate_state_spec,
    //         ));
    //         dispatch_fndefs.push(pkg_inst_ctx.smt_declare_oracle_dispatch_function(dtype));
    //     }
    //
    //     let mut out = intermediate_state_typedefs;
    //
    //     out.append(&mut return_typedefs);
    //     out.append(&mut split_oracle_fndefs);
    //     out.append(&mut dispatch_fndefs);
    //     out
    // }
    //
    // pub(crate) fn smt_declare_partial_return_datatype(&self, dtype: &PartialsDatatype) -> SmtExpr {
    //     let PartialsDatatype { pkg_inst_name, .. } = dtype;
    //
    //     let game_inst_ctx = self.context();
    //     let pkg_inst_ctx = game_inst_ctx.pkg_inst_ctx_by_name(pkg_inst_name).unwrap();
    //
    //     let game_inst = game_inst_ctx.game_inst();
    //     let pkg_inst = pkg_inst_ctx.pkg_inst();
    //
    //     let game_name = game_inst.game_name();
    //     let game_params = &game_inst.consts;
    //     let pkg_name = &pkg_inst.pkg.name;
    //     let pkg_params = &pkg_inst.params;
    //
    //     let oracle_name = &dtype.real_oracle_sig.name;
    //
    //     let prp = patterns::PartialReturnPattern {
    //         game_name,
    //         game_params,
    //         pkg_name,
    //         pkg_params,
    //         oracle_name,
    //     };
    //
    //     let spec = prp.datastructure_spec(&());
    //     declare_datatype(&prp, &spec)
    // }
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
