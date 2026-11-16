use crate::{
    expressions::{Expression, ExpressionKind},
    identifier::Identifier,
    package::Edge,
    statement::{Assignment, AssignmentRhs, CodeBlock, InvokeOracle, Pattern, Statement},
    types::{Type, TypeKind},
    writers::smt::{
        contexts::OracleContext,
        exprs::{SmtAs, SmtEq2, SmtExpr, SmtIte, SmtLet},
        names::{self, FunctionNameBuilder},
        patterns::{
            oracle_args::{self, GameConstsPattern, OracleArgPattern},
            variables::{GameStatePattern, VariablePattern},
            DatastructurePattern, FunctionPattern, ReturnConstructor, ReturnSelector, ReturnValue,
            ReturnValueConstructor, ReturnValueSelector,
        },
    },
};

impl<'a> OracleContext<'a> {
    pub(crate) fn smt_game_state(&self) -> SmtExpr {
        "<game-state>".into()
    }

    pub(crate) fn smt_construct_abort<S: Into<SmtExpr>>(&self, game_state: S) -> SmtExpr {
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
    pub(crate) fn smt_call_oracle_fn<
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

    pub(crate) fn smt_arg_name(&self, arg_name: &str) -> SmtExpr {
        let game = self.game_inst_context.game_inst().game();
        let pkg_inst = &game.pkgs[self.pkg_inst_offs];
        let odef = &pkg_inst.pkg.oracles[self.oracle_offs];

        FunctionNameBuilder::new()
            .push("arg")
            .push(game.name())
            .push(self.renamed.unwrap_or(&odef.sig.name))
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
    pub(crate) fn smt_write_back_state(&self) -> SmtExpr {
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
                &pkg_inst.name,
                pkg_inst_ctx.smt_update_pkgstate_from_locals().unwrap(),
            )
            .unwrap()
    }

    pub(crate) fn smt_codeblock(&self, block: CodeBlock) -> SmtExpr {
        let mut stmts = block.0.iter().rev();

        let innermost = stmts.next();
        let mut result = self.smt_build_innermost(innermost.unwrap());

        for stmt in stmts {
            result = match stmt {
                Statement::IfThenElse(ite) => SmtIte {
                    cond: &ite.cond,
                    then: self.smt_codeblock(ite.then_block.clone()),
                    els: self.smt_codeblock(ite.else_block.clone()),
                }
                .into(),
                Statement::Return(None, _) => {
                    // (mk-return-{name} statevarname expr)
                    self.smt_build_return_none()
                }
                Statement::Return(Some(expr), _) => {
                    // (mk-return-{name} statevarname expr)
                    self.smt_build_return_some(expr)
                }
                Statement::Abort(_) => {
                    // mk-abort-{name}
                    self.smt_build_abort()
                }
                Statement::For(_, _, _, _, _) => {
                    unreachable!()
                    // let game_inst_name = game_inst.name();
                    // let _game_name = game.name();
                    // let pkg_inst_name = &oracle_ctx.pkg_inst_ctx().pkg_inst().name;
                    // let pkg_name = &oracle_ctx.pkg_inst_ctx().pkg_inst().pkg.name;
                    // let oracle_name = oracle_ctx.oracle_name();
                    // unreachable!("found a for statement in the smt writer stage. \
                    //              this should have been eliminated by now and can't be handled here. \
                    //              game:{game_inst_name}(game_name) pkg:{pkg_inst_name}({pkg_name}) oracle:{oracle_name}", game_inst_name = game_inst_name, pkg_inst_name = pkg_inst_name, pkg_name = pkg_name, oracle_name = oracle_name)
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
                    self.smt_build_invoke(result, &discard_ident, None, args, edge)
                }
                Statement::Assignment(Assignment { pattern, rhs }, _) => {
                    match (pattern, rhs) {
                        (Pattern::Tuple(idents), AssignmentRhs::Expression(expr)) => {
                            self.smt_build_parse(result, idents, expr)
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
                                    result,
                                    ident,
                                    opt_idx.as_ref(),
                                    args,
                                    edge,
                                ),
                                AssignmentRhs::Expression(expr) => {
                                    self.smt_build_assign(result, ident, opt_idx.as_ref(), expr)
                                }
                            }
                        }
                    }
                }
            };
        }
        result
    }

    fn smt_build_innermost(&self, stmt: &Statement) -> SmtExpr {
        match stmt {
            Statement::IfThenElse(ite) => SmtIte {
                cond: &ite.cond,
                then: self.smt_codeblock(ite.then_block.clone()),
                els: self.smt_codeblock(ite.else_block.clone()),
            }
            .into(),
            Statement::Return(None, _) => {
                // (mk-return-{name} statevarname expr)
                self.smt_build_return_none()
            }
            Statement::Return(Some(expr), _) => {
                // (mk-return-{name} statevarname expr)
                self.smt_build_return_some(expr)
            }
            Statement::Abort(_) => {
                // mk-abort-{name}
                self.smt_build_abort()
            }
            _ => unreachable!("found invalid statement at end of oracle: {:#?}", stmt),
        }
    }

    fn smt_build_return_none(&self) -> SmtExpr {
        let new_game_state = self.smt_write_back_state();
        self.smt_construct_return(new_game_state, "mk-empty")
    }

    fn smt_build_return_some(&self, expr: &Expression) -> SmtExpr {
        let new_game_state = self.smt_write_back_state();
        self.smt_construct_return(new_game_state, expr)
    }

    fn smt_build_abort(&self) -> SmtExpr {
        let new_game_state = self.smt_write_back_state();
        let var_game_state = &GameStatePattern;
        let body = self.smt_construct_abort(var_game_state);
        let bindings = vec![(var_game_state.name(), new_game_state)];
        SmtLet { bindings, body }.into()
    }

    fn smt_build_invoke(
        &self,
        body: SmtExpr,
        assignee_ident: &Identifier,
        opt_idx: Option<&Expression>,
        args: &[Expression],
        edge: &Edge,
    ) -> SmtExpr {
        let pkg_inst_ctx = self.pkg_inst_ctx();
        let game_inst_ctx = pkg_inst_ctx.game_inst_ctx();

        let pkg_inst = pkg_inst_ctx.pkg_inst();
        let game_name = game_inst_ctx.game_name();

        let target = &self.game_inst_context.game().pkgs[edge.to()];

        let called_oracle_context = self
            .game_inst_context
            .pkg_inst_ctx_by_name(&target.name)
            .unwrap()
            .oracle_ctx_by_name(&edge.sig().name)
            .unwrap();

        let var_gamestate = &GameStatePattern;
        let var_gameconsts = GameConstsPattern { game_name };

        let updated_pkgstate = pkg_inst_ctx.smt_update_pkgstate_from_locals().unwrap();
        let updated_game_state = game_inst_ctx
            .smt_update_gamestate_pkgstate(var_gamestate, &pkg_inst.name, updated_pkgstate)
            .unwrap();

        let abort_body = self.smt_construct_abort(updated_game_state);

        let let_bindings = vec![(
            var_gamestate.name(),
            called_oracle_context.smt_access_return_state(names::var_ret_name()),
        )];

        let return_value_pattern = ReturnValue::new(self.oracle_return_type());
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

    fn smt_build_assign(
        &self,
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
                then: self.smt_construct_abort(&GameStatePattern),
                els: smtout,
            }
            .into()
        } else {
            smtout
        }
    }

    fn smt_build_sample(
        &self,
        result: SmtExpr,
        ident: &Identifier,
        opt_idx: Option<&Expression>,
        sample_id: Option<usize>,
        ty: &Type,
        sample_name: Option<&String>,
    ) -> SmtExpr {
        let sample_id = sample_id.expect("found a None sample_id");
        let sample_pos = &self.game_inst_context.sample_info().positions[sample_id];
        debug_assert!(sample_name.is_some_and(|name| *name == sample_pos.sample_name));

        let game_inst_name = self.game_inst_context.game_inst_name();

        let gamestate = self.smt_game_state();
        // ctr is the current "i-th sampling for sample id sample_id"
        let ctr = self
            .game_inst_context
            .smt_access_gamestate_rand(gamestate, sample_id)
            .unwrap_or_else(|| {
                let max_known_sample_id = self.game_inst_context.sample_info().count;
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
        let new_gamestate = self
            .game_inst_context
            .smt_increment_gamestate_rand(
                var_gamestate,
                self.game_inst_context.sample_info(),
                sample_id,
            )
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

    fn smt_build_parse(
        &self,
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
}
