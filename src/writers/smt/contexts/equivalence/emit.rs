use std::collections::{BTreeMap, BTreeSet};

use crate::{
    identifier::Identifier,
    theorem::{Claim, ClaimType, RandomnessType},
    types::{CountSpec, Type, TypeKind},
    writers::smt::{
        contexts::{game_defs, EquivalenceContext, GameInstanceContext, GenericOracleContext},
        declare::declare_const,
        exprs::{SmtAnd, SmtAssert, SmtEq2, SmtExpr, SmtForall, SmtImplies, SmtIte, SmtNot},
        names, patterns,
        patterns::{
            const_mapping::GameConstMappingFunction, functions::FunctionPattern,
            oracle_args::GameStateOracleArgPattern, oracle_args::OracleArgPattern,
            oracle_args::UnitOracleArgPattern, theorem_constants::ConstantPattern,
            ReturnIsAbortConst, SmtDefineFun,
        },
        sorts::Sort,
    },
};

impl<'a> EquivalenceContext<'a> {
    pub(crate) fn emit_invariant(&self) -> Vec<SmtExpr> {
        self.invariants.clone()
    }

    pub(crate) fn emit_initial_state_values(&self) -> Vec<SmtExpr> {
        let mut out = Vec::new();

        out.extend(game_defs::emit_game_initial_state_values(
            self.left_game_inst_ctx(),
        ));
        out.extend(game_defs::emit_game_initial_state_values(
            self.right_game_inst_ctx(),
        ));

        out
    }

    pub(crate) fn emit_invariant_start_assert(&self) -> SmtExpr {
        let state_left = self.left_game_inst_ctx().oracle_arg_game_state_pattern();
        let state_right = self.right_game_inst_ctx().oracle_arg_game_state_pattern();

        SmtAssert(SmtNot((
            "invariant",
            state_left.global_const_name(
                self.equivalence.left_name(),
                &patterns::oracle_args::GameStateOracleArgVariant::Initial,
            ),
            state_right.global_const_name(
                self.equivalence.right_name(),
                &patterns::oracle_args::GameStateOracleArgVariant::Initial,
            ),
        )))
        .into()
    }

    pub(crate) fn emit_game_invariant_start_assert(&self, claim: &Claim) -> SmtExpr {
        let gctx = match claim.ty {
            ClaimType::LeftGameInvariant => self.left_game_inst_ctx(),
            ClaimType::RightGameInvariant => self.right_game_inst_ctx(),
            _ => unreachable!(),
        };
        let game_inst_name = gctx.game_inst_name();
        let state = gctx.oracle_arg_game_state_pattern();
        let initial_state = state.global_const_name(
            game_inst_name,
            &patterns::oracle_args::GameStateOracleArgVariant::Initial,
        );
        SmtAssert(SmtNot((claim.name(), initial_state.clone()))).into()
    }

    pub(crate) fn emit_oracle_claim_assert(&self, claim: &Claim, oracle_name: &str) -> SmtExpr {
        let gctx_left = self.left_game_inst_ctx();
        let gctx_right = self.right_game_inst_ctx();

        let octx_left = gctx_left.exported_oracle_ctx_by_name(oracle_name).unwrap();
        let octx_right = gctx_right.exported_oracle_ctx_by_name(oracle_name).unwrap();

        let state_left = octx_left.oracle_arg_game_state_pattern();
        let state_right = octx_right.oracle_arg_game_state_pattern();

        let game_inst_name_left = self.equivalence.left_name();
        let game_inst_name_right = self.equivalence.right_name();

        let game_name_left = gctx_left.game().name();
        let game_name_right = gctx_right.game().name();

        let game_params_left = &gctx_left.game_inst().consts;
        let game_params_right = &gctx_right.game_inst().consts;

        let pkg_name_left = octx_left.pkg_inst_ctx().pkg_name();
        let pkg_name_right = octx_right.pkg_inst_ctx().pkg_name();

        let pkg_params_left = &octx_left.pkg_inst_ctx().pkg_inst().params;
        let pkg_params_right = &octx_right.pkg_inst_ctx().pkg_inst().params;

        let args: Vec<_> = self
            .oracle_sig_by_exported_name(oracle_name)
            .unwrap()
            .args
            .iter()
            .map(|(arg_name, arg_type)| patterns::OracleArgs {
                oracle_name,
                game_name: game_name_left, // left/right doesn't matter as both exist and are asserted to be equal
                arg_name,
                arg_type,
            })
            .collect();

        // find the package instance which is marked as exporting
        // the oracle of this name, both left and right.
        let left_return = patterns::ReturnConst {
            game_inst_name: game_inst_name_left,
            game_name: game_name_left,
            game_params: game_params_left,
            pkg_name: pkg_name_left,
            pkg_params: pkg_params_left,
            oracle_name,
            oracle_import_name: oracle_name,
        };

        let right_return = patterns::ReturnConst {
            game_inst_name: game_inst_name_right,
            game_name: game_name_right,
            game_params: game_params_right,
            pkg_name: pkg_name_right,
            pkg_params: pkg_params_right,
            oracle_name,
            oracle_import_name: oracle_name,
        };

        // this helper builds an smt expression that calls the
        // function with the given name with the old states,
        // return values and the respective arguments.
        // We expect that function to return a boolean, which makes
        // it a relation.
        let build_lemma_call = |name: &str| {
            let call_args: Vec<SmtExpr> = vec![
                state_left.old_global_const_name(game_inst_name_left).into(),
                state_right
                    .old_global_const_name(game_inst_name_right)
                    .into(),
                left_return.name().into(),
                right_return.name().into(),
            ]
            .into_iter()
            .chain(args.into_iter().map(|arg| arg.name().into()))
            .collect();

            let relation = self.relation_pattern(name, oracle_name);
            relation.call(&call_args).unwrap()
        };

        let build_relation_call = |name: &str| -> SmtExpr {
            (
                name,
                &state_left.new_global_const_name(game_inst_name_left, oracle_name.to_string()),
                &state_right.new_global_const_name(game_inst_name_right, oracle_name.to_string()),
            )
                .into()
        };

        let build_invariant_old_call = |name: &str| -> SmtExpr {
            (
                name,
                &state_left.old_global_const_name(game_inst_name_left),
                &state_right.old_global_const_name(game_inst_name_right),
            )
                .into()
        };
        let build_left_invariant_old_call = |name: &str| -> SmtExpr {
            (name, &state_left.old_global_const_name(game_inst_name_left)).into()
        };
        let build_right_invariant_old_call = |name: &str| -> SmtExpr {
            (
                name,
                &state_right.old_global_const_name(game_inst_name_right),
            )
                .into()
        };

        let build_invariant_new_call = |name: &str| -> SmtExpr {
            (
                name,
                &state_left.new_global_const_name(game_inst_name_left, oracle_name.to_string()),
                &state_right.new_global_const_name(game_inst_name_right, oracle_name.to_string()),
            )
                .into()
        };
        let build_left_invariant_new_call = |name: &str| -> SmtExpr {
            (
                name,
                &state_left.new_global_const_name(game_inst_name_left, oracle_name.to_string()),
            )
                .into()
        };
        let build_right_invariant_new_call = |name: &str| -> SmtExpr {
            (
                name,
                &state_right.new_global_const_name(game_inst_name_right, oracle_name.to_string()),
            )
                .into()
        };

        let dep_calls: Vec<_> = claim
            .dependencies()
            .iter()
            .map(|dep_name| {
                let claim_type = ClaimType::guess_from_name(dep_name);
                match claim_type {
                    ClaimType::Lemma => build_lemma_call.clone()(dep_name),
                    ClaimType::Relation => build_relation_call(dep_name),
                    ClaimType::Invariant
                    | ClaimType::LeftGameInvariant
                    | ClaimType::RightGameInvariant => unreachable!(),
                }
            })
            .collect();

        let postcond_call = match claim.ty {
            ClaimType::Lemma => build_lemma_call.clone()(&claim.name),
            ClaimType::Relation => build_relation_call(&claim.name),
            ClaimType::Invariant => build_invariant_new_call(&claim.name),
            ClaimType::LeftGameInvariant => build_left_invariant_new_call(&claim.name),
            ClaimType::RightGameInvariant => build_right_invariant_new_call(&claim.name),
        };

        let randomness_mapping = SmtForall {
            bindings: vec![
                ("randmap-sample-id-left".into(), "SampleId".into()),
                ("randmap-sample-offset-left".into(), Type::integer().into()),
                ("randmap-sample-id-right".into(), "SampleId".into()),
                ("randmap-sample-offset-right".into(), Type::integer().into()),
            ],
            body: (
                "=>",
                (
                    format!("randomness-mapping-{oracle_name}"),
                    "randmap-sample-id-left",
                    "randmap-sample-id-right",
                    "randmap-sample-offset-left",
                    "randmap-sample-offset-right",
                ),
                (
                    "rand-is-eq",
                    "randmap-sample-id-left",
                    "randmap-sample-id-right",
                    "randmap-sample-offset-left",
                    "randmap-sample-offset-right",
                ),
            ),
        };

        let mut dependencies_code: Vec<SmtExpr> = vec![
            randomness_mapping.into(),
            build_invariant_old_call("invariant"),
        ];

        for pkg in &gctx_left.game().pkgs {
            if !pkg.pkg.invariants.is_empty() {
                dependencies_code.push(build_left_invariant_old_call(
                    &names::package_invariant_fn_name(game_inst_name_left, pkg.name()),
                ));
            }
        }
        for pkg in &gctx_right.game().pkgs {
            if !pkg.pkg.invariants.is_empty() {
                dependencies_code.push(build_right_invariant_old_call(
                    &names::package_invariant_fn_name(game_inst_name_right, pkg.name()),
                ));
            }
        }

        if !gctx_left.game().invariants.is_empty() {
            dependencies_code.push(build_left_invariant_old_call(
                &names::game_invariant_fn_name(game_inst_name_left),
            ));
        }
        if !gctx_right.game().invariants.is_empty() {
            dependencies_code.push(build_right_invariant_old_call(
                &names::game_invariant_fn_name(game_inst_name_right),
            ));
        }

        for dep in dep_calls {
            dependencies_code.push(dep)
        }

        crate::writers::smt::exprs::SmtAssert(SmtNot(SmtImplies(
            SmtAnd(dependencies_code),
            postcond_call,
        )))
        .into()
    }

    pub(crate) fn emit_game_definitions(&'a self) -> Vec<SmtExpr> {
        game_defs::emit_game_definitions(self.theorem, &self.game_instances())
    }

    /// The two game instances of this equivalence, paired with their sampling information.
    fn game_instances(&'a self) -> Vec<game_defs::GameInstanceWithSampleInfo<'a>> {
        vec![
            (self.left_game_inst_ctx(), self.sample_info_left()),
            (self.right_game_inst_ctx(), self.sample_info_right()),
        ]
    }

    pub(crate) fn emit_base_declarations(&self) -> Vec<SmtExpr> {
        game_defs::emit_base_declarations(&self.types())
    }

    pub(crate) fn emit_auto_randomness(&self, oracle_name: &str) -> Vec<SmtExpr> {
        match self.equivalence.randomness_by_oracle_name(oracle_name) {
            RandomnessType::Custom => {
                vec![]
            }
            RandomnessType::Simple => {
                let define = SmtDefineFun {
                    is_rec: false,
                    sort: Type::boolean().into(),
                    name: format!("randomness-mapping-{oracle_name}"),
                    body: SmtAnd(vec![
                        SmtEq2 {
                            lhs: "sample-id-0",
                            rhs: "sample-id-1",
                        }
                        .into(),
                        SmtEq2 {
                            lhs: "offset-0",
                            rhs: "0",
                        }
                        .into(),
                        SmtEq2 {
                            lhs: "offset-1",
                            rhs: "0",
                        }
                        .into(),
                    ]),
                    args: vec![
                        (
                            "sample-id-0".to_string(),
                            Sort::Other("SampleId".to_string(), vec![]),
                        ),
                        (
                            "sample-id-1".to_string(),
                            Sort::Other("SampleId".to_string(), vec![]),
                        ),
                        ("offset-0".to_string(), Type::integer().into()),
                        ("offset-1".to_string(), Type::integer().into()),
                    ],
                };
                vec![define.into()]
            }
            RandomnessType::None => {
                let define = SmtDefineFun {
                    is_rec: false,
                    sort: Type::boolean().into(),
                    name: format!("randomness-mapping-{oracle_name}"),
                    body: "false",
                    args: vec![
                        (
                            "sample-id-0".to_string(),
                            Sort::Other("SampleId".to_string(), vec![]),
                        ),
                        (
                            "sample-id-1".to_string(),
                            Sort::Other("SampleId".to_string(), vec![]),
                        ),
                        ("offset-0".to_string(), Type::integer().into()),
                        ("offset-1".to_string(), Type::integer().into()),
                    ],
                };
                vec![define.into()]
            }
        }
    }

    pub(crate) fn emit_theorem_paramfuncs(&'a self) -> Vec<SmtExpr> {
        game_defs::emit_theorem_paramfuncs(self.theorem)
    }

    pub(crate) fn emit_return_value_helpers(
        &'a self,
        oracle_name: &str,
    ) -> impl Iterator<Item = SmtExpr> + 'a {
        let left_gctx = self.left_game_inst_ctx();
        let left_octx = left_gctx.exported_oracle_ctx_by_name(oracle_name).unwrap();
        let left_pctx = left_octx.pkg_inst_ctx();

        let right_gctx = self.right_game_inst_ctx();
        let right_octx = right_gctx.exported_oracle_ctx_by_name(oracle_name).unwrap();
        let right_pctx = right_octx.pkg_inst_ctx();

        let left_return_value = left_octx.return_value_const_pattern(oracle_name);
        let right_return_value = right_octx.return_value_const_pattern(oracle_name);

        let left_is_abort = ReturnIsAbortConst {
            game_inst_name: left_gctx.game_inst().name(),
            pkg_inst_name: left_pctx.pkg_inst_name(),
            oracle_name,
            ty: left_octx.oracle_return_type(),
        };

        let right_is_abort = ReturnIsAbortConst {
            game_inst_name: right_gctx.game_inst().name(),
            pkg_inst_name: right_pctx.pkg_inst_name(),
            oracle_name,
            ty: right_octx.oracle_return_type(),
        };

        let consts: [(_, SmtExpr); 3] = [
            (
                "<equal-aborts>",
                SmtEq2 {
                    lhs: left_is_abort.value(left_return_value.name()),
                    rhs: right_is_abort.value(right_return_value.name()),
                }
                .into(),
            ),
            (
                "<no-aborts>",
                SmtAnd(vec![
                    SmtNot(left_is_abort.value(left_return_value.name())).into(),
                    SmtNot(right_is_abort.value(right_return_value.name())).into(),
                ])
                .into(),
            ),
            (
                "<same-outputs>",
                SmtEq2 {
                    lhs: left_return_value.name(),
                    rhs: right_return_value.name(),
                }
                .into(),
            ),
        ];

        consts
            .into_iter()
            .flat_map(|(name, value)| {
                let declare = declare_const(name, Sort::Bool);
                let constrain = SmtAssert(SmtEq2 {
                    lhs: name,
                    rhs: value,
                });

                [declare, constrain.into()]
            })
            .chain(std::iter::once(
                self.relation_definition_equal_aborts(oracle_name).into(),
            ))
            .chain(std::iter::once(
                self.relation_definition_left_no_abort(oracle_name).into(),
            ))
            .chain(std::iter::once(
                self.relation_definition_right_no_abort(oracle_name).into(),
            ))
            .chain(std::iter::once(
                self.relation_definition_no_abort(oracle_name).into(),
            ))
            .chain(std::iter::once(
                self.relation_definition_same_output(oracle_name).into(),
            ))

        // out
    }

    pub(crate) fn emit_constant_declarations(&self) -> Vec<SmtExpr> {
        /*
         *
         * things being declared here:
         * - nonsplit oracle args
         * - for $game_inst in left, right
         *   - old game state $game_inst
         *   - new game state $game_inst
         *   - randomness counters $game_inst
         *   - randomness values $game_inst
         *   - for oracle in game.non-split-exports
         *     - return $game_inst $oracle
         *   - for oracle in game.split-exports
         *     - partial return $game_inst $oracle
         *     - split oracle args
         *
         * things being constrained here:
         * - for $game_inst in left, right
         *   - rand_ctr_$i = get_rand(game_state, $i)
         *   - rand_val_$i = rand_$game_inst($i, rand_ctr_$i)
         *   - for $oracle in $game_inst.non-split-exports
         *     - return = $oracle(state, args...)
         *     - new_game_state_$game_inst = get-state(return)
         *       - wait, maybe this should only be in the procondition of the claim statements
         *   - for $oracle in $game_inst.non-split-exports
         *     - partial return = $oracle(state, args...)
         *
         * Thoughts on the design of the next iteration of this:
         *
         * What can go wrong here?
         *
         *   Underconstraining
         *
         *     The solver would give us a sat where we expect an unsat and we can
         *     use the model to see which constraint is missing. Until that is done, we can't prove
         *     anything but that is not that big of a deal. So I guess this is an easily debuggable
         *     completeness problem.
         *
         *   Overconstraining
         *
         *     We might add too many constraints, which would lead to the solver
         *     reporting unsat where it should return sat. This would break soundness, in ways that
         *     are not easily debuggable.
         *
         *   I feel like soundness is more important than completeness!
         *
         * What can we do to prevent that? (TODO)
         *
         *   Testing
         *
         *     I suppose the best way to guard against this is to have test cases with theorems
         *     that are expected to not go through and make sure that this is actually the case.
         *
         *   Clear Documentation/Spec
         *
         *     Making explicit the model we have of the system helps both
         *     with catching logic bugs (because in order to vet the logic you can read the docs)
         *     and implementation bugs (because you can compare the implementation against the spec).
         *
         * When do we apply the constraints?
         *
         *   Option A: Immediately after declaring
         *
         *     This doesn't work for e.g. the "new state", as that would be constrained in
         *     contradictory ways. My current heuristic is that if the value is the output of a
         *     function and there are several potential functions that it could be the output of,
         *     then it won't work.
         *
         *       Can we maybe avoid that issue by not "overloading" constants? Use constants as
         *       the output of one particular thing? What are other instances of constants that are
         *       constrained differently depending on the call?
         *
         *         Other instances: I was going to say PartialReturn, but not only by "real" oracle
         *         but also by split oracle, but I don' think that is true since because of the
         *         dispatch function. So maybe it's just Return and PartialReturn, by "real" oracle?
         *
         *         We could avoid that by not having a single "new state" constant, but one per
         *         oracle. That might be a tad inconvenient though? Or we just bind the convenient
         *         names using let, either in the lemma/relation/invariant or in the glue code
         *         calling it. This would mean we don't even need the constants and don't need to
         *         constrain them. Sounds like there is less chance of confusion, too!
         *
         *   Option B: First declare all constants, then constrain
         *
         *     Seems difficult to keep track of the constraints we still need to do.
         *
         * So to me it seems the best way is to
         *
         * 1.  declare foundational constants ("old state", "function arguments")
         * 2.  declare constants that conceptually are outputs of a known function taking
         *     foundational constants ("return per oracle") and immediately constrain them
         * 3.  only bind convenience values in (let ..) blocks close to the code using them.
         *     This can be done manually in the user code, or in the glue code calling the user
         *     code.
         *
         *       I think there is a discussion to be had here, though. If we go with the let-bind
         *       approache, we can't make the randomness mapping a bunch of asserts. It needs to be
         *       an expression that evaluates to a bool. Is the user fine with that?
         *
         *       I think this can affect model readability (for a human) in one of two ways:
         *
         *         Possible Impact A: There a fewer global constants, and all the values are in the
         *         specific part of the gamestate. It is more tidy and it is easy to find what you
         *         are looking for.
         *
         *         Possibe Impact B: Instead of having a global constant rand-Real-1-4 as a constant
         *         in the model, you have to sift through the game state structs to find the
         *         correct one to see the value, which makes it more difficult.
         *
         *         I wonder which of these would be stronger, and believe it depends on the habits and
         *         preferences of the user.
         *
         * Which leaves us to specify (and give reasons for) our list of constants and constraints.
         * Afterwards, we also make a list of constants constraints we chose not to include here.
         *
         *   Foundational Constants: Old Gamestate, Old Intermediate State and Arguments
         *
         *     These are only used as inputs to the oracle functions. There is nothing we can tie
         *     them to, we can only constrain them in lemmas, etc.
         *
         *   Function Outputs: Return, PartialReturn
         *
         *     These can be directly computed from the above. They should simply be constrained.
         *
         *   Convenience Values: New Gamestate, New Intermediate State, IsAbort, Return Value,
         *                       Randomness Counters, Random Values
         *
         *     These fall in two categories:
         *
         *     1.  Values where a convenient name would not be globally unique (e.g. new state, is abort)
         *
         *           Here I think using (let ..) bindings really is the best way to handle the
         *           ambiguity.
         *
         *     2.  Values that have unique names, but are rarely needed and are just copied from the
         *         gamestate (e.g. randomness)
         *
         *           Here I am not sure - From a "purity" standpoint it feels nice to me, but I see how
         *           that is not a very strong argument, so we may just declare and constrain them globally.
         *
         */

        let left_game_inst_name = self.equivalence.left_name();
        let right_game_inst_name = self.equivalence.right_name();

        let left = self
            .theorem
            .find_game_instance(self.equivalence.left_name())
            .unwrap();
        let right = self
            .theorem
            .find_game_instance(self.equivalence.right_name())
            .unwrap();

        let gctx_left = GameInstanceContext::new(left);
        let gctx_right = GameInstanceContext::new(right);

        let left_game_name = &gctx_left.game().name;
        let right_game_name = &gctx_right.game().name;

        let mut out = Vec::new();

        /////// state constants

        let game_state_left = gctx_left.oracle_arg_game_state_pattern();
        let game_state_right = gctx_right.oracle_arg_game_state_pattern();

        // the new ones are declared in the declare-then-assert loop below

        out.push(game_state_left.declare_old(left_game_inst_name));
        //out.push(game_state_left.declare_new(left_game_inst_name));
        out.push(game_state_right.declare_old(right_game_inst_name));
        //out.push(game_state_right.declare_new(right_game_inst_name));

        ////// consts constants

        let game_consts_left = patterns::oracle_args::GameConstsPattern {
            game_name: left_game_name,
        };
        let game_consts_right = patterns::oracle_args::GameConstsPattern {
            game_name: right_game_name,
        };

        let theorem_consts = patterns::oracle_args::TheoremConstsPattern {
            theorem_name: &self.theorem().name,
        };

        // the interface requires us to pass in a game instance name, but for the theorem constants
        // that gets ignored. We use a name here that would for sure cause trouble if it were
        // included.
        let hack_this_should_be_ignored = "this is being ignored anyway, but let's make sure it fails if it gets included )))))))))))))";

        out.push(theorem_consts.unit_declare(hack_this_should_be_ignored));

        let theorem_game_const_mapping_left = GameConstMappingFunction {
            theorem_name: &self.theorem().name,
            game_name: left_game_name,
            game_inst_name: left_game_inst_name,
        };

        let theorem_game_const_mapping_right = GameConstMappingFunction {
            theorem_name: &self.theorem().name,
            game_name: right_game_name,
            game_inst_name: right_game_inst_name,
        };

        let theorem_game_const_mapping_call_left =
            theorem_game_const_mapping_left.call(&[theorem_consts
                .unit_global_const_name(hack_this_should_be_ignored)
                .into()]);
        let theorem_game_const_mapping_call_right =
            theorem_game_const_mapping_right.call(&[theorem_consts
                .unit_global_const_name(hack_this_should_be_ignored)
                .into()]);

        out.push(
            game_consts_left
                .unit_define(
                    left_game_inst_name,
                    theorem_game_const_mapping_call_left.unwrap(),
                )
                .into(),
        );
        out.push(
            game_consts_right
                .unit_define(
                    right_game_inst_name,
                    theorem_game_const_mapping_call_right.unwrap(),
                )
                .into(),
        );

        /////// arguments for non-split and split oracles

        for left_export in &left.game().exports {
            let right_export = right
                .game
                .exports
                .iter()
                .find(|exp| exp.name() == left_export.name())
                .unwrap();
            if let (Some(mut left_orcl_ctx), Some(mut right_orcl_ctx)) = (
                gctx_left.exported_oracle_ctx_by_name(left_export.name()),
                gctx_right.exported_oracle_ctx_by_name(right_export.name()),
            ) {
                left_orcl_ctx.set_renamed(left_export.alias());
                right_orcl_ctx.set_renamed(right_export.alias());
                for ((arg_name_left, arg_type), (arg_name_right, _)) in left_export
                    .sig()
                    .args
                    .iter()
                    .zip(right_export.sig().args.iter())
                {
                    if gctx_left.game_inst().game.name() == gctx_right.game_inst().game.name() {
                        out.push(declare_const(
                            left_orcl_ctx.smt_arg_name(arg_name_left),
                            arg_type.clone().into(),
                        ));
                    } else {
                        out.push(declare_const(
                            left_orcl_ctx.smt_arg_name(arg_name_left),
                            arg_type.clone().into(),
                        ));
                        out.push(declare_const(
                            right_orcl_ctx.smt_arg_name(arg_name_right),
                            arg_type.clone().into(),
                        ));
                        out.push(
                            SmtAssert(SmtEq2 {
                                lhs: left_orcl_ctx.smt_arg_name(arg_name_left),
                                rhs: right_orcl_ctx.smt_arg_name(arg_name_right),
                            })
                            .into(),
                        );
                    }
                }
            }
        }

        ////// return values

        for (decl_ret, constrain) in game_defs::build_returns(left) {
            out.push(decl_ret);
            out.push(constrain);
        }

        for (decl_ret, constrain) in game_defs::build_returns(right) {
            out.push(decl_ret);
            out.push(constrain);
        }

        /////// randomess counters

        for (decl_ctr, assert_ctr, assert_zero_ctr, decl_val, assert_val) in
            game_defs::build_rands(self.sample_info_left(), left)
        {
            out.push(decl_ctr);
            out.push(assert_ctr);
            out.push(assert_zero_ctr);
            out.push(decl_val);
            out.push(assert_val);
        }

        for (decl_ctr, assert_ctr, assert_zero_ctr, decl_val, assert_val) in
            game_defs::build_rands(self.sample_info_right(), right)
        {
            out.push(decl_ctr);
            out.push(assert_ctr);
            out.push(assert_zero_ctr);
            out.push(decl_val);
            out.push(assert_val);
        }

        /////////// helpers for working with randomness

        out.push(game_defs::define_randctr_function(
            left,
            self.sample_info_left(),
        ));
        out.push(game_defs::define_randctr_function(
            right,
            self.sample_info_right(),
        ));
        out.push(self.smt_define_randeq_function());

        out
    }

    pub fn smt_define_randeq_function(&self) -> SmtExpr {
        let left_game_inst = self.left_game_inst_ctx().game_inst();
        let right_game_inst = self.right_game_inst_ctx().game_inst();

        let left_game_inst_name = &left_game_inst.name;
        let right_game_inst_name = &right_game_inst.name;

        /*
         *
         *
         * (= (randfn_left left-id left-ctr) (randfn-right right-id right-ctr)))
         *
         * if ( = left-id 3) (randfn-Int id ctr) else if ( )
         *
         *
         * if (or [cases left is type A and right is type A]) (= (fn left id ctr) fn right id ctr)
         *
         */

        fn type_use_theorem_ident(ty: Type) -> Type {
            match ty.into_kind() {
                TypeKind::Bits(mut count_spec) => {
                    if let CountSpec::Identifier(identifier) = &mut count_spec {
                        let theorem_ident = identifier.as_theorem_identifier();
                        assert!(
                            theorem_ident.is_some(),
                            "expected {identifier:?} to be completely resolved"
                        );
                        **identifier =
                            Identifier::TheoremIdentifier(theorem_ident.cloned().unwrap());
                    }
                    Type::bits(count_spec)
                }
                kind => Type::from_kind(kind),
            }
        }

        let left_positions = &self.sample_info_left().positions;
        let right_positions = &self.sample_info_right().positions;

        let left_types: BTreeSet<Type> = BTreeSet::from_iter(
            self.sample_info_left()
                .tys
                .iter()
                .cloned()
                .map(type_use_theorem_ident),
        );
        let right_types: BTreeSet<Type> = BTreeSet::from_iter(
            self.sample_info_right()
                .tys
                .iter()
                .cloned()
                .map(type_use_theorem_ident),
        );

        let types: Vec<&Type> = left_types.intersection(&right_types).collect();

        let mut left_positions_by_type: BTreeMap<_, Vec<_>> = BTreeMap::new();
        let mut right_positions_by_type: BTreeMap<_, Vec<_>> = BTreeMap::new();

        for pos in left_positions {
            let pos_ty = pos.ty.clone();
            let pos_theorem_ty = type_use_theorem_ident(pos_ty);
            left_positions_by_type
                .entry(pos_theorem_ty)
                .or_default()
                .push(pos);
        }

        for pos in right_positions {
            let pos_ty = pos.ty.clone();
            let pos_theorem_ty = type_use_theorem_ident(pos_ty);
            right_positions_by_type
                .entry(pos_theorem_ty)
                .or_default()
                .push(pos);
        }

        let mut body: SmtExpr = true.into();

        for ty in types {
            let sort: SmtExpr = ty.into();

            let left_has_type = left_positions_by_type
                .get(ty)
                .expect("expected that left sample info has positions for type {ty:?}")
                .iter()
                .map(|sample_pos| ("=", *sample_pos, "sample-id-left").into());
            let mut left_or_case: Vec<SmtExpr> = vec!["or".into()];
            left_or_case.extend(left_has_type);

            let right_has_type = right_positions_by_type
                .get(ty)
                .expect("expected that right sample info has positions for type {ty:?}")
                .iter()
                .map(|sample_pos| ("=", *sample_pos, "sample-id-right").into());

            let mut right_or_case: Vec<SmtExpr> = vec!["or".into()];
            right_or_case.extend(right_has_type);

            body = SmtIte {
                cond: SmtAnd(vec![
                    SmtExpr::List(left_or_case),
                    SmtExpr::List(right_or_case),
                ]),
                then: (
                    "=",
                    (
                        format!("__sample-rand-{left_game_inst_name}-{sort}"),
                        "sample-id-left",
                        "sample-ctr-left",
                    ),
                    (
                        format!("__sample-rand-{right_game_inst_name}-{sort}"),
                        "sample-id-right",
                        "sample-ctr-right",
                    ),
                ),
                els: body,
            }
            .into()
        }

        (
            "define-fun",
            "rand-is-eq",
            (
                ("sample-id-left", "SampleId"),
                ("sample-id-right", "SampleId"),
                ("sample-ctr-left", Type::integer()),
                ("sample-ctr-right", Type::integer()),
            ),
            "Bool",
            body,
        )
            .into()
    }
}
