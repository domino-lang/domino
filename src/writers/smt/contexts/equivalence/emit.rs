use std::{collections::HashSet, fmt::Display};

use crate::{
    gamehops::equivalence::{
        smtrewrite::SmtStatementKind,
        {ClaimType, ResolvedClaim},
    },
    theorem::{RandomnessMappingInjectivityCheck, RandomnessType},
    types::{Type, TypeKind},
    writers::smt::{
        contexts::{emit_base_declarations, unique_by_name, EquivalenceContext},
        declare::declare_const,
        exprs::{SmtAnd, SmtAssert, SmtEq2, SmtExpr, SmtImplies, SmtNot},
        names, patterns,
        patterns::{
            const_mapping::define_game_const_mapping_fun, datastructures::DatastructurePattern,
            declare_datatype, functions::FunctionPattern, oracle_args::GameStateOracleArgPattern,
            oracle_args::OracleArgPattern, oracle_args::UnitOracleArgPattern,
            theorem_constants::ConstantPattern, SmtDefineFun,
        },
        sorts::Sort,
    },
};

impl RandomnessMappingInjectivityCheck {
    /// Emits the smt code that searches for a counterexample to injectivity of the randomness
    /// mapping relation on the given component.
    ///
    /// Injectivity on the left means that no two distinct left sampling
    /// points are related to the same right sampling point (and similarly for the right). We declare
    /// the three sampling points involved as constants, assert that both pairs are in the
    /// relation, and assert that the two points on `component` differ. A sat result is therefore a
    /// counterexample to injectivity, and unsat means the relation is injective on that component.
    ///
    /// The relation may also read the old game states, the oracle arguments and the theorem
    /// constants. Those are declared (and constrained) by the equivalence-wide smt code, so they
    /// stay free here and the check quantifies over them implicitly.
    pub(crate) fn emit_randomness_mapping_injectivity_check(
        self,
        oracle_name: &str,
    ) -> Vec<SmtExpr> {
        // the two sampling points on the component we check injectivity on
        const FIRST_ID: &str = "<injective-randmap-first-id>";
        const FIRST_CTR: &str = "<injective-randmap-first-ctr>";
        const SECOND_ID: &str = "<injective-randmap-second-id>";
        const SECOND_CTR: &str = "<injective-randmap-second-ctr>";
        // the sampling point on the other component that both are related to
        const SHARED_ID: &str = "<injective-randmap-shared-id>";
        const SHARED_CTR: &str = "<injective-randmap-shared-ctr>";

        let sample_id_sort = || Sort::Other("SampleId".to_string(), vec![]);

        let relation_call = |id: &str, ctr: &str| -> SmtExpr {
            let (id_left, id_right, ctr_left, ctr_right) = match self {
                Self::Left => (id, SHARED_ID, ctr, SHARED_CTR),
                Self::Right => (SHARED_ID, id, SHARED_CTR, ctr),
            };

            (
                format!("randomness-mapping-{oracle_name}"),
                id_left,
                id_right,
                ctr_left,
                ctr_right,
            )
                .into()
        };

        vec![
            declare_const(FIRST_ID, sample_id_sort()),
            declare_const(FIRST_CTR, Sort::Int),
            declare_const(SECOND_ID, sample_id_sort()),
            declare_const(SECOND_CTR, Sort::Int),
            declare_const(SHARED_ID, sample_id_sort()),
            declare_const(SHARED_CTR, Sort::Int),
            // R(first_id, shared_id, first_ctr, shared_ctr)
            SmtAssert(relation_call(FIRST_ID, FIRST_CTR)).into(),
            // R(second_id, shared_id, second_ctr, shared_ctr)
            SmtAssert(relation_call(SECOND_ID, SECOND_CTR)).into(),
            // (first_id, first_ctr) != (second_id, second_ctr)
            SmtAssert(SmtNot(SmtAnd(vec![
                SmtEq2 {
                    lhs: FIRST_ID,
                    rhs: SECOND_ID,
                }
                .into(),
                SmtEq2 {
                    lhs: FIRST_CTR,
                    rhs: SECOND_CTR,
                }
                .into(),
            ])))
            .into(),
        ]
    }
}

pub(crate) const RANDOMNESS_MAPPING_CONDITION_NAME: &str = "<randomness-mapping>";

#[derive(Clone, Debug)]
pub(crate) struct RandomnessMappingEntry {
    pub(crate) sample_id_left: SmtExpr,
    pub(crate) sample_id_right: SmtExpr,
    pub(crate) offset_left: usize,
    pub(crate) offset_right: usize,
    // the sampling type shared by both sides (guaranteed identical by `types_match`), used to
    // pick the concrete `__sample-rand-*` functions to compare directly.
    pub(crate) ty: Type,
}

impl Display for RandomnessMappingEntry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "left id: {}, right id: {}, left offset: {}, right offset: {}, ty: {:?}",
            self.sample_id_left, self.sample_id_right, self.offset_left, self.offset_right, self.ty
        )
    }
}

impl<'a> EquivalenceContext<'a> {
    pub(crate) fn emit_invariant(&self) -> Vec<SmtExpr> {
        self.invariants
            .iter()
            .chain(self.left_invariants.iter())
            .chain(self.right_invariants.iter())
            .map(|stmt| stmt.expr.clone())
            .collect()
    }

    pub(crate) fn emit_initial_state_values(&self) -> Vec<SmtExpr> {
        let mut out = Vec::new();

        out.extend(self.left_game_inst_ctx().emit_game_initial_state_values());
        out.extend(self.right_game_inst_ctx().emit_game_initial_state_values());

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

    pub(crate) fn emit_game_or_package_invariant_start_assert(
        &self,
        claim: &ResolvedClaim,
    ) -> SmtExpr {
        let gctx = match claim.ty {
            ClaimType::LeftGameInvariant | ClaimType::LeftPackageInvariant => {
                self.left_game_inst_ctx()
            }
            ClaimType::RightGameInvariant | ClaimType::RightPackageInvariant => {
                self.right_game_inst_ctx()
            }
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

    pub(crate) fn emit_oracle_claim_assert(
        &self,
        claim: &ResolvedClaim,
        oracle_name: &str,
    ) -> SmtExpr {
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
            .map(|dep| match dep.ty {
                ClaimType::Lemma => build_lemma_call.clone()(&dep.name),
                ClaimType::Relation => build_relation_call(&dep.name),
                ClaimType::LeftPackageInvariant
                | ClaimType::RightPackageInvariant
                | ClaimType::LeftGameInvariant
                | ClaimType::RightGameInvariant => {
                    unreachable!("Not a valid dependency: {} - {:?}", dep.name, dep.ty)
                }
            })
            .collect();

        let postcond_call = match claim.ty {
            ClaimType::Lemma => build_lemma_call.clone()(&claim.name),
            ClaimType::Relation => build_relation_call(&claim.name),
            ClaimType::LeftPackageInvariant => build_left_invariant_new_call(&claim.name),
            ClaimType::RightPackageInvariant => build_right_invariant_new_call(&claim.name),
            ClaimType::LeftGameInvariant => build_left_invariant_new_call(&claim.name),
            ClaimType::RightGameInvariant => build_right_invariant_new_call(&claim.name),
        };

        let mut dependencies_code: Vec<SmtExpr> = vec![
            RANDOMNESS_MAPPING_CONDITION_NAME.into(),
            build_invariant_old_call("invariant"),
        ];

        dependencies_code.extend(
            self.left_invariants
                .iter()
                .filter_map(|stmt| match stmt.kind {
                    SmtStatementKind::GameInvariant { .. }
                    | SmtStatementKind::PackageInvariant { .. } => {
                        Some(build_left_invariant_old_call(&stmt.kind.name()))
                    }
                    _ => None,
                }),
        );
        dependencies_code.extend(
            self.right_invariants
                .iter()
                .filter_map(|stmt| match stmt.kind {
                    SmtStatementKind::GameInvariant { .. }
                    | SmtStatementKind::PackageInvariant { .. } => {
                        Some(build_right_invariant_old_call(&stmt.kind.name()))
                    }
                    _ => None,
                }),
        );

        for dep in dep_calls {
            dependencies_code.push(dep)
        }

        crate::writers::smt::exprs::SmtAssert(SmtNot(SmtImplies(
            SmtAnd(dependencies_code),
            postcond_call,
        )))
        .into()
    }

    fn randomness_mapping_candidates(&self, oracle_name: &str) -> Vec<RandomnessMappingEntry> {
        let left_export = self
            .left_game_inst_ctx()
            .game()
            .exports
            .iter()
            .find(|export| export.name() == oracle_name)
            .unwrap_or_else(|| unreachable!("oracle resolution should have caught this: could not find left export {oracle_name}"));
        let right_export = self
            .right_game_inst_ctx()
            .game()
            .exports
            .iter()
            .find(|export| export.name() == oracle_name)
            .unwrap_or_else(|| unreachable!("oracle resolution should have caught this: could not find right export {oracle_name}"));

        let left_offsets = self
            .max_offsets_left()
            .get(left_export)
            .unwrap_or_else(|| unreachable!("sample_max_counter_extractor should have filled this: could not find max offsets for left export {oracle_name}"));
        let right_offsets = self
            .max_offsets_right()
            .get(right_export)
            .unwrap_or_else(|| unreachable!("sample_max_counter_extractor should have filled this: could not find max offsets for right export {oracle_name}"));

        let mut left_entries: Vec<_> = left_offsets
            .iter()
            .flat_map(|(position, max_offset)| {
                (0..*max_offset)
                    .map(move |offset| (position, SmtExpr::from(position), offset, &position.ty))
            })
            .collect();
        let mut right_entries: Vec<_> = right_offsets
            .iter()
            .flat_map(|(position, max_offset)| {
                (0..*max_offset)
                    .map(move |offset| (position, SmtExpr::from(position), offset, &position.ty))
            })
            .collect();

        left_entries.sort_by_key(|(position, _, offset, _)| (position.sample_id, *offset));
        right_entries.sort_by_key(|(position, _, offset, _)| (position.sample_id, *offset));

        left_entries
            .iter()
            .flat_map(|(_left_position, sample_id_left, offset_left, ty_left)| {
                right_entries
                    .iter()
                    .filter(move |(_, _, _, ty_right)| ty_left.types_match(ty_right))
                    .map(
                        move |(_, sample_id_right, offset_right, _)| RandomnessMappingEntry {
                            sample_id_left: sample_id_left.clone(),
                            sample_id_right: sample_id_right.clone(),
                            offset_left: *offset_left,
                            offset_right: *offset_right,
                            // `types_match` guarantees left and right resolve to the same SMT
                            // sort, so either type can be used to pick the `__sample-rand-*`
                            // functions for both sides.
                            ty: (*ty_left).clone(),
                        },
                    )
            })
            .collect()
    }

    pub(crate) fn emit_randomness_mapping_condition(&self, oracle_name: &str) -> Vec<SmtExpr> {
        let left_game_inst_name = self.left_game_inst_ctx().game_inst().name();
        let right_game_inst_name = self.right_game_inst_ctx().game_inst().name();

        let conjuncts: Vec<SmtExpr> = self
            .randomness_mapping_candidates(oracle_name)
            .iter()
            .map(|entry| {
                let left_rand_fn = names::fn_sample_rand_name(left_game_inst_name, &entry.ty);
                let right_rand_fn = names::fn_sample_rand_name(right_game_inst_name, &entry.ty);

                SmtImplies(
                    (
                        format!("randomness-mapping-{oracle_name}"),
                        entry.sample_id_left.clone(),
                        entry.sample_id_right.clone(),
                        entry.offset_left,
                        entry.offset_right,
                    ),
                    SmtEq2 {
                        lhs: (
                            left_rand_fn,
                            entry.sample_id_left.clone(),
                            entry.offset_left,
                        ),
                        rhs: (
                            right_rand_fn,
                            entry.sample_id_right.clone(),
                            entry.offset_right,
                        ),
                    },
                )
                .into()
            })
            .collect();

        let rhs: SmtExpr = if conjuncts.is_empty() {
            true.into()
        } else {
            SmtAnd(conjuncts).into()
        };

        vec![
            declare_const(RANDOMNESS_MAPPING_CONDITION_NAME, Type::boolean().into()),
            SmtAssert(SmtEq2 {
                lhs: RANDOMNESS_MAPPING_CONDITION_NAME,
                rhs,
            })
            .into(),
        ]
    }

    pub(crate) fn emit_game_definitions(&'a self) -> impl Iterator<Item = SmtExpr> + 'a {
        let mut left_writer = self.left_game_inst_ctx();
        let mut right_writer = self.right_game_inst_ctx();

        left_writer
            .smt_composition_randomness()
            .chain(right_writer.smt_composition_randomness())
            .chain(self.smt_package_const_definitions())
            .chain(self.smt_package_state_definitions())
            .chain(self.smt_theorem_const_definition())
            .chain(self.smt_game_const_definitions())
            .chain(self.smt_game_state_definitions())
            .chain(self.smt_theorem_game_const_mapping_definitions())
            .chain(self.smt_game_pkg_const_mapping_definitions())
            .chain(self.smt_package_return_definitions())
            .chain(self.smt_oracle_function_definitions())
    }

    pub(crate) fn emit_base_declarations(&self) -> Vec<SmtExpr> {
        emit_base_declarations(self.types())
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

    pub(crate) fn emit_theorem_paramfuncs(&'a self) -> impl Iterator<Item = SmtExpr> + 'a {
        fn get_fn<T: Clone>(arg: &(T, Type)) -> Option<(T, Vec<Type>, Type)> {
            let (other, ty) = arg;
            match ty.kind() {
                TypeKind::Fn(args, ret) => Some((other.clone(), args.to_vec(), *ret.clone())),
                _ => None,
            }
        }

        let imported_fns = self
            .left_game_inst_ctx()
            .game_inst()
            .consts
            .iter()
            .chain(self.right_game_inst_ctx().game_inst().consts.iter())
            .filter_map(|(ident, _expr)| {
                if matches!(ident.ty.kind(), TypeKind::Fn(_, _)) {
                    if let Some(val) = &ident.assigned_value {
                        val.as_identifier().map(|ident| ident.ident())
                    } else {
                        None
                    }
                } else {
                    None
                }
            })
            .collect::<HashSet<_>>();

        self.theorem.consts.iter().filter_map(get_fn).filter_map(
            move |(func_name, arg_types, ret_type)| {
                if imported_fns.contains(&func_name) {
                    let arg_types: SmtExpr = arg_types
                        .into_iter()
                        .map(|ty| ty.into())
                        .collect::<Vec<SmtExpr>>()
                        .into();

                    Some(
                        (
                            "declare-fun",
                            format!("<<func-{func_name}>>"),
                            arg_types,
                            ret_type,
                        )
                            .into(),
                    )
                } else {
                    None
                }
            },
        )
    }

    pub(crate) fn emit_return_value_helpers(&self, oracle_name: &str) -> Vec<SmtExpr> {
        std::iter::once(self.relation_definition_equal_aborts(oracle_name).into())
            .chain(std::iter::once(
                self.relation_definition_no_abort(oracle_name).into(),
            ))
            .chain(std::iter::once(
                self.relation_definition_same_output(oracle_name).into(),
            ))
            .collect()
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

        let left = self
            .theorem
            .find_game_instance(self.equivalence.left_name())
            .unwrap();
        let right = self
            .theorem
            .find_game_instance(self.equivalence.right_name())
            .unwrap();

        let gctx_left = self.left_game_inst_ctx();
        let gctx_right = self.right_game_inst_ctx();

        let mut out = Vec::new();

        ////// consts constants

        let theorem_consts = patterns::oracle_args::TheoremConstsPattern {
            theorem_name: &self.theorem().name,
        };

        // the interface requires us to pass in a game instance name, but for the theorem constants
        // that gets ignored. We use a name here that would for sure cause trouble if it were
        // included.
        let hack_this_should_be_ignored = "this is being ignored anyway, but let's make sure it fails if it gets included )))))))))))))";

        out.push(theorem_consts.unit_declare(hack_this_should_be_ignored));

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

        out.extend(gctx_left.emit_constant_declarations(&self.theorem().name));
        out.extend(gctx_right.emit_constant_declarations(&self.theorem().name));

        out
    }

    /// Returns an iterator of all the package const datatypes that need to be defined for this
    /// equivalence theorem. It makes sure to skip duplicate definitions, which may occur if a
    /// package is used more than once.
    pub(crate) fn smt_package_const_definitions(&'a self) -> impl Iterator<Item = SmtExpr> + 'a {
        unique_by_name(
            self.left_game_inst_ctx()
                .named_smt_package_const_definitions()
                .chain(
                    self.right_game_inst_ctx()
                        .named_smt_package_const_definitions(),
                ),
        )
    }

    /// Returns an iterator of all the package state datatypes that need to be defined for this
    /// equivalence theorem. It makes sure to skip duplicate definitions, which may occur if a
    /// package is used more than once.
    pub(crate) fn smt_package_state_definitions(&'a self) -> impl Iterator<Item = SmtExpr> + 'a {
        unique_by_name(
            self.left_game_inst_ctx()
                .named_smt_package_state_definitions()
                .chain(
                    self.right_game_inst_ctx()
                        .named_smt_package_state_definitions(),
                ),
        )
    }

    /// Returns an iterator of all the package state datatypes that need to be defined for this
    /// equivalence theorem. It makes sure to skip duplicate definitions, which may occur if a
    /// package is used more than once.
    pub(crate) fn smt_package_return_definitions(&'a self) -> impl Iterator<Item = SmtExpr> + 'a {
        unique_by_name(
            self.left_game_inst_ctx()
                .named_smt_package_return_definitions()
                .chain(
                    self.right_game_inst_ctx()
                        .named_smt_package_return_definitions(),
                ),
        )
    }

    /// Returns an iterator of all the game state datatypes that need to be defined for this
    /// equivalence theorem. It makes sure to skip duplicate definitions, which may occur if a
    /// package is used more than once.
    pub(crate) fn smt_game_state_definitions(&'a self) -> impl Iterator<Item = SmtExpr> + 'a {
        unique_by_name([
            self.left_game_inst_ctx().named_smt_game_state_definition(),
            self.right_game_inst_ctx().named_smt_game_state_definition(),
        ])
    }

    /// Returns an iterator cntaining the theorem const datatype.
    pub(crate) fn smt_theorem_const_definition(&'a self) -> impl Iterator<Item = SmtExpr> + 'a {
        let pattern = self.datastructure_theorem_consts_pattern();
        let spec = pattern.datastructure_spec(self.theorem());

        Some(declare_datatype(&pattern, &spec)).into_iter()
    }

    /// Returns an iterator of all the game const datatypes that need to be defined for this
    /// equivalence theorem. It makes sure to skip duplicate definitions, which may occur if a
    /// package is used more than once.
    pub(crate) fn smt_game_const_definitions(&'a self) -> impl Iterator<Item = SmtExpr> + 'a {
        unique_by_name([
            self.left_game_inst_ctx().named_smt_game_const_definition(),
            self.right_game_inst_ctx().named_smt_game_const_definition(),
        ])
    }

    /// Returns an iterator over the functions that map the constant values of the theorem to that of a
    /// game instance. Ranges over all game instances.
    pub(crate) fn smt_theorem_game_const_mapping_definitions(
        &'a self,
    ) -> impl Iterator<Item = SmtExpr> + 'a {
        Some(self)
            .into_iter()
            .flat_map(move |ectx| {
                vec![
                    ectx.left_game_inst_ctx().game_inst(),
                    ectx.right_game_inst_ctx().game_inst(),
                ]
                .into_iter()
            })
            .flat_map(move |game_inst| {
                define_game_const_mapping_fun(self.theorem(), game_inst.game(), game_inst.name())
                    .map(SmtExpr::from)
            })
    }

    /// Returns an iterator over the functions that map the constant values of a game to that of a
    /// package instance. Ranges over all package instances in all games.
    pub(crate) fn smt_game_pkg_const_mapping_definitions(
        &'a self,
    ) -> impl Iterator<Item = SmtExpr> + 'a {
        let mut seen_game_names: HashSet<&str> = Default::default();

        Some(self)
            .into_iter()
            .flat_map(move |ectx| {
                vec![ectx.left_game_inst_ctx(), ectx.right_game_inst_ctx()].into_iter()
            })
            .filter(move |gctx| seen_game_names.insert(gctx.game_name()))
            .flat_map(|gctx| gctx.smt_game_pkg_const_mapping_definitions())
    }

    pub(crate) fn smt_oracle_function_definitions(&'a self) -> impl Iterator<Item = SmtExpr> + 'a {
        unique_by_name(
            self.left_game_inst_ctx()
                .named_smt_oracle_function_definitions()
                .chain(
                    self.right_game_inst_ctx()
                        .named_smt_oracle_function_definitions(),
                ),
        )
    }
}
