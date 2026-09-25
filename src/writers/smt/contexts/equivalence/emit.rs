use std::{
    collections::{BTreeSet, HashSet},
    fmt::Display,
};

use crate::{
    gamehops::equivalence::smtrewrite::SmtStatementKind,
    hacks,
    theorem::{Claim, ClaimType, GameInstance, RandomnessMappingInjectivityCheck, RandomnessType},
    transforms::samplify::SampleInfo,
    types::{Type, TypeKind},
    writers::smt::{
        contexts::{EquivalenceContext, GameInstanceContext, GenericOracleContext},
        declare::declare_const,
        exprs::{SmtAnd, SmtAssert, SmtEq2, SmtExpr, SmtImplies, SmtNot},
        names, patterns,
        patterns::{
            const_mapping::GameConstMappingFunction,
            const_mapping::{define_game_const_mapping_fun, define_pkg_const_mapping_fun},
            datastructures::DatastructurePattern,
            declare_datatype,
            functions::FunctionPattern,
            oracle_args::GameStateOracleArgPattern,
            oracle_args::OracleArgPattern,
            oracle_args::UnitOracleArgPattern,
            theorem_constants::ConstantPattern,
            GameStateDeclareInfo, ReturnIsAbortConst, SmtDefineFun,
        },
        sorts::Sort,
        writer::CompositionSmtWriter,
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
    /// Index of the left sampling in its game instance's `SampleInfo::positions`.
    pub(crate) sample_left: usize,
    /// Likewise for the right sampling.
    pub(crate) sample_right: usize,
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
            .map(|stmt| stmt.expr.clone())
            .collect()
    }

    pub(crate) fn emit_initial_state_values(&self) -> Vec<SmtExpr> {
        let mut out = Vec::new();

        out.extend(self.emit_game_initial_state_values(self.left_game_inst_ctx()));
        out.extend(self.emit_game_initial_state_values(self.right_game_inst_ctx()));

        out
    }

    fn emit_game_initial_state_values(&self, gctx: GameInstanceContext<'a>) -> Vec<SmtExpr> {
        let game_inst_name = gctx.game_inst_name();
        let initial_state = gctx.oracle_arg_game_state_pattern().global_const_name(
            game_inst_name,
            &patterns::oracle_args::GameStateOracleArgVariant::Initial,
        );

        let mut out = Vec::new();
        out.push(
            gctx.oracle_arg_game_state_pattern()
                .declare_initial(game_inst_name),
        );

        for pctx in gctx.pkg_inst_contexts() {
            let pkg_state = gctx
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

    pub(crate) fn emit_game_or_package_invariant_start_assert(&self, claim: &Claim) -> SmtExpr {
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

    /// The claim's assumptions (each an SMT *term*, not an assert) and its goal term.
    ///
    /// `emit_oracle_claim_assert` combines them into the single refutation
    /// `(assert (not (=> (and <deps>) <goal>)))` that `prove` fires one `check-sat` on.
    /// The debugger instead asserts the assumptions positively and up front (via
    /// [`emit_claim_assumptions`](Self::emit_claim_assumptions)) so they constrain the
    /// branch-reachability queries it makes while walking the execution tree, and only adds
    /// the negated goal (via [`emit_claim_goal_negated`](Self::emit_claim_goal_negated)) at a
    /// terminal pair. `assert(d1) … assert(dn)` plus `assert(not goal)` is equisatisfiable
    /// with the single combined refutation.
    pub(crate) fn claim_assumptions_and_goal(
        &self,
        claim: &Claim,
        oracle_name: &str,
    ) -> (Vec<SmtExpr>, SmtExpr) {
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
                    | ClaimType::LeftPackageInvariant
                    | ClaimType::RightPackageInvariant
                    | ClaimType::LeftGameInvariant
                    | ClaimType::RightGameInvariant => unreachable!(),
                }
            })
            .collect();

        let postcond_call = match claim.ty {
            ClaimType::Lemma => build_lemma_call.clone()(&claim.name),
            ClaimType::Relation => build_relation_call(&claim.name),
            ClaimType::Invariant => build_invariant_new_call(&claim.name),
            ClaimType::LeftPackageInvariant => build_left_invariant_new_call(&claim.name),
            ClaimType::RightPackageInvariant => build_right_invariant_new_call(&claim.name),
            ClaimType::LeftGameInvariant => build_left_invariant_new_call(&claim.name),
            ClaimType::RightGameInvariant => build_right_invariant_new_call(&claim.name),
        };

        let mut dependencies_code: Vec<SmtExpr> = vec![
            RANDOMNESS_MAPPING_CONDITION_NAME.into(),
            build_invariant_old_call("invariant"),
        ];

        for pkg in &gctx_left.game().pkgs {
            if !pkg.pkg.invariants.is_empty() {
                dependencies_code.push(build_left_invariant_old_call(&format!(
                    "package-invariant!{}-{}!",
                    game_inst_name_left,
                    pkg.name()
                )));
            }
        }
        for pkg in &gctx_right.game().pkgs {
            if !pkg.pkg.invariants.is_empty() {
                dependencies_code.push(build_right_invariant_old_call(&format!(
                    "package-invariant!{}-{}!",
                    game_inst_name_right,
                    pkg.name()
                )));
            }
        }

        if !gctx_left.game().invariants.is_empty() {
            dependencies_code.push(build_left_invariant_old_call(&format!(
                "game-invariant!{}!",
                game_inst_name_left,
            )));
        }
        if !gctx_right.game().invariants.is_empty() {
            dependencies_code.push(build_right_invariant_old_call(&format!(
                "game-invariant!{}!",
                game_inst_name_right,
            )));
        }

        for dep in dep_calls {
            dependencies_code.push(dep)
        }

        (dependencies_code, postcond_call)
    }

    /// The single-refutation claim assertion `prove` uses:
    /// `(assert (not (=> (and <deps>) <goal>)))`.
    pub(crate) fn emit_oracle_claim_assert(&self, claim: &Claim, oracle_name: &str) -> SmtExpr {
        let (deps, goal) = self.claim_assumptions_and_goal(claim, oracle_name);
        crate::writers::smt::exprs::SmtAssert(SmtNot(SmtImplies(SmtAnd(deps), goal))).into()
    }

    /// One `(assert <dep>)` per assumption, in the same order
    /// [`claim_assumptions_and_goal`](Self::claim_assumptions_and_goal) returns them. The
    /// debugger asserts these up front so they constrain intermediate reachability queries.
    ///
    /// `emit_claim_assumptions(..)` followed by `emit_claim_goal_negated(..)` is
    /// equisatisfiable with the single `(assert (not (=> (and d1..dn) goal)))` that
    /// [`emit_oracle_claim_assert`](Self::emit_oracle_claim_assert) produces.
    // Consumed by `domino debug` (story 06); no non-test caller on this branch yet.
    #[allow(dead_code)]
    pub(crate) fn emit_claim_assumptions(&self, claim: &Claim, oracle_name: &str) -> Vec<SmtExpr> {
        let (deps, _goal) = self.claim_assumptions_and_goal(claim, oracle_name);
        deps.into_iter()
            .map(|dep| crate::writers::smt::exprs::SmtAssert(dep).into())
            .collect()
    }

    /// `(assert (not <goal>))` — the refutation the debugger checks at a terminal pair,
    /// once the assumptions from [`emit_claim_assumptions`](Self::emit_claim_assumptions)
    /// are already on the stack.
    // Consumed by `domino debug` (story 06); no non-test caller on this branch yet.
    #[allow(dead_code)]
    pub(crate) fn emit_claim_goal_negated(&self, claim: &Claim, oracle_name: &str) -> SmtExpr {
        let (_deps, goal) = self.claim_assumptions_and_goal(claim, oracle_name);
        crate::writers::smt::exprs::SmtAssert(SmtNot(goal)).into()
    }

    /// The generated package- and game-invariant claims for this equivalence, i.e. the claims
    /// that are not written by the user but derived from the presence of `invariant:` files on
    /// the packages and games.
    ///
    /// Lifted out of `EquivalenceSmtDriver` so `domino debug` (story 06) can enumerate the same
    /// claim set the prover checks without duplicating the logic.
    pub(crate) fn generate_game_or_package_invariant_claims(&self) -> Vec<Claim> {
        fn package_invariant_claims(
            gctx: GameInstanceContext<'_>,
            claim_type: ClaimType,
        ) -> Vec<Claim> {
            gctx.game()
                .pkgs
                .iter()
                .filter_map(|pkg| {
                    if pkg.pkg.invariants.is_empty() {
                        None
                    } else {
                        Some(Claim {
                            admitted: false,
                            dependencies: vec!["no-abort".to_string()],
                            ty: claim_type,
                            name: format!(
                                "package-invariant!{}-{}!",
                                gctx.game_inst_name(),
                                pkg.name()
                            ),
                        })
                    }
                })
                .collect()
        }

        fn game_invariant_claim(
            gctx: GameInstanceContext<'_>,
            claim_type: ClaimType,
        ) -> Option<Claim> {
            if gctx.game().invariants.is_empty() {
                None
            } else {
                Some(Claim {
                    admitted: false,
                    dependencies: vec!["no-abort".to_string()],
                    ty: claim_type,
                    name: format!("game-invariant!{}!", gctx.game_inst_name()),
                })
            }
        }

        let mut claims = vec![];
        claims.extend(package_invariant_claims(
            self.left_game_inst_ctx(),
            ClaimType::LeftPackageInvariant,
        ));
        claims.extend(package_invariant_claims(
            self.right_game_inst_ctx(),
            ClaimType::RightPackageInvariant,
        ));
        if let Some(claim) =
            game_invariant_claim(self.left_game_inst_ctx(), ClaimType::LeftGameInvariant)
        {
            claims.push(claim);
        }
        if let Some(claim) =
            game_invariant_claim(self.right_game_inst_ctx(), ClaimType::RightGameInvariant)
        {
            claims.push(claim);
        }
        claims
    }

    pub(crate) fn randomness_mapping_candidates(&self, oracle_name: &str) -> Vec<RandomnessMappingEntry> {
        let left_export = self
            .left_game_inst_ctx()
            .game()
            .exports
            .iter()
            .find(|export| export.name() == oracle_name)
            .unwrap_or_else(|| panic!("could not find left export {oracle_name}"));
        let right_export = self
            .right_game_inst_ctx()
            .game()
            .exports
            .iter()
            .find(|export| export.name() == oracle_name)
            .unwrap_or_else(|| panic!("could not find right export {oracle_name}"));

        let left_offsets = self
            .max_offsets_left()
            .get(left_export)
            .unwrap_or_else(|| panic!("could not find max offsets for left export {oracle_name}"));
        let right_offsets = self
            .max_offsets_right()
            .get(right_export)
            .unwrap_or_else(|| panic!("could not find max offsets for right export {oracle_name}"));

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
            .flat_map(|(left_position, sample_id_left, offset_left, ty_left)| {
                right_entries
                    .iter()
                    .filter(move |(_, _, _, ty_right)| ty_left.types_match(ty_right))
                    .map(
                        move |(right_position, sample_id_right, offset_right, _)| RandomnessMappingEntry {
                            sample_left: left_position.sample_id,
                            sample_right: right_position.sample_id,
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

    /// The condition `randomness-mapping-<O>` states for one candidate: that the
    /// mapping pairs the left draw with the right one. It is a term over the
    /// global constants, so it may depend on the state and the oracle's
    /// arguments; the debugger asks the solver, it never reads it.
    pub(crate) fn randomness_mapping_premise(
        &self,
        oracle_name: &str,
        entry: &RandomnessMappingEntry,
    ) -> SmtExpr {
        (
            format!("randomness-mapping-{oracle_name}"),
            entry.sample_id_left.clone(),
            entry.sample_id_right.clone(),
            entry.offset_left,
            entry.offset_right,
        )
            .into()
    }

    /// The names of the equivalence's `define-state-relation`s, in file order.
    /// These are exactly the relations the EasyCrypt `inv` operator conjoins
    /// (`writers::easycrypt::invariant`), each defined here as an SMT function
    /// of the two game states.
    pub(crate) fn state_relation_names(&self) -> Vec<String> {
        self.invariants
            .iter()
            .filter(|stmt| matches!(stmt.sort, SmtStatementKind::StateRelation))
            .filter_map(|stmt| match &stmt.expr {
                SmtExpr::List(items) => match items.as_slice() {
                    [SmtExpr::Atom(kw), SmtExpr::Atom(name), ..] if kw == "define-fun" => {
                        Some(name.clone())
                    }
                    _ => None,
                },
                _ => None,
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
                    self.randomness_mapping_premise(oracle_name, entry),
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
        let left = self
            .theorem
            .find_game_instance(self.equivalence.left_name())
            .unwrap();
        let right = self
            .theorem
            .find_game_instance(self.equivalence.right_name())
            .unwrap();

        let mut left_writer = CompositionSmtWriter::new(left, self.sample_info_left());
        let mut right_writer = CompositionSmtWriter::new(right, self.sample_info_right());

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
        let mut base_declarations: Vec<SmtExpr> = vec![("set-logic", "ALL").into()];

        let mut bits_sort_suffixes = HashSet::new();

        for ty in self.types() {
            if let TypeKind::Bits(count_spec) = &ty.kind() {
                let bits_sort_suffix = count_spec.resolved_suffix();

                log::debug!("found {bits_sort_suffix}");

                // ensure we don't write more than once. Earlier we also dedupe, but we dedupe
                // identifiers, which contain more info than just the name.
                if bits_sort_suffixes.insert(bits_sort_suffix.clone()) {
                    base_declarations.extend(hacks::BitsDeclaration(bits_sort_suffix));
                }
            }
        }

        base_declarations.extend(hacks::MaybeDeclaration);
        base_declarations.push(hacks::ReturnValueDeclaration.into());
        base_declarations.extend(hacks::TuplesDeclaration(1..32));
        base_declarations.extend(hacks::EmptyDeclaration);
        base_declarations.push(hacks::SampleIdDeclaration.into());

        base_declarations
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

        self.theorem
            .consts
            .iter()
            .filter_map(get_fn)
            .map(|(func_name, arg_types, ret_type)| {
                let arg_types: SmtExpr = arg_types
                    .into_iter()
                    .map(|ty| ty.into())
                    .collect::<Vec<SmtExpr>>()
                    .into();

                (
                    "declare-fun",
                    format!("<<func-{func_name}>>"),
                    arg_types,
                    ret_type,
                )
                    .into()
            })
    }

    pub(crate) fn emit_return_value_helpers(&self, oracle_name: &str) -> Vec<SmtExpr> {
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
            .collect()

        // out
    }

    /// Declares (and mostly constrains) the base constants for the equivalence check.
    ///
    /// `skip_return_constraint_for` is threaded to [`build_returns`]: with `Some(o)` the
    /// `<return-o>` constant is declared but left unconstrained on both sides, for the
    /// debugger to constrain from its per-path DSA encoding. `prove` passes `None`.
    pub(crate) fn emit_constant_declarations(
        &self,
        skip_return_constraint_for: Option<&str>,
    ) -> Vec<SmtExpr> {
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

        out.extend(build_returns(left, skip_return_constraint_for));
        out.extend(build_returns(right, skip_return_constraint_for));

        /////// randomess counters

        for (decl_ctr, assert_ctr, assert_zero_ctr) in build_rands(self.sample_info_left(), left) {
            out.push(decl_ctr);
            out.push(assert_ctr);
            // it is important for randomness mapping to assert that old counter is zero
            // otherwise offset is needed
            out.push(assert_zero_ctr);
        }

        for (decl_ctr, assert_ctr, assert_zero_ctr) in build_rands(self.sample_info_right(), right)
        {
            out.push(decl_ctr);
            out.push(assert_ctr);
            // it is important for randomness mapping to assert that old counter is zero
            // otherwise offset is needed
            out.push(assert_zero_ctr);
        }

        out
    }

    /// Returns an iterator of all the package const datatypes that need to be defined for this
    /// equivalence theorem. It makes sure to skip duplicate definitions, which may occur if a
    /// package is used more than once.
    pub(crate) fn smt_package_const_definitions(&'a self) -> impl Iterator<Item = SmtExpr> + 'a {
        let mut already_defined = BTreeSet::new();

        Some(self)
            .into_iter()
            .flat_map(|ectx| {
                vec![ectx.left_game_inst_ctx(), ectx.right_game_inst_ctx()].into_iter()
            })
            .flat_map(|gctx| gctx.pkg_inst_contexts())
            .map(|pctx| {
                let pattern = pctx.datastructure_pkg_consts_pattern();
                let spec = pattern.datastructure_spec(pctx.pkg());

                (pattern, spec)
            })
            .filter_map(move |(pattern, spec)| {
                if already_defined.insert(pattern.sort_name()) {
                    Some(declare_datatype(&pattern, &spec))
                } else {
                    None
                }
            })
    }

    /// Returns an iterator of all the package state datatypes that need to be defined for this
    /// equivalence theorem. It makes sure to skip duplicate definitions, which may occur if a
    /// package is used more than once.
    pub(crate) fn smt_package_state_definitions(&'a self) -> impl Iterator<Item = SmtExpr> + 'a {
        let mut already_defined = BTreeSet::new();

        Some(self)
            .into_iter()
            .flat_map(|ectx| {
                vec![ectx.left_game_inst_ctx(), ectx.right_game_inst_ctx()].into_iter()
            })
            .flat_map(|gctx| gctx.pkg_inst_contexts())
            .filter_map(move |pctx| {
                let pattern = pctx.pkg_state_pattern();
                let spec = pattern.datastructure_spec(pctx.pkg());

                if already_defined.insert(pattern.sort_name()) {
                    Some(declare_datatype(&pattern, &spec))
                } else {
                    None
                }
            })
    }

    /// Returns an iterator of all the package state datatypes that need to be defined for this
    /// equivalence theorem. It makes sure to skip duplicate definitions, which may occur if a
    /// package is used more than once.
    pub(crate) fn smt_package_return_definitions(&'a self) -> impl Iterator<Item = SmtExpr> + 'a {
        let mut already_defined = BTreeSet::new();

        Some(self)
            .into_iter()
            .flat_map(|ectx| {
                vec![ectx.left_game_inst_ctx(), ectx.right_game_inst_ctx()].into_iter()
            })
            .flat_map(|gctx| gctx.pkg_inst_contexts())
            .flat_map(|pctx| pctx.oracle_contexts())
            .filter_map(move |octx| {
                let pattern = octx.return_pattern();
                let spec = pattern.datastructure_spec(&octx.oracle_sig().ty);

                if already_defined.insert(pattern.sort_name()) {
                    Some(declare_datatype(&pattern, &spec))
                } else {
                    None
                }
            })
    }

    /// Returns an iterator of all the game state datatypes that need to be defined for this
    /// equivalence theorem. It makes sure to skip duplicate definitions, which may occur if a
    /// package is used more than once.
    pub(crate) fn smt_game_state_definitions(&'a self) -> impl Iterator<Item = SmtExpr> + 'a {
        let mut already_defined = BTreeSet::new();

        Some(self)
            .into_iter()
            .flat_map(move |ectx| {
                vec![
                    (ectx.left_game_inst_ctx(), self.sample_info_left()),
                    (ectx.right_game_inst_ctx(), self.sample_info_right()),
                ]
                .into_iter()
            })
            .filter_map(move |(gctx, sample_info)| {
                let declare_info = GameStateDeclareInfo {
                    game_inst: gctx.game_inst(),
                    sample_info,
                };

                let pattern = gctx.datastructure_game_state_pattern();
                let spec = pattern.datastructure_spec(&declare_info);

                if already_defined.insert(pattern.sort_name()) {
                    let datatype = declare_datatype(&pattern, &spec);
                    Some(datatype)
                } else {
                    None
                }
            })
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
        let mut already_defined = BTreeSet::new();

        Some(self)
            .into_iter()
            .flat_map(move |ectx| {
                vec![ectx.left_game_inst_ctx(), ectx.right_game_inst_ctx()].into_iter()
            })
            .filter_map(move |gctx| {
                let pattern = gctx.datastructure_game_consts_pattern();
                let spec = pattern.datastructure_spec(gctx.game());

                if already_defined.insert(pattern.sort_name()) {
                    Some(declare_datatype(&pattern, &spec))
                } else {
                    None
                }
            })
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
            .flat_map(|gctx| {
                gctx.game().pkgs.iter().flat_map(move |pkg_inst| {
                    define_pkg_const_mapping_fun(gctx.game(), &pkg_inst.pkg, &pkg_inst.name)
                        .map(SmtExpr::from)
                })
            })
    }

    pub(crate) fn smt_oracle_function_definitions(&'a self) -> impl Iterator<Item = SmtExpr> + 'a {
        let mut already_defined = BTreeSet::new();

        Some(self)
            .into_iter()
            .flat_map(move |ectx| {
                let left_gctx = ectx.left_game_inst_ctx();
                let right_gctx = ectx.right_game_inst_ctx();

                vec![
                    (left_gctx, ectx.sample_info_left()),
                    (right_gctx, ectx.sample_info_right()),
                ]
                .into_iter()
            })
            .flat_map(|(gctx, sample_info)| {
                gctx.pkg_inst_contexts()
                    .map(move |pctx| (pctx, sample_info))
            })
            .flat_map(|(pctx, sample_info)| {
                pctx.oracle_contexts().map(move |octx| (octx, sample_info))
            })
            .filter_map(move |(octx, sample_info)| {
                let gctx = octx.game_inst_ctx();
                let pctx = octx.pkg_inst_ctx();
                let pattern = octx.oracle_pattern();

                let game_inst = gctx.game_inst();

                let writer = CompositionSmtWriter::new(game_inst, sample_info);

                if already_defined.insert(pattern.function_name()) {
                    let fundef =
                        writer.smt_define_nonsplit_oracle_fn(pctx.pkg_inst(), octx.oracle_def());
                    Some(fundef)
                } else {
                    None
                }
            })
    }
}

/// Emits, for every exported oracle of `game_inst`, the four declare/constrain pairs the
/// claim machinery relies on: `<return-…>`, `return-value-…`, `<return-is-abort-…>` and the
/// new game state, each declared then constrained, interleaved in that order.
///
/// When `skip_return_constraint_for == Some(o)` and the export's adversary-visible name is
/// `o`, the `<return-o>` **declaration** is still emitted but its constraint
/// `(= <return-o> (<oracle-fn> …))` is **not**. The debugger supplies that constraint itself
/// from its per-path DSA encoding; `return-value-o`, `<return-is-abort-o>` and the new state
/// stay constrained off `<return-o>` exactly as before, so `emit_oracle_claim_assert`, the
/// invariants and the relations keep working unchanged.
fn build_returns(
    game_inst: &GameInstance,
    skip_return_constraint_for: Option<&str>,
) -> Vec<SmtExpr> {
    let gctx = GameInstanceContext::new(game_inst);
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

        out.push(return_const.declare());
        if skip_return_constraint_for != Some(oracle_import_name) {
            out.push(constrain_return.into());
        }
        out.push(return_value_const.declare());
        out.push(constrain_return_value.into());
        out.push(is_abort_const_pattern.declare());
        out.push(constrain_is_abort.into());
        out.push(state.declare_new(game_inst_name, oracle_import_name.to_string()));
        out.push(constrain_new_state.into());
    }

    out
}

fn build_rands(
    sample_info: &SampleInfo,
    game_inst: &GameInstance,
) -> Vec<(SmtExpr, SmtExpr, SmtExpr)> {
    let gctx = GameInstanceContext::new(game_inst);

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
            let randctr = gctx
                .smt_access_gamestate_rand(sample_info, state, sample_id)
                .unwrap();

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
mod story04_tests {
    //! Story 04 — assumptions/goal split + skippable return constraint.
    //!
    //! These pin the `prove`-facing output (`emit_oracle_claim_assert`,
    //! `emit_constant_declarations(None)`) against committed goldens and check the two new
    //! debugger-facing emitters compose back to the single refutation `prove` uses.

    use crate::gamehops::GameHop;
    use crate::project::Project as _;
    use crate::theorem::{Claim, ClaimType};
    use crate::transforms::{theorem_transforms::EquivalenceTransform, TheoremTransform};
    use crate::writers::smt::contexts::EquivalenceContext;
    use crate::writers::smt::exprs::{SmtAnd, SmtAssert, SmtExpr, SmtImplies, SmtNot};

    const PROJECT: &str = "example-projects/kem-dem/kem-dem-cca-ssp";
    const THEOREM: &str = "kem_dem_cca_ssp";
    const ORACLE: &str = "PKENC";

    /// A claim that exercises every arm of `claim_assumptions_and_goal`: a `Lemma` goal, a
    /// `Relation` dependency (name starts with `relation`) and a `Lemma` dependency.
    fn mixed_claim() -> Claim {
        Claim {
            name: "same-output".to_string(),
            ty: ClaimType::Lemma,
            dependencies: vec![
                "relation-no-abort".to_string(),
                "lemma-kem-correctness".to_string(),
            ],
            admitted: false,
        }
    }

    fn with_eqctx(f: impl FnOnce(&EquivalenceContext<'_>)) {
        let files =
            crate::project::DirectoryFiles::load(std::path::Path::new(PROJECT)).unwrap();
        let project =
            crate::project::DirectoryProject::load(std::path::PathBuf::from(PROJECT), &files)
                .unwrap();
        let theorem = project.get_theorem(THEOREM).unwrap();
        let (theorem, auxs) = EquivalenceTransform.transform_theorem(theorem).unwrap();

        let eq = theorem
            .game_hops
            .iter()
            .find_map(|hop| match hop {
                GameHop::Equivalence(eq) => Some(eq),
                _ => None,
            })
            .expect("proofstep 0 is an equivalence");

        let eqctx = EquivalenceContext::new(eq, &theorem, &auxs);
        f(&eqctx);
    }

    /// Compares `actual` against `testdata/story04/<name>`. If the golden file is missing it
    /// is written and the test fails, asking for a re-run — so the first run bootstraps it.
    fn check_golden(name: &str, actual: &str) {
        let path = std::path::Path::new("testdata/story04").join(name);
        match std::fs::read_to_string(&path) {
            Ok(expected) => assert_eq!(actual, expected, "golden mismatch for {name}"),
            Err(_) => {
                std::fs::create_dir_all(path.parent().unwrap()).unwrap();
                std::fs::write(&path, actual).unwrap();
                panic!("wrote new golden {}; re-run the test", path.display());
            }
        }
    }

    fn render(exprs: &[SmtExpr]) -> String {
        exprs
            .iter()
            .map(|e| e.to_string())
            .collect::<Vec<_>>()
            .join("\n")
    }

    #[test]
    fn emit_oracle_claim_assert_matches_golden() {
        with_eqctx(|eqctx| {
            let out = eqctx.emit_oracle_claim_assert(&mixed_claim(), ORACLE);
            check_golden("emit_oracle_claim_assert.smt2", &out.to_string());
        });
    }

    #[test]
    fn emit_constant_declarations_none_matches_golden() {
        with_eqctx(|eqctx| {
            let out = eqctx.emit_constant_declarations(None);
            check_golden("emit_constant_declarations_none.smt2", &render(&out));
        });
    }

    /// The wrappers compose back to exactly the single refutation `prove` emits.
    #[test]
    fn assumptions_and_negated_goal_compose_to_claim_assert() {
        with_eqctx(|eqctx| {
            let claim = mixed_claim();
            let (deps, goal) = eqctx.claim_assumptions_and_goal(&claim, ORACLE);

            let recombined: SmtExpr = SmtAssert(SmtNot(SmtImplies(
                SmtAnd(deps.clone()),
                goal.clone(),
            )))
            .into();
            assert_eq!(
                recombined.to_string(),
                eqctx.emit_oracle_claim_assert(&claim, ORACLE).to_string(),
            );

            // one `(assert <dep>)` per assumption, same order
            let assumptions = eqctx.emit_claim_assumptions(&claim, ORACLE);
            assert_eq!(assumptions.len(), deps.len());
            for (asserted, term) in assumptions.iter().zip(&deps) {
                let expected: SmtExpr = SmtAssert(term.clone()).into();
                assert_eq!(asserted.to_string(), expected.to_string());
            }

            // `(assert (not <goal>))`
            let negated = eqctx.emit_claim_goal_negated(&claim, ORACLE);
            let expected: SmtExpr = SmtAssert(SmtNot(goal)).into();
            assert_eq!(negated.to_string(), expected.to_string());
        });
    }

    /// `emit_constant_declarations(Some(o))` differs from `None` by exactly the two
    /// `constrain_return` asserts for `o` (left + right) and nothing else.
    #[test]
    fn skip_return_constraint_drops_exactly_two_asserts() {
        with_eqctx(|eqctx| {
            let none: Vec<String> = eqctx
                .emit_constant_declarations(None)
                .iter()
                .map(|e| e.to_string())
                .collect();
            let some: Vec<String> = eqctx
                .emit_constant_declarations(Some(ORACLE))
                .iter()
                .map(|e| e.to_string())
                .collect();

            // `some` is `none` with two entries removed, order otherwise preserved.
            let mut some_iter = some.iter();
            let mut removed = Vec::new();
            let mut cursor = some_iter.next();
            for line in &none {
                if cursor == Some(line) {
                    cursor = some_iter.next();
                } else {
                    removed.push(line.clone());
                }
            }
            assert_eq!(cursor, None, "`some` is not a subsequence of `none`");
            assert_eq!(removed.len(), 2, "expected exactly two dropped asserts");
            for r in &removed {
                let flat: String = r.split_whitespace().collect::<Vec<_>>().join(" ");
                assert!(
                    flat.starts_with("(assert (= <return-")
                        && flat.contains(&format!("-{ORACLE}> (<oracle-")),
                    "unexpected dropped line: {r}"
                );
            }
            // one for the left game instance, one for the right
            assert_ne!(removed[0], removed[1]);
        });
    }
}
