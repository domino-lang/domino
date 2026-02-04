// SPDX-License-Identifier: MIT OR Apache-2.0

use std::collections::{BTreeSet, HashMap, HashSet};
use std::fmt::Write;
use std::iter::FromIterator;

use crate::expressions::{Expression, ExpressionKind};
use crate::identifier::game_ident::GameIdentifier;
use crate::identifier::pkg_ident::PackageIdentifier;
use crate::identifier::theorem_ident::{TheoremConstIdentifier, TheoremIdentifier};
use crate::identifier::Identifier;
use crate::types::{CountSpec, TypeKind};
use crate::writers::smt::contexts::GameInstanceContext;
use crate::writers::smt::declare::declare_const;
use crate::writers::smt::patterns::const_mapping::{
    define_game_const_mapping_fun, GameConstMappingFunction,
};
use crate::writers::smt::patterns::functions::const_mapping::define_pkg_const_mapping_fun;
use crate::writers::smt::patterns::oracle_args::{
    OldNewOracleArgPattern as _, UnitOracleArgPattern as _,
};
use crate::writers::smt::patterns::{
    declare_datatype, FunctionPattern, GameStateDeclareInfo, ReturnIsAbortConst,
};
use crate::writers::smt::sorts::Sort;
use crate::{
    hacks,
    package::{Export, OracleSig},
    theorem::{Claim, ClaimType, GameInstance, Theorem},
    transforms::{
        samplify::SampleInfo, theorem_transforms::EquivalenceTransform, TheoremTransform,
    },
    types::Type,
    util::prover_process::{Communicator, ProverResponse},
    writers::smt::{
        contexts::{self, GenericOracleContext},
        declare,
        exprs::{SmtAnd, SmtAssert, SmtEq2, SmtExpr, SmtForall, SmtImplies, SmtIte, SmtNot},
        patterns::{self, ConstantPattern, DatastructurePattern},
        writer::CompositionSmtWriter,
    },
};

// Equivalence contains the composisitions/games and the invariant data,
// whereas the pure Equivalence just contains the names and file paths.
// TODO: explore if we can keep references to the games in the project hashmap
#[derive(Debug, Clone)]
pub struct Equivalence {
    // these two are game instance names
    pub(crate) left_name: String,
    pub(crate) right_name: String,
    pub(crate) invariants: Vec<(String, Vec<String>)>,
    pub(crate) trees: Vec<(String, Vec<Claim>)>,
}

impl Equivalence {
    pub fn new(
        left_name: String,
        right_name: String,
        mut invariants: Vec<(String, Vec<String>)>,
        mut trees: Vec<(String, Vec<Claim>)>,
    ) -> Self {
        trees.sort();
        invariants.sort();

        Equivalence {
            left_name,
            right_name,
            invariants, // TODO INV
            trees,
        }
    }

    pub fn trees(&self) -> &[(String, Vec<Claim>)] {
        &self.trees
    }

    pub fn left_name(&self) -> &str {
        &self.left_name
    }

    pub fn right_name(&self) -> &str {
        &self.right_name
    }

    pub fn get_invariants(&self, offs: usize) -> Option<&[String]> {
        self.invariants
            .get(offs)
            .map(|(_name, invariants)| invariants.as_slice())
    }

    pub fn invariants_by_oracle_name(&self, oracle_name: &str) -> Vec<String> {
        self.invariants
            .iter()
            .find_map(|(oracle_name_, invariants)| {
                if oracle_name_.as_str() == oracle_name {
                    Some(invariants.clone())
                } else {
                    None
                }
            })
            .unwrap_or(vec![])
    }

    pub(crate) fn proof_tree_by_oracle_name(&self, oracle_name: &str) -> Vec<Claim> {
        self.trees
            .iter()
            .find(|(name, _tree)| name == oracle_name)
            .map(|(_oname, tree)| tree.clone())
            .unwrap_or_else(|| panic!("can't find proof tree for {oracle_name}"))
    }
}

pub mod error;
mod verify_fn;

use error::{Error, Result};
pub use verify_fn::{verify, verify_parallel};

#[derive(Clone, Copy)]
pub(crate) struct EquivalenceContext<'a> {
    equivalence: &'a Equivalence,
    theorem: &'a Theorem<'a>,
    auxs: &'a <EquivalenceTransform as TheoremTransform>::Aux,
}

// simple getters
impl<'a> EquivalenceContext<'a> {
    pub(crate) fn theorem(&self) -> &'a Theorem<'a> {
        self.theorem
    }

    pub(crate) fn equivalence(&self) -> &'a Equivalence {
        self.equivalence
    }
}

// subcontexts
impl<'a> EquivalenceContext<'a> {
    pub(crate) fn left_game_inst_ctx(self) -> contexts::GameInstanceContext<'a> {
        let game_inst = self
            .theorem()
            .find_game_instance(self.equivalence().left_name())
            .unwrap();

        contexts::GameInstanceContext::new(game_inst)
    }

    pub(crate) fn right_game_inst_ctx(self) -> contexts::GameInstanceContext<'a> {
        let game_inst = self
            .theorem()
            .find_game_instance(self.equivalence().right_name())
            .unwrap();

        contexts::GameInstanceContext::new(game_inst)
    }
}

impl<'a> EquivalenceContext<'a> {
    fn emit_base_declarations(&self, comm: &mut Communicator) -> Result<()> {
        let mut base_declarations: Vec<SmtExpr> = vec![("set-logic", "ALL").into()];

        let mut bits_sort_suffixes = HashSet::new();

        for ty in self.types() {
            if let TypeKind::Bits(count_spec) = &ty.kind() {
                let bits_sort_suffix = match count_spec {
                    crate::types::CountSpec::Literal(num) => format!("{num}"),
                    crate::types::CountSpec::Any => "*".to_string(),
                    crate::types::CountSpec::Identifier(ident) => match ident.as_ref() {
                        Identifier::TheoremIdentifier(ident) => ident.ident(),
                        Identifier::GameIdentifier(GameIdentifier::Const(game_const_ident)) => {
                            match game_const_ident.assigned_value.as_ref().map(Box::as_ref).map(Expression::kind) {
                                Some(ExpressionKind::Identifier(ident@Identifier::TheoremIdentifier(TheoremIdentifier::Const(_)))) => ident.ident(),
                                Some(ExpressionKind::Identifier(_)) => unreachable!("other identifiers can't occur here"),
                                Some(other) => todo!("ADD ERR MSG: no complex expressions allowed for now, found {other:?}"),
                                None => {log::debug!("skipping identifier {count_spec:?} since it is not fully resolved"); ident.ident()}
                            }
                        } ,
                        Identifier::PackageIdentifier(PackageIdentifier::Const(pkg_const_ident)) => match pkg_const_ident.game_assignment.as_ref().unwrap_or_else(|| panic!("the assigned value for this identifier should have been resolved at this point:\n  {pkg_const_ident:#?}")).as_ref().kind() {
                            ExpressionKind::Identifier(Identifier::GameIdentifier(GameIdentifier::Const(game_const_ident))) => {
                                match game_const_ident.assigned_value.as_ref().map(Box::as_ref).map(Expression::kind) {
                                    Some(ExpressionKind::Identifier(ident@Identifier::TheoremIdentifier(TheoremIdentifier::Const(_))) )=> ident.ident(),
                                    Some(ExpressionKind::Identifier(_) )=> unreachable!("other identifiers can't occur here"),
                                    Some(other) => todo!("ADD ERR MSG: no complex expressions allowed for now, found {other:?}"),
                                    None => {log::debug!("skipping identifier {count_spec:?} since it is not fully resolved"); ident.ident()}
                                }
                            },
                            ExpressionKind::Identifier(_) => unreachable!("other identifiers can't occur here"),
                            other => todo!("ADD ERR MSG: no complex expressions allowed for now, found {other:?}"),
                        }
                        Identifier::PackageIdentifier(_) => unreachable!("non-const package identifiers can't occur here"),
                        Identifier::GameIdentifier(_) => unreachable!("non-const game identifiers can't occur here"),
                        Identifier::Generated(_, _) => unreachable!("generated identifiers can't occur here"),
                    },
                };

                log::debug!("found {bits_sort_suffix}");

                // ensure we don't write more than once. Earlier we also dedupe, but we dedupe
                // identifiers, which contain more info than just the name.
                if bits_sort_suffixes.insert(bits_sort_suffix.clone()) {
                    base_declarations.extend(hacks::BitsDeclaration(bits_sort_suffix).into_iter());
                }
            }
        }

        base_declarations.extend(hacks::MaybeDeclaration);
        base_declarations.push(hacks::ReturnValueDeclaration.into());
        base_declarations.extend(hacks::TuplesDeclaration(1..32));
        base_declarations.extend(hacks::EmptyDeclaration);
        base_declarations.push(hacks::SampleIdDeclaration.into());

        for decl in base_declarations {
            comm.write_smt(decl)?
        }

        Ok(())
    }

    fn emit_theorem_paramfuncs(&self, comm: &mut Communicator) -> Result<()> {
        fn get_fn<T: Clone>(arg: &(T, Type)) -> Option<(T, Vec<Type>, Type)> {
            let (other, ty) = arg;
            match ty.kind() {
                TypeKind::Fn(args, ret) => Some((other.clone(), args.to_vec(), *ret.clone())),
                _ => None,
            }
        }

        let funcs = self.theorem.consts.iter().filter_map(get_fn);

        for (func_name, arg_types, ret_type) in funcs {
            let arg_types: SmtExpr = arg_types
                .into_iter()
                .map(|ty| ty.into())
                .collect::<Vec<SmtExpr>>()
                .into();

            let smt = (
                "declare-fun",
                format!("<<func-{func_name}>>"),
                arg_types,
                ret_type,
            );
            comm.write_smt(smt)?;
        }
        Ok(())
    }

    fn emit_game_definitions(&self, comm: &mut Communicator) -> Result<()> {
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

        let mut out = vec![];

        // This is for debugging, so we know what section the offending thing came from
        let mut offsets = Vec::with_capacity(16);

        out.append(&mut left_writer.smt_composition_randomness());
        offsets.push((out.len(), "left writer comp rand"));
        out.append(&mut right_writer.smt_composition_randomness());
        offsets.push((out.len(), "right writer comp rand"));

        out.extend(self.smt_package_const_definitions());
        offsets.push((out.len(), "pkg const defs"));
        out.extend(self.smt_package_state_definitions());
        offsets.push((out.len(), "pkg state defs"));

        out.extend(self.smt_theorem_const_definition());
        offsets.push((out.len(), "theorem const defs"));
        out.extend(self.smt_game_const_definitions());
        offsets.push((out.len(), "game const defs"));
        out.extend(self.smt_game_state_definitions());
        offsets.push((out.len(), "game state defs"));

        out.extend(self.smt_theorem_game_const_mapping_definitions());
        offsets.push((out.len(), "theorem to game const mapping defs"));
        out.extend(self.smt_game_pkg_const_mapping_definitions());
        offsets.push((out.len(), "game to pkg const mapping defs"));

        out.extend(self.smt_package_return_definitions());
        offsets.push((out.len(), "pkg return type defs"));
        out.extend(self.smt_oracle_function_definitions());
        offsets.push((out.len(), "oracle function defs"));
        //out.append(&mut left_writer.smt_datatypes());
        // out.append(&mut right_writer.smt_datatypes());

        //out.append(&mut left_writer.smt_oracle_functions());
        //out.append(&mut right_writer.smt_oracle_functions());
        // out.append(&mut left_writer.smt_composition_partial_stuff());
        // out.append(&mut right_writer.smt_composition_partial_stuff());

        //out.append(&mut left_writer.smt_composition_all());
        //out.append(&mut right_writer.smt_composition_all());

        for (i, ref decl) in out.into_iter().enumerate() {
            comm.write_smt(decl.clone()).inspect_err(|err| {
                let (_, section) = offsets.iter().find(|(j, _)| i <= *j).unwrap();
                log::debug!(
                    "failed with at item {i}(section {section}) with error {err} at decl {decl:?}"
                )
            })?
        }

        Ok(())
    }

    fn emit_constant_declarations(&self, comm: &mut Communicator) -> Result<()> {
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

        let gctx_left = contexts::GameInstanceContext::new(left);
        let gctx_right = contexts::GameInstanceContext::new(right);

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

        ////// split stuff

        // let mut processed = HashSet::new();
        // for SplitExport(pkg_inst_offs, oracle_sig) in &left_game.split_exports {
        //     let pkg_inst = &left_game.pkgs[*pkg_inst_offs];
        //
        //     let pkg_inst_name = &pkg_inst.name;
        //     let pkg_name = &pkg_inst.pkg.name;
        //     let pkg_params = &pkg_inst.params;
        //     let oracle_name = &oracle_sig.name;
        //
        //     if processed.contains(oracle_name) {
        //         continue;
        //     }
        //
        //     processed.insert(oracle_name);
        //
        //     let decl_intermediate_state_left = patterns::IntermediateStateConst {
        //         game_inst_name: left_game_inst_name,
        //         pkg_inst_name,
        //         pkg_name,
        //         pkg_params,
        //         oracle_name,
        //         variant: "old",
        //     };
        //
        //     out.push(decl_intermediate_state_left.declare());
        // }
        //
        // let mut processed = HashSet::new();
        // for SplitExport(pkg_inst_offs, oracle_sig) in &right_game.split_exports {
        //     let pkg_inst_name = &right_game.pkgs[*pkg_inst_offs].name;
        //     let pkg_params = &right_game.pkgs[*pkg_inst_offs].params;
        //     let pkg_name = &right_game.pkgs[*pkg_inst_offs].pkg.name;
        //     let oracle_name = &oracle_sig.name;
        //
        //     if processed.contains(oracle_name) {
        //         continue;
        //     }
        //
        //     processed.insert(oracle_name);
        //
        //     let decl_intermediate_state_right = patterns::IntermediateStateConst {
        //         game_inst_name: right_game_inst_name,
        //         pkg_inst_name,
        //         pkg_name,
        //         pkg_params,
        //         oracle_name,
        //         variant: "old",
        //     };
        //
        //     out.push(decl_intermediate_state_right.declare());
        // }

        /////// arguments for non-split and split oracles

        // let left_partial_datatypes = into_partial_dtypes(self.split_info_left());
        // let right_partial_datatypes = into_partial_dtypes(self.split_info_right());

        // write declarations of arguments for the exports in left
        for Export(_, sig) in &left.game().exports {
            if let Some(orcl_ctx) = gctx_left.exported_oracle_ctx_by_name(&sig.name) {
                for (arg_name, arg_type) in &sig.args {
                    out.push(declare::declare_const(
                        orcl_ctx.smt_arg_name(arg_name),
                        arg_type.clone().into(),
                    ));
                }
            }

            // if let Some(partial_dtype) = left_partial_datatypes
            //     .iter()
            //     .find(|dtype| dtype.real_oracle_sig.name == sig.name)
            // {
            //     let orcl_ctx = gctx_left
            //         .exported_split_oracle_ctx_by_name(&sig.name, partial_dtype)
            //         .unwrap();
            //     for (arg_name, arg_type) in &sig.args {
            //         out.push(declare::declare_const(
            //             orcl_ctx.smt_arg_name(arg_name),
            //             arg_type.clone().into(),
            //         ));
            //     }
            // }
        }

        // write declarations of arguments for the split oracles of the right.
        // the non-split ones are shared between games and have already been
        // added for the loop above.
        // for Export(_, sig) in &right.game().exports {
        //     if let Some(partial_dtype) = right_partial_datatypes
        //         .iter()
        //         .find(|dtype| dtype.real_oracle_sig.name == sig.name)
        //     {
        //         let orcl_ctx = gctx_right
        //             .exported_split_oracle_ctx_by_name(&sig.name, partial_dtype)
        //             .unwrap();
        //         for (arg_name, arg_type) in &sig.args {
        //             out.push(declare::declare_const(
        //                 orcl_ctx.smt_arg_name(arg_name),
        //                 arg_type.clone().into(),
        //             ));
        //         }
        //     }
        // }

        ////// return values

        for (decl_ret, constrain) in build_returns(left) {
            out.push(decl_ret);
            out.push(constrain);
        }

        for (decl_ret, constrain) in build_returns(right) {
            out.push(decl_ret);
            out.push(constrain);
        }

        // for (decl_ret, constrain) in build_partial_returns(left, &left_partial_datatypes) {
        //     out.push(decl_ret);
        //     out.push(constrain);
        // }
        //
        // for (decl_ret, constrain) in build_partial_returns(right, &right_partial_datatypes) {
        //     out.push(decl_ret);
        //     out.push(constrain);
        // }

        /////// randomess counters

        for (decl_ctr, assert_ctr, decl_val, assert_val) in
            build_rands(self.sample_info_left(), left)
        {
            out.push(decl_ctr);
            out.push(assert_ctr);
            out.push(decl_val);
            out.push(assert_val);
        }

        for (decl_ctr, assert_ctr, decl_val, assert_val) in
            build_rands(self.sample_info_right(), right)
        {
            out.push(decl_ctr);
            out.push(assert_ctr);
            out.push(decl_val);
            out.push(assert_val);
        }

        /////////// helpers for working with randomness

        out.push(self.smt_define_randctr_function(left, self.sample_info_left()));
        out.push(self.smt_define_randctr_function(right, self.sample_info_right()));
        out.push(self.smt_define_randeq_function());

        ///// write expressions

        for expr in out {
            comm.write_smt(expr)?;
        }

        Ok(())
    }

    fn emit_return_value_helpers(&self, comm: &mut Communicator, oracle_name: &str) -> Result<()> {
        let left_gctx = self.left_game_inst_ctx();
        let left_octx = left_gctx.exported_oracle_ctx_by_name(oracle_name).unwrap();
        let left_pctx = left_octx.pkg_inst_ctx();

        let right_gctx = self.right_game_inst_ctx();
        let right_octx = right_gctx.exported_oracle_ctx_by_name(oracle_name).unwrap();
        let right_pctx = right_octx.pkg_inst_ctx();

        let left_return_value = left_octx.return_value_const_pattern();
        let right_return_value = right_octx.return_value_const_pattern();

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

        for (name, value) in consts {
            let declare = declare_const(name, Sort::Bool);
            let constrain = SmtAssert(SmtEq2 {
                lhs: name,
                rhs: value,
            });

            comm.write_smt(declare)?;
            comm.write_smt(constrain)?;
        }

        comm.write_smt(self.relation_definition_equal_aborts(oracle_name))?;
        comm.write_smt(self.relation_definition_left_no_abort(oracle_name))?;
        comm.write_smt(self.relation_definition_right_no_abort(oracle_name))?;
        comm.write_smt(self.relation_definition_no_abort(oracle_name))?;
        comm.write_smt(self.relation_definition_same_output(oracle_name))?;

        Ok(())
    }

    fn emit_invariant(&self, comm: &mut Communicator, oracle_name: &str) -> Result<()> {
        for file_name in &self.equivalence.invariants_by_oracle_name(oracle_name) {
            log::info!("reading file {file_name}");
            let file_contents = std::fs::read_to_string(file_name).map_err(|err| {
                let file_name = file_name.clone();
                error::new_invariant_file_read_error(oracle_name.to_string(), file_name, err)
            })?;
            log::info!("read file {file_name}");
            write!(comm, "{file_contents}").unwrap();
            log::info!("wrote contents of file {file_name}");

            if comm.check_sat()? != ProverResponse::Sat {
                return Err(Error::UnsatAfterInvariantRead {
                    equivalence: self.equivalence.clone(),
                    oracle_name: oracle_name.to_string(),
                });
            }
        }

        Ok(())
    }

    // fn split_oracle_sig_by_exported_name(
    //     &'a self,
    //     oracle_name: &str,
    // ) -> Option<&'a SplitOracleSig> {
    //     let gctx_left = self.left_game_inst_ctx();
    //
    //     gctx_left
    //         .game()
    //         .split_exports
    //         .iter()
    //         .find(|SplitExport(_, sig)| sig.name == oracle_name)
    //         .and_then(|SplitExport(inst_idx, _)| {
    //             gctx_left.game().pkgs[*inst_idx]
    //                 .pkg
    //                 .split_oracles
    //                 .iter()
    //                 .find(|odef| odef.sig.name == oracle_name)
    //                 .map(|odef| &odef.sig)
    //         })
    // }
    //
    // fn emit_split_claim_assert(
    //     &self,
    //     comm: &mut Communicator,
    //     oracle_name: &str,
    //     path: &SplitPath,
    //     claim: &Claim,
    // ) -> Result<()> {
    //     println!("name: {oracle_name}");
    //     println!("path: {path:?}");
    //
    //     let gctx_left = self.left_game_inst_ctx();
    //     let gctx_right = self.right_game_inst_ctx();
    //
    //     let game_inst_name_left = self.equivalence.left_name();
    //     let game_inst_name_right = self.equivalence.right_name();
    //
    //     let game_name_left = &gctx_left.game().name;
    //     let game_name_right = &gctx_right.game().name;
    //
    //     let game_params_left = &gctx_left.game_inst().consts;
    //     let game_params_right = &gctx_right.game_inst().consts;
    //
    //     let pkg_inst_ctx_left = gctx_left
    //         .pkg_inst_ctx_by_exported_split_oracle_name(oracle_name)
    //         .unwrap();
    //     let pkg_inst_ctx_right = gctx_right
    //         .pkg_inst_ctx_by_exported_split_oracle_name(oracle_name)
    //         .unwrap();
    //
    //     let pkg_inst_name_left = pkg_inst_ctx_left.pkg_inst_name();
    //     let pkg_inst_name_right = pkg_inst_ctx_right.pkg_inst_name();
    //
    //     let pkg_name_left = pkg_inst_ctx_left.pkg_name();
    //     let pkg_name_right = pkg_inst_ctx_right.pkg_name();
    //
    //     let pkg_params_left = &pkg_inst_ctx_left.pkg_inst().params;
    //     let pkg_params_right = &pkg_inst_ctx_right.pkg_inst().params;
    //
    //     let args: Vec<_> = self
    //         .split_oracle_sig_by_exported_name(oracle_name)
    //         .unwrap()
    //         .args
    //         .iter()
    //         .map(|(arg_name, arg_type)| patterns::OracleArgs {
    //             oracle_name,
    //             arg_name,
    //             arg_type,
    //         })
    //         .collect();
    //
    //     // find the package instance which is marked as exporting
    //     // the oracle of this name, both left and right.
    //     let left_partial_return_name = patterns::PartialReturnConst {
    //         game_name: game_name_left,
    //         game_params: game_params_left,
    //         pkg_name: pkg_name_left,
    //         pkg_params: pkg_params_left,
    //         game_inst_name: game_inst_name_left,
    //         pkg_inst_name: pkg_inst_name_left,
    //         oracle_name,
    //     }
    //     .name();
    //
    //     let right_partial_return_name = patterns::PartialReturnConst {
    //         game_name: game_name_right,
    //         game_params: game_params_right,
    //         game_inst_name: game_inst_name_right,
    //         pkg_name: pkg_name_right,
    //         pkg_params: pkg_params_right,
    //         pkg_inst_name: pkg_inst_name_right,
    //         oracle_name,
    //     }
    //     .name();
    //
    //     let state_left = gctx_left.oracle_arg_game_state_pattern();
    //     let state_right = gctx_right.oracle_arg_game_state_pattern();
    //
    //     let state_left_new_name =
    //         state_left.new_global_const_name(game_inst_name_left, oracle_name.to_string());
    //     let state_left_old_name = state_left.old_global_const_name(game_inst_name_left);
    //
    //     let state_right_new_name =
    //         state_right.new_global_const_name(game_inst_name_right, oracle_name.to_string());
    //     let state_right_old_name = state_right.old_global_const_name(game_inst_name_right);
    //
    //     let intermediate_state_left_new_name = patterns::IntermediateStateConst {
    //         game_inst_name: game_inst_name_left,
    //         pkg_inst_name: pkg_inst_name_left,
    //         pkg_name: pkg_name_left,
    //         pkg_params: pkg_params_left,
    //         oracle_name,
    //         variant: &format!("new-{oracle_name}"),
    //     }
    //     .name();
    //
    //     let intermediate_state_left_old_name = patterns::IntermediateStateConst {
    //         game_inst_name: game_inst_name_left,
    //         pkg_inst_name: pkg_inst_name_left,
    //         pkg_name: pkg_name_left,
    //         pkg_params: pkg_params_left,
    //         oracle_name,
    //         variant: "old",
    //     }
    //     .name();
    //
    //     let intermediate_state_right_new_name = patterns::IntermediateStateConst {
    //         game_inst_name: game_inst_name_right,
    //         pkg_inst_name: pkg_inst_name_right,
    //         pkg_name: pkg_name_right,
    //         pkg_params: pkg_params_right,
    //         oracle_name,
    //         variant: &format!("new-{oracle_name}"),
    //     }
    //     .name();
    //
    //     let intermediate_state_right_old_name = patterns::IntermediateStateConst {
    //         game_inst_name: game_inst_name_right,
    //         pkg_inst_name: pkg_inst_name_right,
    //         pkg_name: pkg_name_right,
    //         pkg_params: pkg_params_right,
    //         oracle_name,
    //         variant: "old",
    //     }
    //     .name();
    //
    //     let randomness_mapping = SmtForall {
    //         bindings: vec![
    //             ("randmap-sample-id-left".into(), Type::Integer.into()),
    //             ("randmap-sample-ctr-left".into(), Type::Integer.into()),
    //             ("randmap-sample-id-right".into(), Type::Integer.into()),
    //             ("randmap-sample-ctr-right".into(), Type::Integer.into()),
    //         ],
    //         body: (
    //             "=>",
    //             (
    //                 format!("randomness-mapping-{oracle_name}"),
    //                 (
    //                     format!("get-rand-ctr-{game_inst_name_left}"),
    //                     "randmap-sample-id-left",
    //                 ),
    //                 (
    //                     format!("get-rand-ctr-{game_inst_name_right}"),
    //                     "randmap-sample-id-right",
    //                 ),
    //                 "randmap-sample-id-left",
    //                 "randmap-sample-id-right",
    //                 "randmap-sample-ctr-left",
    //                 "randmap-sample-ctr-right",
    //             ),
    //             (
    //                 "rand-is-eq",
    //                 "randmap-sample-id-left",
    //                 "randmap-sample-id-right",
    //                 "randmap-sample-ctr-left",
    //                 "randmap-sample-ctr-right",
    //             ),
    //         ),
    //     };
    //
    //     // this helper builds an smt expression that calls the
    //     // function with the given name with the old states,
    //     // return values and the respective arguments.
    //     // We expect that function to return a boolean, which makes
    //     // it a relation.
    //     let build_lemma_call = |name: &str| {
    //         let mut tmp: Vec<SmtExpr> = vec![
    //             name.into(),
    //             state_left_old_name.clone().into(),
    //             state_right_old_name.clone().into(),
    //             intermediate_state_left_old_name.clone().into(),
    //             intermediate_state_right_old_name.clone().into(),
    //             left_partial_return_name.clone().into(),
    //             right_partial_return_name.clone().into(),
    //         ];
    //
    //         for arg in args {
    //             tmp.push(arg.name().into());
    //         }
    //
    //         SmtExpr::List(tmp)
    //     };
    //
    //     let build_relation_call = |name: &str| -> SmtExpr {
    //         (
    //             name,
    //             &state_left_new_name,
    //             &state_right_new_name,
    //             &intermediate_state_left_new_name,
    //             &intermediate_state_right_new_name,
    //         )
    //             .into()
    //     };
    //
    //     let build_invariant_old_call = |name: &str| -> SmtExpr {
    //         (
    //             name,
    //             &state_left_old_name,
    //             &state_right_old_name,
    //             &intermediate_state_left_old_name,
    //             &intermediate_state_right_old_name,
    //         )
    //             .into()
    //     };
    //
    //     let build_invariant_new_call = |name: &str| -> SmtExpr {
    //         (
    //             name,
    //             &state_left_new_name,
    //             &state_right_new_name,
    //             &intermediate_state_left_new_name,
    //             &intermediate_state_right_new_name,
    //         )
    //             .into()
    //     };
    //
    //     let dep_calls: Vec<_> = claim
    //         .dependencies()
    //         .iter()
    //         .map(|dep_name| {
    //             let claim_type = ClaimType::guess_from_name(dep_name);
    //             match claim_type {
    //                 ClaimType::Lemma => build_lemma_call.clone()(dep_name),
    //                 ClaimType::Relation => build_relation_call(dep_name),
    //                 ClaimType::Invariant => unreachable!(),
    //             }
    //         })
    //         .collect();
    //
    //     let postcond_call = match claim.ty {
    //         ClaimType::Lemma => build_lemma_call.clone()(&claim.name),
    //         ClaimType::Relation => build_relation_call(&claim.name),
    //         ClaimType::Invariant => build_invariant_new_call(&claim.name),
    //     };
    //
    //     let mut dependencies_code: Vec<SmtExpr> = vec![
    //         randomness_mapping.into(),
    //         build_invariant_old_call("invariant"),
    //     ];
    //
    //     for dep in dep_calls {
    //         dependencies_code.push(dep)
    //     }
    //
    //     comm.write_smt(crate::writers::smt::exprs::SmtAssert(SmtNot(SmtImplies(
    //         SmtAnd(dependencies_code),
    //         postcond_call,
    //     ))))?;
    //
    //     Ok(())
    // }

    fn oracle_sig_by_exported_name(&'a self, oracle_name: &str) -> Option<&'a OracleSig> {
        let gctx_left = self.left_game_inst_ctx();

        gctx_left
            .game()
            .exports
            .iter()
            .find(|Export(_, sig)| sig.name == oracle_name)
            .and_then(|Export(inst_idx, _)| {
                gctx_left.game().pkgs[*inst_idx]
                    .pkg
                    .oracles
                    .iter()
                    .find(|odef| odef.sig.name == oracle_name)
                    .map(|odef| &odef.sig)
            })
    }

    fn emit_claim_assert(
        &self,
        comm: &mut Communicator,
        oracle_name: &str,
        claim: &Claim,
    ) -> Result<()> {
        let gctx_left = self.left_game_inst_ctx();
        let gctx_right = self.right_game_inst_ctx();

        let game_inst_name_left = self.equivalence.left_name();
        let game_inst_name_right = self.equivalence.right_name();

        let game_name_left = gctx_left.game().name();
        let game_name_right = gctx_right.game().name();

        let game_params_left = &gctx_left.game_inst().consts;
        let game_params_right = &gctx_right.game_inst().consts;

        let octx_left = gctx_left.exported_oracle_ctx_by_name(oracle_name).unwrap();
        let octx_right = gctx_right.exported_oracle_ctx_by_name(oracle_name).unwrap();

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
        };

        let right_return = patterns::ReturnConst {
            game_inst_name: game_inst_name_right,
            game_name: game_name_right,
            game_params: game_params_right,
            pkg_name: pkg_name_right,
            pkg_params: pkg_params_right,
            oracle_name,
        };

        let state_left = octx_left.oracle_arg_game_state_pattern();
        let state_right = octx_right.oracle_arg_game_state_pattern();

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

        let build_invariant_new_call = |name: &str| -> SmtExpr {
            (
                name,
                &state_left.new_global_const_name(game_inst_name_left, oracle_name.to_string()),
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
                    ClaimType::Invariant => unreachable!(),
                }
            })
            .collect();

        let postcond_call = match claim.ty {
            ClaimType::Lemma => build_lemma_call.clone()(&claim.name),
            ClaimType::Relation => build_relation_call(&claim.name),
            ClaimType::Invariant => build_invariant_new_call(&claim.name),
        };

        let randomness_mapping = SmtForall {
            bindings: vec![
                ("randmap-sample-id-left".into(), "SampleId".into()),
                (
                    "randmap-sample-ctr-left".into(),
                    Type::from_kind(TypeKind::Integer).into(),
                ),
                ("randmap-sample-id-right".into(), "SampleId".into()),
                (
                    "randmap-sample-ctr-right".into(),
                    Type::from_kind(TypeKind::Integer).into(),
                ),
            ],
            body: (
                "=>",
                (
                    format!("randomness-mapping-{oracle_name}"),
                    (
                        format!("get-rand-ctr-{game_inst_name_left}"),
                        "randmap-sample-id-left",
                    ),
                    (
                        format!("get-rand-ctr-{game_inst_name_right}"),
                        "randmap-sample-id-right",
                    ),
                    "randmap-sample-id-left",
                    "randmap-sample-id-right",
                    "randmap-sample-ctr-left",
                    "randmap-sample-ctr-right",
                ),
                (
                    "rand-is-eq",
                    "randmap-sample-id-left",
                    "randmap-sample-id-right",
                    "randmap-sample-ctr-left",
                    "randmap-sample-ctr-right",
                ),
            ),
        };

        let mut dependencies_code: Vec<SmtExpr> = vec![
            randomness_mapping.into(),
            build_invariant_old_call("invariant"),
        ];

        for dep in dep_calls {
            dependencies_code.push(dep)
        }

        comm.write_smt(crate::writers::smt::exprs::SmtAssert(SmtNot(SmtImplies(
            SmtAnd(dependencies_code),
            postcond_call,
        ))))?;

        Ok(())
    }

    fn types(&self) -> Vec<Type> {
        let (_, (types_left, _)) = self
            .auxs
            .iter()
            .find(|(name, _aux)| name == self.equivalence().left_name())
            .unwrap();
        let (_, (types_right, _)) = self
            .auxs
            .iter()
            .find(|(name, _aux)| name == self.equivalence().right_name())
            .unwrap();
        let types_theorem: HashSet<Type> = self
            .theorem()
            .consts
            .iter()
            .filter_map(|(name, ty)| match ty.kind() {
                TypeKind::Integer => Some(Type::from_kind(TypeKind::Bits(CountSpec::Identifier(
                    Box::new(Identifier::TheoremIdentifier(TheoremIdentifier::Const(
                        TheoremConstIdentifier {
                            theorem_name: self.theorem().name.clone(),
                            name: name.clone(),
                            ty: Type::from_kind(TypeKind::Integer),
                            inst_info: None,
                        },
                    ))),
                )))),
                _ => None,
            })
            .collect();

        let mut types: Vec<_> = types_left
            .union(types_right)
            .cloned()
            .collect::<HashSet<_>>()
            .union(&types_theorem)
            .cloned()
            .collect();
        types.sort();
        types
    }

    fn sample_info_left(self) -> &'a SampleInfo {
        let (_, (_, sample_info)) = self
            .auxs
            .iter()
            .find(|(name, _aux)| name == self.equivalence().left_name())
            .unwrap();
        sample_info
    }

    fn sample_info_right(self) -> &'a SampleInfo {
        let (_, (_, sample_info)) = self
            .auxs
            .iter()
            .find(|(name, _aux)| name == self.equivalence().right_name())
            .unwrap();
        sample_info
    }

    // fn split_info_left(&self) -> &'a Vec<SplitInfoEntry> {
    //     let aux_resolver = SliceResolver(self.auxs);
    //     let (_, (_, _, split_info)) = aux_resolver
    //         .resolve_value(self.equivalence.left_name())
    //         .unwrap();
    //     split_info
    // }
    //
    // fn split_info_right(&self) -> &'a Vec<SplitInfoEntry> {
    //     let aux_resolver = SliceResolver(self.auxs);
    //     let (_, (_, _, split_info)) = aux_resolver
    //         .resolve_value(self.equivalence.right_name())
    //         .unwrap();
    //     split_info
    // }

    fn verify_exports_match(&self) -> (Vec<OracleSig>, Vec<OracleSig>) {
        let left_game_inst = self
            .theorem
            .find_game_instance(self.equivalence().left_name())
            .unwrap();
        let right_game_inst = self
            .theorem
            .find_game_instance(self.equivalence().right_name())
            .unwrap();

        let left_exports: HashSet<_> = left_game_inst
            .game()
            .exports
            .iter()
            .map(|Export(_, oracle_sig)| oracle_sig.clone())
            .collect();
        let right_exports: HashSet<_> = right_game_inst
            .game()
            .exports
            .iter()
            .map(|Export(_, oracle_sig)| oracle_sig.clone())
            .collect();

        let only_left: Vec<_> = left_exports
            .iter()
            .filter(|sig| {
                right_exports
                    .iter()
                    .all(|right_sig| sig.name != right_sig.name || !sig.types_match(right_sig))
            })
            .cloned()
            .collect();
        let only_right: Vec<_> = right_exports
            .iter()
            .filter(|sig| {
                left_exports
                    .iter()
                    .all(|left_sig| sig.name != left_sig.name || !sig.types_match(left_sig))
            })
            .cloned()
            .collect();

        (only_left, only_right)
    }

    fn oracle_sequence(&self) -> Vec<&'a OracleSig> {
        let game_inst = self
            .theorem
            .find_game_instance(self.equivalence().left_name())
            .unwrap();

        log::debug!("oracle sequence: {:?}", game_inst.game().exports);

        game_inst
            .game()
            .exports
            .iter()
            .map(|Export(_, oracle_sig)| oracle_sig)
            .collect()
    }

    // fn split_oracle_sequence(&self) -> Vec<&'a SplitOracleSig> {
    //     let game_inst = SliceResolver(self.theorem.instances())
    //         .resolve_value(self.equivalence.left_name())
    //         .unwrap();
    //
    //     println!("oracle sequence: {:?}", game_inst.game().exports);
    //
    //     game_inst
    //         .game()
    //         .split_exports
    //         .iter()
    //         .map(|SplitExport(_, split_oracle_sig)| split_oracle_sig)
    //         .collect()
    // }

    /// Returns an iterator of all the package const datatypes that need to be defined for this
    /// equivalence theorem. It makes sure to skip duplicate definitions, which may occur if a
    /// package is used more than once.
    pub(crate) fn smt_package_const_definitions(self) -> impl Iterator<Item = SmtExpr> + 'a {
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
    pub(crate) fn smt_package_state_definitions(self) -> impl Iterator<Item = SmtExpr> + 'a {
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
    pub(crate) fn smt_package_return_definitions(self) -> impl Iterator<Item = SmtExpr> + 'a {
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
    pub(crate) fn smt_game_state_definitions(self) -> impl Iterator<Item = SmtExpr> + 'a {
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
    pub(crate) fn smt_theorem_const_definition(self) -> impl Iterator<Item = SmtExpr> + 'a {
        let pattern = self.datastructure_theorem_consts_pattern();
        let spec = pattern.datastructure_spec(self.theorem());

        Some(declare_datatype(&pattern, &spec)).into_iter()
    }

    /// Returns an iterator of all the game const datatypes that need to be defined for this
    /// equivalence theorem. It makes sure to skip duplicate definitions, which may occur if a
    /// package is used more than once.
    pub(crate) fn smt_game_const_definitions(self) -> impl Iterator<Item = SmtExpr> + 'a {
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
        self,
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
        self,
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

    pub(crate) fn smt_oracle_function_definitions(self) -> impl Iterator<Item = SmtExpr> + 'a {
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

    pub fn smt_define_randctr_function(
        &self,
        game_inst: &GameInstance,
        sample_info: &SampleInfo,
    ) -> SmtExpr {
        let gctx = GameInstanceContext::new(game_inst);
        let game = game_inst.game();
        let game_inst_name = game_inst.name();
        let game_name = &game.name;
        let params = &game_inst.consts;

        let state_name = gctx
            .oracle_arg_game_state_pattern()
            .old_global_const_name(game_inst_name);

        let pattern = patterns::GameStatePattern { game_name, params };
        let info = patterns::GameStateDeclareInfo {
            game_inst,
            sample_info,
        };

        let spec = pattern.datastructure_spec(&info);
        let (_, selectors) = &spec.0[0];

        let mut body = SmtExpr::Atom("0".to_string());

        for selector in selectors {
            body = match selector {
                patterns::GameStateSelector::Randomness { sample_pos } => SmtIte {
                    cond: ("=", "sampleid", sample_pos.as_ref()),
                    then: (pattern.selector_name(selector), state_name.clone()),
                    els: body,
                }
                .into(),
                _ => body,
            };
        }

        (
            "define-fun",
            format!("get-rand-ctr-{game_inst_name}"),
            (("sampleid", "SampleId"),),
            "Int",
            body,
        )
            .into()
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
                    Type::from_kind(TypeKind::Bits(count_spec))
                }
                kind => Type::from_kind(kind),
            }
        }

        let left_positions = &self.sample_info_left().positions;
        let right_positions = &self.sample_info_right().positions;

        let left_types: HashSet<Type> = HashSet::from_iter(
            self.sample_info_left()
                .tys
                .iter()
                .cloned()
                .map(type_use_theorem_ident),
        );
        let right_types: HashSet<Type> = HashSet::from_iter(
            self.sample_info_right()
                .tys
                .iter()
                .cloned()
                .map(type_use_theorem_ident),
        );

        let types: Vec<&Type> = left_types.intersection(&right_types).collect();

        let mut left_positions_by_type: HashMap<_, Vec<_>> = HashMap::new();
        let mut right_positions_by_type: HashMap<_, Vec<_>> = HashMap::new();

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
                ("sample-ctr-left", Type::from_kind(TypeKind::Integer)),
                ("sample-ctr-right", Type::from_kind(TypeKind::Integer)),
            ),
            "Bool",
            body,
        )
            .into()
    }
}

// ResolvedEquivalence contains the composisitions/games and the invariant data,
// whereas the pure Equivalence just contains the names and file paths.
// TODO: explore if we can keep references to the games in the project hashmap

fn build_returns(game_inst: &GameInstance) -> Vec<(SmtExpr, SmtExpr)> {
    let gctx = contexts::GameInstanceContext::new(game_inst);
    let game_name = &game_inst.game().name;
    let game_inst_name = &game_inst.name();
    let game_params = &game_inst.consts;

    // write declarations of right return constants and constrain them
    let mut out = vec![];
    for Export(inst_idx, sig) in &game_inst.game().exports {
        let pkg_inst = &game_inst.game().pkgs[*inst_idx];

        let pkg_inst_name = &pkg_inst.name;
        let pkg_params = &pkg_inst.params;
        let pkg_name = &pkg_inst.pkg.name;
        let oracle_name = &sig.name;
        let return_type = &sig.ty;

        let octx = gctx
            .exported_oracle_ctx_by_name(&sig.name)
            .unwrap_or_else(|| {
                panic!(
                    "error looking up exported oracle with name {oracle_name} in game {game_name}"
                )
            });

        let return_const = patterns::ReturnConst {
            game_inst_name,
            game_name,
            game_params,
            pkg_name,
            pkg_params,
            oracle_name,
        };

        let return_value_const = patterns::ReturnValueConst {
            game_inst_name,
            pkg_inst_name,
            oracle_name,
            ty: &sig.ty,
        };

        let is_abort_const_pattern = ReturnIsAbortConst {
            game_inst_name,
            pkg_inst_name,
            oracle_name,
            ty: &sig.ty,
        };

        let state = octx.oracle_arg_game_state_pattern();
        let consts = octx.oracle_arg_game_consts_pattern();

        let old_state_const = state.old_global_const_name(game_inst_name);
        let new_state_const = state.new_global_const_name(game_inst_name, oracle_name.to_string());
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
            state.declare_new(game_inst_name, oracle_name.to_string()),
            constrain_new_state.into(),
        ));
    }

    out
}

fn build_rands(
    sample_info: &SampleInfo,
    game_inst: &GameInstance,
) -> Vec<(SmtExpr, SmtExpr, SmtExpr, SmtExpr)> {
    let gctx = contexts::GameInstanceContext::new(game_inst);

    sample_info
        .positions
        .iter()
        .map(|sample_item| {
            let sample_id = sample_item.sample_id;
            let ty = &sample_item.ty;
            let game_inst_name = game_inst.name();

            let state = gctx
                .oracle_arg_game_state_pattern()
                .old_global_const_name(game_inst_name);

            let randctr_name = format!("randctr-{game_inst_name}-{sample_id}");
            let randval_name = format!("randval-{game_inst_name}-{sample_id}");

            let decl_randctr = declare::declare_const(randctr_name.clone(), Sort::Int);
            let decl_randval = declare::declare_const(randval_name.clone(), ty.clone().into());

            // pull randomness counter for given sample_id out of the gamestate
            let randctr = gctx
                .smt_access_gamestate_rand(sample_info, state, sample_id)
                .unwrap();

            let constrain_randctr: SmtExpr = SmtAssert(SmtEq2 {
                lhs: randctr_name.as_str(),
                rhs: randctr.clone(),
            })
            .into();

            // apply respective randomness function (based on type) to the given counter
            let randval = gctx.smt_eval_randfn(sample_item, ("+", 0, randctr_name.as_str()), ty);

            let constrain_randval: SmtExpr = SmtAssert(SmtEq2 {
                lhs: randval_name,
                rhs: randval,
            })
            .into();

            (
                decl_randctr,
                constrain_randctr,
                decl_randval,
                constrain_randval,
            )
        })
        .collect()
}
