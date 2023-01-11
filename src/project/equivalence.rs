use crate::package::{Composition, Export};
use crate::transforms::samplify::SampleInfo;
use crate::util::prover_process::{Communicator, ProverResponse};
use crate::writers::smt::exprs::{SmtAnd, SmtAssert, SmtEq2, SmtExpr, SmtImplies, SmtNot};
use crate::writers::smt::writer::CompositionSmtWriter;
use crate::writers::smt::{contexts, declare};
use crate::{hacks, types};
use crate::{
    project::error::{Error, Result},
    types::Type,
};

use std::collections::{HashMap, HashSet};
use std::fmt::{Display, Write};
use std::io::Write as IOWrite;
use std::iter::FromIterator;

use serde_derive::{Deserialize, Serialize};

use super::load::ProofTreeSpec;

#[derive(Debug, Serialize, Deserialize)]
pub struct Equivalence {
    pub left: String,
    pub right: String,
    pub invariant_path: String,
    pub trees: HashMap<String, ProofTreeSpec>,
}

// ResolvedEquivalence contains the composisitions/games and the invariant data,
// whereas the pure Equivalence just contains the names and file paths.
// TODO: explore if we can keep references to the games in the project hashmap
pub struct ResolvedEquivalence {
    pub left: Composition,
    pub right: Composition,
    pub invariant: String,
    pub trees: HashMap<String, ProofTreeSpec>,

    pub left_decl_smt_file: std::fs::File,
    pub right_decl_smt_file: std::fs::File,
    pub base_decl_smt_file: std::fs::File,
    pub const_decl_smt_file: std::fs::File,
    pub epilogue_smt_file: std::fs::File,
    pub joined_smt_file: std::fs::File,
}

impl ResolvedEquivalence {
    pub fn prove(&mut self) -> Result<()> {
        //let context = ProofContext::new(self);
        let ResolvedEquivalence {
            left,
            right,
            invariant,

            left_decl_smt_file,
            right_decl_smt_file,
            base_decl_smt_file,
            const_decl_smt_file,
            epilogue_smt_file,
            joined_smt_file,

            trees,
        } = self;

        // check that the parameters shared by both are of the same type
        check_matching_parameters(left, right)?;

        // apply transformations
        let (ref left, _, types_left, samp_left) = crate::transforms::transform_all(&left).unwrap();
        let (ref right, _, types_right, samp_right) =
            crate::transforms::transform_all(&right).unwrap();

        // get bits types
        let mut bits_types: Vec<_> = types_left
            .union(&types_right)
            .filter_map(|t| match t {
                Type::Bits(x) => Some(x.clone()),
                _ => None,
            })
            .collect();
        bits_types.sort();

        // prepare the buffer for the data we send to the prover
        let mut base_declarations = String::new();
        let mut left_declarations = String::new();
        let mut rght_declarations = String::new();

        // write logic to us
        write!(base_declarations, "(set-logic ALL)\n")?;

        // write bits types declarations
        for id in bits_types {
            write!(base_declarations, "{}", hacks::BitsDeclaration(id))?;
        }

        // write other type declarations
        write!(base_declarations, "{}", hacks::MaybeDeclaration)?;
        write!(base_declarations, "{}", hacks::TuplesDeclaration(1..32))?;
        write!(base_declarations, "{}", hacks::EmptyDeclaration)?;

        //
        let gctx_left = contexts::GameContext::new(&left);
        let gctx_right = contexts::GameContext::new(&right);

        // write left game code
        let mut left_writer = CompositionSmtWriter::new(&left, &samp_left);
        for line in left_writer.smt_composition_all() {
            writeln!(left_declarations, "{line}")?;
        }

        // write right game code
        let mut right_writer = CompositionSmtWriter::new(&right, &samp_right);
        for line in right_writer.smt_composition_all() {
            writeln!(rght_declarations, "{line}")?;
        }

        //// Declarations
        let mut const_declarations = String::new();

        // write declaration of left (old) state constant
        let decl_state_left =
            declare::declare_const("state-left".to_string(), gctx_left.smt_sort_gamestates());

        // write declaration of right (old) state constant
        let decl_state_right =
            declare::declare_const("state-right".to_string(), gctx_right.smt_sort_gamestates());

        writeln!(const_declarations, "{decl_state_left}")?;
        writeln!(const_declarations, "{decl_state_right}")?;

        // write declarations of state lengths
        let state_length_left_old = "state-length-left-old";
        let state_length_left_new = "state-length-left-new";
        let state_length_right_old = "state-length-right-old";
        let state_length_right_new = "state-length-right-new";
        let state_lengths = &[
            state_length_left_old,
            state_length_left_new,
            state_length_right_old,
            state_length_right_new,
        ];

        for state_length in state_lengths {
            let decl_state_length =
                declare::declare_const(state_length.to_string(), types::Type::Integer);
            write!(const_declarations, "{decl_state_length}")?;
        }

        // write declarations of arguments
        for Export(_, sig) in &left.exports {
            let oracle_name = &sig.name;
            for (arg_name, arg_type) in &sig.args {
                let decl_arg =
                    declare::declare_const(format!("arg-{oracle_name}-{arg_name}"), arg_type);
                write!(const_declarations, "{decl_arg}")?;
            }
        }

        for (decl_ret, constrain) in build_returns(&left, Side::Left) {
            write!(const_declarations, "{decl_ret}")?;
            write!(const_declarations, "{constrain}")?;
        }

        for (decl_ret, constrain) in build_returns(&right, Side::Right) {
            write!(const_declarations, "{decl_ret}")?;
            write!(const_declarations, "{constrain}")?;
        }

        for (decl_ctr, assert_ctr, decl_val, assert_val) in
            build_rands(&samp_left, left, Side::Left)
        {
            write!(const_declarations, "{decl_ctr}")?;
            write!(const_declarations, "{assert_ctr}")?;
            write!(const_declarations, "{decl_val}")?;
            write!(const_declarations, "{assert_val}")?;
        }

        for (decl_ctr, assert_ctr, decl_val, assert_val) in
            build_rands(&samp_right, right, Side::Right)
        {
            write!(const_declarations, "{decl_ctr}")?;
            write!(const_declarations, "{assert_ctr}")?;
            write!(const_declarations, "{decl_val}")?;
            write!(const_declarations, "{assert_val}")?;
        }

        // write epilogue code
        let mut epilogue = Vec::new();
        for (oracle_name, tree) in trees {
            let sig = left
                .exports
                .iter()
                .find(|Export(_, sig)| &sig.name == oracle_name)
                .map(|Export(_, sig)| sig)
                .unwrap();

            let args: Vec<_> = sig
                .args
                .iter()
                .map(|(arg_name, _)| format!("arg-{oracle_name}-{arg_name}"))
                .collect();

            // find the package instance which is marked as exporting
            // the oracle of this name, both left and right.
            let left_return_name = left
                .exports
                .iter()
                .find(|Export(_, sig)| &sig.name == oracle_name)
                .map(|Export(inst_idx, _)| {
                    let inst_name = &left.pkgs[*inst_idx].name;
                    format!("return-left-{inst_name}-{oracle_name}")
                })
                .unwrap();

            let right_return_name = right
                .exports
                .iter()
                .find(|Export(_, sig)| &sig.name == oracle_name)
                .map(|Export(inst_idx, _)| {
                    let inst_name = &right.pkgs[*inst_idx].name;
                    format!("return-right-{inst_name}-{oracle_name}")
                })
                .unwrap();

            // this helper builds an smt expression that calls the
            // function with the given name with the old states,
            // return values and the respective arguments.
            // We expect that function to return a boolean, which makes
            // it a relation.
            let build_lemma_call = |name: String| {
                let mut tmp: Vec<SmtExpr> = vec![
                    name.into(),
                    "state-left".into(),
                    "state-right".into(),
                    "state-length-left-old".into(),
                    "state-length-right-old".into(),
                    left_return_name.clone().into(),
                    right_return_name.clone().into(),
                ];

                for arg in &args {
                    tmp.push(arg.clone().into());
                }

                SmtExpr::List(tmp)
            };

            /*
            implicint deps:
            - randomness mapping
            - invariant holds on old state

            (push 1)
            (assert (not (=>
                (and
                    (implicit dependencies)
                    (explicit dependencies)
                )
                (current lemma)
            )))
            (check-sat)
            (pop 1)
            */

            for (lemma_name, deps) in tree {
                let mut lemma_code = String::new();

                writeln!(lemma_code, "; oracle {oracle_name}, lemma {lemma_name}")?;

                let mut dependencies_code: Vec<SmtExpr> = vec![
                    format!("randomness-mapping-{oracle_name}").into(),
                    build_lemma_call(format!("invariant-{oracle_name}")),
                ];

                for dep_name in deps {
                    dependencies_code.push(build_lemma_call(dep_name.clone()))
                }

                let code: Vec<SmtExpr> = vec![
                    ("push", "1").into(),
                    crate::writers::smt::exprs::SmtAssert(SmtNot(SmtImplies(
                        SmtAnd(dependencies_code),
                        build_lemma_call(lemma_name.clone()),
                    )))
                    .into(),
                    ("check-sat",).into(),
                    ("pop", "1").into(),
                ];

                for line in code {
                    write!(lemma_code, "{line}")?;
                }

                epilogue.push((oracle_name, lemma_name, lemma_code))
            }
        }

        // write data to files
        write!(base_decl_smt_file, "{base_declarations}")?;
        write!(left_decl_smt_file, "{left_declarations}")?;
        write!(right_decl_smt_file, "{rght_declarations}")?;

        write!(const_decl_smt_file, "{const_declarations}")?;

        for (_, _, code) in &epilogue {
            write!(epilogue_smt_file, "{code}")?;
        }

        // start talking to prover

        let mut prover_comm =
            Communicator::new_cvc5_with_transcript(joined_smt_file.try_clone().unwrap())?;

        write!(prover_comm, "{base_declarations}")?;
        write!(prover_comm, "{left_declarations}")?;
        write!(prover_comm, "{rght_declarations}")?;

        println!("sent definitions, waiting for sat... ");
        expect_sat(&mut prover_comm)?;
        println!("received.");

        write!(prover_comm, "{const_declarations}")?;

        println!("sent declarations and basic constraints, waiting for sat... ");
        expect_sat(&mut prover_comm)?;
        println!("received.");

        write!(prover_comm, "{invariant}").unwrap();

        println!("sent invariant, waiting for sat... ");
        expect_sat(&mut prover_comm)?;
        println!("received.");

        for (oracle_name, lemma_name, epilogue_code) in &epilogue {
            write!(prover_comm, "{epilogue_code}").unwrap();

            println!("sent code for lemma {oracle_name}/{lemma_name}, waiting for response... (expecting unsat)");
            expect_unsat(&mut prover_comm)?;
            println!("received.");
        }

        prover_comm.close();
        let rest = prover_comm.read_until_end()?;

        println!("sent everything, now receiving rest:\n{rest}");

        prover_comm.join()?;

        Ok(())
    }
}

fn expect_sat(comm: &mut Communicator) -> Result<()> {
    match comm.check_sat()? {
        ProverResponse::Sat => Ok(()),
        resp => Err(Error::UnexpectedProverResponseError(
            resp,
            ProverResponse::Sat,
        )),
    }
}

fn expect_unsat(comm: &mut Communicator) -> Result<()> {
    match comm.check_sat()? {
        ProverResponse::Unsat => Ok(()),
        resp => Err(Error::UnexpectedProverResponseError(
            resp,
            ProverResponse::Unsat,
        )),
    }
}

// This function gets the parameter names that both have and checks that
// both use the same types.
// The invariant should be used to make assertions on equality or other
// relations between the two.
//
// TODO figure out if there is a better mechanism we could use here
fn check_matching_parameters(left: &Composition, right: &Composition) -> Result<()> {
    use std::collections::hash_map::RandomState;

    // populate tables name -> type
    let left_params: HashMap<_, _, RandomState> =
        HashMap::from_iter(left.consts.clone().into_iter());
    let right_params: HashMap<_, _, RandomState> =
        HashMap::from_iter(right.consts.clone().into_iter());

    // prepare sets of names
    let left_params_set = HashSet::<_, RandomState>::from_iter(left_params.keys());
    let right_params_set = HashSet::<_, RandomState>::from_iter(right_params.keys());
    let common_params = left_params_set.intersection(&right_params_set);

    // check that the common params have the same type
    for param in common_params {
        if left_params[*param] != right_params[*param] {
            return Err(Error::CompositionParamMismatch(
                left.name.clone(),
                right.name.clone(),
                (*param).clone(),
            ));
        }
    }

    Ok(())
}

fn oracle_arg_name(oracle_name: &str, arg_name: &str) -> String {
    format!("arg-{oracle_name}-{arg_name}")
}

fn build_returns(game: &Composition, game_side: Side) -> Vec<(SmtExpr, SmtExpr)> {
    let gctx = contexts::GameContext::new(game);

    // write declarations of right return constants and constrain them
    game.exports
        .iter()
        .map(|Export(inst_idx, sig)| {
            let octx = gctx.exported_oracle_ctx_by_name(&sig.name).unwrap();

            let inst_name = &game.pkgs[*inst_idx].name;
            let oracle_name = &sig.name;
            let return_name = format!("return-{game_side}-{inst_name}-{oracle_name}");

            let decl_return = declare::declare_const(return_name.clone(), octx.smt_sort_return());

            let args = sig
                .args
                .iter()
                .map(|(arg_name, _)| oracle_arg_name(oracle_name, arg_name).into());

            let invok = octx
                .smt_invoke_oracle(
                    format!("state-{game_side}"),
                    format!("state-length-{game_side}-old"),
                    args,
                )
                .unwrap();

            let constrain_return: SmtExpr = SmtAssert(SmtEq2 {
                lhs: return_name,
                rhs: invok,
            })
            .into();

            (decl_return, constrain_return)
        })
        .collect()
}

fn build_rands(
    sample_info: &SampleInfo,
    game: &Composition,
    game_side: Side,
) -> Vec<(SmtExpr, SmtExpr, SmtExpr, SmtExpr)> {
    let gctx = contexts::GameContext::new(game);

    sample_info
        .positions
        .iter()
        .map(|sample_item| {
            let ictx = gctx.pkg_inst_ctx_by_name(&sample_item.inst_name).unwrap();

            let sample_id = sample_item.sample_id;
            let tipe = &sample_item.tipe;

            let states = format!("state-{game_side}");
            let states_len = format!("state-length-{game_side}-old");
            let state = ("select", states, states_len);

            let randctr_name = format!("randctr-{game_side}-{sample_id}");
            let randval_name = format!("randval-{game_side}-{sample_id}");

            let decl_randctr = declare::declare_const(randctr_name.clone(), Type::Integer);
            let decl_randval = declare::declare_const(randval_name.clone(), tipe);

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
            let randval = gctx.smt_eval_randfn(sample_id, ("+", 0, randctr_name.as_str()), tipe);

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

enum Side {
    Left,
    Right,
}

impl Display for Side {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Side::Left => write!(f, "left"),
            Side::Right => write!(f, "right"),
        }
    }
}
