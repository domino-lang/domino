// SPDX-License-Identifier: MIT OR Apache-2.0

use rayon::iter::{IntoParallelRefIterator, ParallelIterator};
use std::io::Write as _;
use std::sync::{Arc, Mutex};

use crate::{
    gamehops::equivalence::error::{ClaimTheoremFailedError, Error, Result},
    package::Export,
    project::Project,
    theorem::{Claim, ClaimType},
    ui::TheoremUI,
    util::smtsolver::{SmtSolver, SmtSolverBackend, SmtSolverResponse},
    writers::smt::{contexts::EquivalenceContext, exprs::SmtExpr},
};

pub(crate) struct EquivalenceSmtDriver<'a, Backend: SmtSolverBackend + Sync, Proj: Project + Sync> {
    eqctx: &'a EquivalenceContext<'a>,
    project: &'a Proj,
    backend: &'a Backend,
    transcript: bool,
    req_oracle: Option<&'a str>,
    parallel: usize,
}

impl<'a, Backend: SmtSolverBackend + Sync, Proj: Project + Sync>
    EquivalenceSmtDriver<'a, Backend, Proj>
{
    pub(crate) fn new(
        eqctx: &'a EquivalenceContext<'a>,
        project: &'a Proj,
        backend: &'a Backend,
        transcript: bool,
        req_oracle: Option<&'a str>,
        parallel: usize,
    ) -> Self {
        Self {
            eqctx,
            project,
            backend,
            transcript,
            req_oracle,
            parallel,
        }
    }

    pub(crate) fn verify<UI: TheoremUI + Send>(&mut self, ui: &mut UI) -> Result<()> {
        self.eqctx.verify_exports_match()?;

        let ui = Arc::new(Mutex::new(ui));
        self.verify_equivalence(ui)
    }

    fn verify_equivalence<UI: TheoremUI + Send>(&self, ui: Arc<Mutex<&mut UI>>) -> Result<()> {
        let eq = self.eqctx.equivalence();
        let mut smt = Vec::new();

        log::debug!(
            "emitting base declarations for {}-{}",
            eq.left_name,
            eq.right_name
        );
        smt.push(SmtExpr::Comment("\n".to_string()));
        smt.push(SmtExpr::Comment("base declarations:\n".to_string()));
        smt.append(&mut self.eqctx.emit_base_declarations());
        log::debug!(
            "emitting theorem paramfuncs for {}-{}",
            eq.left_name,
            eq.right_name
        );
        smt.push(SmtExpr::Comment("\n".to_string()));
        smt.push(SmtExpr::Comment("theorem param funcs:\n".to_string()));
        smt.extend(&mut self.eqctx.emit_theorem_paramfuncs());
        log::debug!(
            "emitting game definitions for {}-{}",
            eq.left_name,
            eq.right_name
        );
        smt.push(SmtExpr::Comment("\n".to_string()));
        smt.push(SmtExpr::Comment("game definitions:\n".to_string()));
        smt.extend(&mut self.eqctx.emit_game_definitions());

        log::debug!(
            "emitting const declarations for {}-{}",
            eq.left_name,
            eq.right_name
        );
        smt.append(&mut self.eqctx.emit_constant_declarations());

        let proofstep_name = format!("{} == {}", eq.left_name(), eq.right_name());
        let oracle_sequence = self.oracle_sequence();

        ui.lock().unwrap().proofstep_set_oracles(
            &self.eqctx.theorem().name,
            &proofstep_name,
            (oracle_sequence.len() + 1) // 1 is for checking invariants in the initial state
                .try_into()
                .unwrap(),
        );

        let mut claims: Vec<_> = vec![
            self.verify_invariants_in_initial_state(ui.clone(), &smt)
        ];

        claims.extend(
            rayon::ThreadPoolBuilder::new()
                .num_threads(self.parallel + 1) // one process is reserved for the "main" method
                .build()
                .unwrap()
                .install(|| -> Vec<Result<()>> {
                    oracle_sequence
                        .par_iter()
                        .map(|oracle| -> Vec<Result<()>> {
                            self.verify_oracle(ui.clone(), &smt, oracle)
                        })
                        .flatten()
                        .collect()
                })
        );

        let failed_claims = claims
                .into_iter()
                .filter_map(Result::err)
                .collect::<Vec<_>>();
        if !failed_claims.is_empty() {
            return Err(Error::ParallelEquivalenceError {
                left_game_inst_name: eq.left_name.clone(),
                right_game_inst_name: eq.right_name.clone(),
                failed_claims,
            });
        }
        Ok(())
    }

    fn verify_invariants_in_initial_state<UI: TheoremUI + Send>(
        &self,
        ui: Arc<Mutex<&mut UI>>,
        equivalence_smt: &[SmtExpr],
    ) -> Result<()> {
        let mut smt = vec![];
        let eq = self.eqctx.equivalence();
        let proofstep_name = format!("{} == {}", eq.left_name(), eq.right_name());
        let invariant_in_initial_state_claim_name: &str = "invariants-in-initial-state";

        ui.lock().unwrap().start_oracle(
            &self.eqctx.theorem().name,
            &proofstep_name,
            invariant_in_initial_state_claim_name,
            1
        );

        log::info!("verify: invariants in initial state");
        // This is very nasty and we need to have only one set of 
        // invariants for the entire equivalence
        // TODO: give good error instead of unwrap: empty oracle sequence, do we check this before?
        let oracle_name = self.oracle_sequence().first().unwrap().name();
        smt.append(&mut self.eqctx.emit_invariant(oracle_name));
        smt.append(&mut self.eqctx.emit_initial_state_values());

        let claim = Claim {
            name: String::from(invariant_in_initial_state_claim_name),
            dependencies: vec![],
            ty: ClaimType::InvariantInInitialState,
            admitted: false
        };

        let result = self.verify_claim(
            ui.clone(), equivalence_smt, &smt, oracle_name, &claim);

        ui.lock().unwrap().finish_oracle(
            &self.eqctx.theorem().name,
            &proofstep_name,
            invariant_in_initial_state_claim_name,
        );

        result
    }

    fn verify_oracle<UI: TheoremUI + Send>(
        &self,
        ui: Arc<Mutex<&mut UI>>,
        equivalence_smt: &[SmtExpr],
        oracle: &Export,
    ) -> Vec<Result<()>> {
        let mut smt = Vec::new();
        let eq = self.eqctx.equivalence();
        let proofstep_name = format!("{} == {}", eq.left_name(), eq.right_name());

        let claims = self
            .eqctx
            .equivalence()
            .proof_tree_by_oracle_name(oracle.name());
        ui.lock().unwrap().start_oracle(
            &self.eqctx.theorem().name,
            &proofstep_name,
            oracle.name(),
            claims.len().try_into().unwrap(),
        );

        log::info!("verify: oracle:{oracle:?}");
        smt.extend(&mut self.eqctx.emit_return_value_helpers(oracle.name()));
        smt.append(&mut self.eqctx.emit_auto_randomness(oracle.name()));
        smt.append(&mut self.eqctx.emit_invariant(oracle.name()));

        let result: Vec<_> = claims
            .par_iter()
            .map(|claim| -> Result<()> {
                self.verify_claim(ui.clone(), equivalence_smt, &smt, oracle.name(), claim)
            })
            .collect();

        ui.lock().unwrap().finish_oracle(
            &self.eqctx.theorem().name,
            &proofstep_name,
            oracle.name(),
        );

        result
    }

    fn verify_claim<UI: TheoremUI>(
        &self,
        ui: Arc<Mutex<&mut UI>>,
        equivalence_smt: &[SmtExpr],
        oracle_smt: &[SmtExpr],
        oracle_name: &str,
        claim: &Claim,
    ) -> Result<()> {
        let eq = self.eqctx.equivalence();
        let proofstep_name = format!("{} == {}", eq.left_name(), eq.right_name());
        ui.lock().unwrap().start_lemma(
            &self.eqctx.theorem().name,
            &proofstep_name,
            oracle_name,
            claim.name(),
        );

        if !claim.is_admitted() {
            let mut solver = {
                if self.transcript {
                    let transcript_file: std::fs::File = self
                        .project
                        .get_joined_smt_file(
                            eq.left_name(),
                            eq.right_name(),
                            oracle_name,
                            claim.name(),
                        )
                        .unwrap();

                    self.backend
                        .new_smtsolver_with_transcript(transcript_file)?
                } else {
                    self.backend.new_smtsolver()?
                }
            };
            std::thread::sleep(std::time::Duration::from_millis(20));

            for entry in equivalence_smt {
                solver.write_smt(entry.clone())?;
            }
            for entry in oracle_smt {
                solver.write_smt(entry.clone())?;
            }
            solver.write_smt(self.eqctx.emit_claim_assert(oracle_name, claim))?;

            match solver.check_sat()? {
                SmtSolverResponse::Unsat => {}
                response => {
                    let modelfile = solver.get_model().map(|(modelstring, _model)| {
                        let mut modelfile =
                            tempfile::Builder::new().suffix(".smt2").tempfile().unwrap();
                        modelfile.write_all(modelstring.as_bytes()).unwrap();
                        let (_, fname) = modelfile.keep().unwrap();
                        fname
                    });
                    solver.close();
                    return Err(ClaimTheoremFailedError {
                        claim_name: claim.name().to_string(),
                        oracle_name: oracle_name.to_string(),
                        response,
                        modelfile,
                    }
                    .into());
                }
            }
        }
        ui.lock().unwrap().finish_lemma(
            &self.eqctx.theorem().name,
            &proofstep_name,
            oracle_name,
            claim.name(),
        );

        Ok(())
    }

    fn oracle_sequence(&self) -> Vec<&'a Export> {
        self.eqctx
            .oracle_sequence()
            .into_iter()
            .filter(|export| {
                if let Some(name) = self.req_oracle {
                    export.name() == name
                } else {
                    true
                }
            })
            .collect()
    }
}
