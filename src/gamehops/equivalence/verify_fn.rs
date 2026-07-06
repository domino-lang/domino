// SPDX-License-Identifier: MIT OR Apache-2.0

use rayon::iter::{IntoParallelRefIterator, ParallelIterator};
use std::io::Write as _;
use std::sync::{Arc, Mutex};

use crate::{
    gamehops::equivalence::error::{ClaimTheoremFailedError, Error, Result},
    package::Export,
    project::Project,
    theorem::Claim,
    ui::TheoremUI,
    util::smtsolver::{SmtSolver, SmtSolverBackend, SmtSolverResponse},
    writers::smt::{contexts::EquivalenceContext, exprs::SmtExpr},
};

const INITIAL_STATE_UI_NAME: &str = "invariants in initial state";
const INITIAL_STATE_TRANSCRIPT_NAME: &str = "initial-state";
const INITIAL_INVARIANT_CLAIM_NAME: &str = "invariant";

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
        /* We pick invariants of the first exported oracle but this needs to be changed 
        so that only one set of invariants can be defined for an equivalence but 
        each oracle can define its own randomness mappings. */
        let initial_invariant_source_oracle = oracle_sequence.first().map(|oracle| oracle.name());

        ui.lock().unwrap().proofstep_set_oracles(
            &self.eqctx.theorem().name,
            &proofstep_name,
            (oracle_sequence.len() + usize::from(initial_invariant_source_oracle.is_some()))
                .try_into()
                .unwrap(),
        );

        let mut failed_oracles: Vec<_> = match self.verify_initial_invariant(
            ui.clone(),
            &smt,
            initial_invariant_source_oracle,
        ) {
            Ok(()) => vec![],
            Err(err) => vec![err],
        };

        failed_oracles.extend(
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
                .into_iter()
                .filter_map(Result::err)
                .collect::<Vec<_>>(),
        );
        if !failed_oracles.is_empty() {
            return Err(Error::ParallelEquivalenceError {
                left_game_inst_name: eq.left_name.clone(),
                right_game_inst_name: eq.right_name.clone(),
                failed_oracles,
            });
        }
        Ok(())
    }

    fn verify_initial_invariant<UI: TheoremUI + Send>(
        &self,
        ui: Arc<Mutex<&mut UI>>,
        equivalence_smt: &[SmtExpr],
        invariant_source_oracle: Option<&str>,
    ) -> Result<()> {
        let Some(invariant_source_oracle) = invariant_source_oracle else {
            return Ok(());
        };

        let eq = self.eqctx.equivalence();
        let proofstep_name = format!("{} == {}", eq.left_name(), eq.right_name());

        ui.lock().unwrap().start_oracle(
            &self.eqctx.theorem().name,
            &proofstep_name,
            INITIAL_STATE_UI_NAME,
            1,
        );
        ui.lock().unwrap().start_lemma(
            &self.eqctx.theorem().name,
            &proofstep_name,
            INITIAL_STATE_UI_NAME,
            INITIAL_INVARIANT_CLAIM_NAME,
        );

        let mut solver = {
            if self.transcript {
                let transcript_file: std::fs::File = self
                    .project
                    .get_joined_smt_file(
                        eq.left_name(),
                        eq.right_name(),
                        INITIAL_STATE_TRANSCRIPT_NAME,
                        INITIAL_INVARIANT_CLAIM_NAME,
                    )
                    .unwrap();

                self.backend
                    .new_smtsolver_with_transcript(transcript_file)?
            } else {
                self.backend.new_smtsolver()?
            }
        };

        for entry in equivalence_smt {
            solver.write_smt(entry.clone())?;
        }
        for entry in self.eqctx.emit_invariant(invariant_source_oracle) {
            solver.write_smt(entry)?;
        }
        for entry in self.eqctx.emit_initial_state_values() {
            solver.write_smt(entry)?;
        }
        solver.write_smt(self.eqctx.emit_initial_invariant_claim())?;

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
                    claim_name: INITIAL_INVARIANT_CLAIM_NAME.to_string(),
                    oracle_name: INITIAL_STATE_UI_NAME.to_string(),
                    response,
                    modelfile,
                }
                .into());
            }
        }

        ui.lock().unwrap().finish_lemma(
            &self.eqctx.theorem().name,
            &proofstep_name,
            INITIAL_STATE_UI_NAME,
            INITIAL_INVARIANT_CLAIM_NAME,
        );
        ui.lock().unwrap().finish_oracle(
            &self.eqctx.theorem().name,
            &proofstep_name,
            INITIAL_STATE_UI_NAME,
        );

        Ok(())
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
                self.verify_claim(ui.clone(), equivalence_smt, &smt, oracle, claim)
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
        oracle: &Export,
        claim: &Claim,
    ) -> Result<()> {
        let eq = self.eqctx.equivalence();
        let proofstep_name = format!("{} == {}", eq.left_name(), eq.right_name());
        ui.lock().unwrap().start_lemma(
            &self.eqctx.theorem().name,
            &proofstep_name,
            oracle.name(),
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
                            oracle.name(),
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
            solver.write_smt(self.eqctx.emit_claim_assert(oracle.name(), claim))?;

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
                        oracle_name: oracle.name().to_string(),
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
            oracle.name(),
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
