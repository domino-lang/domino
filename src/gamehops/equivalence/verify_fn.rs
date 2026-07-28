// SPDX-License-Identifier: MIT OR Apache-2.0

use rayon::iter::{IntoParallelRefIterator, ParallelIterator};
use wildcard::Wildcard;

use std::io::Write as _;
use std::path::PathBuf;
use std::sync::{Arc, Mutex};

use crate::{
    gamehops::equivalence::{
        error::{ClaimTheoremFailedError, Error, Result},
        ClaimType,
    },
    package::Export,
    project::Project,
    theorem::ParsedClaim,
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
    req_claim: Option<Wildcard<'a>>,
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
        req_claim: Option<&'a str>,
        parallel: usize,
    ) -> Self {
        let req_claim = req_claim.map(|req| Wildcard::new(req.as_bytes()).unwrap());
        Self {
            eqctx,
            project,
            backend,
            transcript,
            req_oracle,
            req_claim,
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
            oracle_sequence.len().try_into().unwrap(),
        );

        let failed_oracles: Vec<_> = rayon::ThreadPoolBuilder::new()
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
            .collect();
        if !failed_oracles.is_empty() {
            return Err(Error::ParallelEquivalenceError {
                left_game_inst_name: eq.left_name.clone(),
                right_game_inst_name: eq.right_name.clone(),
                failed_oracles,
            });
        }
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

        let claims: Vec<_> = self
            .eqctx
            .equivalence()
            .proof_tree_by_oracle_name(oracle.name())
            .into_iter()
            .filter(|claim| !claim.is_admitted())
            .chain(self.eqctx.claims(oracle.name()).unwrap().iter().filter_map(
                |smt| match smt.ty() {
                    ClaimType::LeftPackageInvariant
                    | ClaimType::RightPackageInvariant
                    | ClaimType::LeftGameInvariant
                    | ClaimType::RightGameInvariant => Some(ParsedClaim {
                        name: smt.name().to_string(),
                        dependencies: vec!["no-abort".to_string()],
                        admitted: false,
                    }),
                    _ => None,
                },
            ))
            .collect();

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
            .filter(|claim| {
                if let Some(req_claim) = &self.req_claim {
                    req_claim.is_match(claim.name.as_bytes())
                } else {
                    true
                }
            })
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
        claim: &ParsedClaim,
    ) -> Result<()> {
        let eq = self.eqctx.equivalence();
        let proofstep_name = format!("{} == {}", eq.left_name(), eq.right_name());
        ui.lock().unwrap().start_lemma(
            &self.eqctx.theorem().name,
            &proofstep_name,
            oracle.name(),
            claim.name(),
        );

        let mut solver = {
            if self.transcript {
                let transcript_file: std::fs::File = self
                    .project
                    .get_smt_file(
                        eq.theorem_name(),
                        eq.left_name(),
                        eq.right_name(),
                        oracle.name(),
                        claim.name(),
                    )
                    .unwrap();

                self.backend.new_smtsolver_with_transcript(transcript_file)
            } else {
                self.backend.new_smtsolver()
            }
        }
        .map_err(|err| Error::prover_process_error(claim.name(), oracle.name(), err))?;
        std::thread::sleep(std::time::Duration::from_millis(20));

        for entry in equivalence_smt
            .iter()
            .chain(oracle_smt)
            .chain(std::iter::once(
                &self.eqctx.emit_claim_assert(oracle.name(), claim),
            ))
        {
            solver
                .write_smt(entry.clone())
                .map_err(|err| Error::prover_process_error(claim.name(), oracle.name(), err))?;
        }

        match solver
            .check_sat()
            .map_err(|err| Error::prover_process_error(claim.name(), oracle.name(), err))?
        {
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
                ui.lock().unwrap().println(&format!(
                    "{:?}",
                    miette::Report::new(ClaimTheoremFailedError {
                        claim_name: claim.name().to_string(),
                        oracle_name: oracle.name().to_string(),
                        response,
                        modelfile: Ok(PathBuf::new()),
                    })
                ));
                return Err(ClaimTheoremFailedError {
                    claim_name: claim.name().to_string(),
                    oracle_name: oracle.name().to_string(),
                    response,
                    modelfile,
                }
                .into());
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
