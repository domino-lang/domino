// SPDX-License-Identifier: MIT OR Apache-2.0

use rayon::iter::{IntoParallelRefIterator, ParallelIterator};
use wildcard::Wildcard;

use std::io::Write as _;
use std::sync::{Arc, Mutex};

use crate::{
    gamehops::equivalence::{
        error::{ClaimTheoremFailedError, Error, Result},
    },
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
    req_claim: Option<Wildcard<'a>>,
    parallel: usize,
    only_induction_start: bool,
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
        only_induction_start: bool
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
            only_induction_start
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

        let claims = rayon::ThreadPoolBuilder::new()
            .num_threads(self.parallel + 1) // one process is reserved for the "main" method
            .build()
            .unwrap()
            .install(|| -> Vec<Result<()>> {
                let verify_induction_start = rayon::iter::once(())
                    .map(|_| self.verify_induction_start(ui.clone(), &smt));

                if self.only_induction_start {
                    verify_induction_start.collect()
                } else {
                    let verify_oracle_claims = oracle_sequence
                        .par_iter()
                        .map(|oracle| self.verify_oracle(ui.clone(), &smt, oracle))
                        .flatten();
                    verify_induction_start.chain(verify_oracle_claims).collect()
                }
            });

        let failed_claims: Vec<_> = claims.into_iter().filter_map(Result::err).collect();
        if !failed_claims.is_empty() {
            return Err(Error::ParallelEquivalenceError {
                left_game_inst_name: eq.left_name.clone(),
                right_game_inst_name: eq.right_name.clone(),
                failed_claims,
            });
        }
        Ok(())
    }

    fn verify_induction_start<UI: TheoremUI + Send>(
        &self,
        ui: Arc<Mutex<&mut UI>>,
        equivalence_smt: &Vec<SmtExpr>,
    ) -> Result<()> {
        let mut smt = equivalence_smt.clone();
        let eq = self.eqctx.equivalence();
        let proofstep_name = format!("{} == {}", eq.left_name(), eq.right_name());

        let claim_group_name = "auto-generated:induction-start";
        let transcript_file_claim_group_name = "!induction-start!";

        ui.lock().unwrap().start_claim_group(
            &self.eqctx.theorem().name,
            &proofstep_name,
            claim_group_name,
            1,
        );

        log::info!("verify: invariants in initial state");
        // TODO (#365): this is temporary workaround until we make the invariants equivalence-wide.
        // For future: It's fine to unwrap for now as we accept games that don't expose any oracles.
        let oracle_name = self.oracle_sequence().first().unwrap().name();
        smt.append(&mut self.eqctx.emit_invariant(oracle_name));
        smt.append(&mut self.eqctx.emit_initial_state_values());
        smt.push(self.eqctx.emit_induction_start_assert());

        let result = self.verify_with_solver(
            smt, 
            claim_group_name, 
            "equivalence-induction-start", 
            transcript_file_claim_group_name, 
            "!equivalence-induction-start!");

        ui.lock().unwrap().finish_claim_group(
            &self.eqctx.theorem().name,
            &proofstep_name,
            claim_group_name,
        );

        result
    }

    fn generate_left_package_invariant_claims(&self) -> Vec<Claim> {
        self.eqctx
            .left_game_inst_ctx()
            .game()
            .pkgs
            .iter()
            .filter_map(|pkg| {
                if pkg.pkg.invariants.is_empty() {
                    None
                } else {
                    Some(Claim {
                        admitted: false,
                        dependencies: vec!["no-abort".to_string()],
                        ty: ClaimType::LeftPackageInvariant,
                        name: format!(
                            "package-invariant!{}-{}!",
                            self.eqctx.left_game_inst_ctx().game_inst().name(),
                            pkg.name()
                        ),
                    })
                }
            })
            .collect()
    }

    fn generate_right_package_invariant_claims(&self) -> Vec<Claim> {
        self.eqctx
            .right_game_inst_ctx()
            .game()
            .pkgs
            .iter()
            .filter_map(|pkg| {
                if pkg.pkg.invariants.is_empty() {
                    None
                } else {
                    Some(Claim {
                        admitted: false,
                        dependencies: vec!["no-abort".to_string()],
                        ty: ClaimType::RightPackageInvariant,
                        name: format!(
                            "package-invariant!{}-{}!",
                            self.eqctx.right_game_inst_ctx().game_inst().name(),
                            pkg.name()
                        ),
                    })
                }
            })
            .collect()
    }

    fn push_left_game_invariant_claim_if_exists(
        &self, 
        claims: &mut Vec<Claim>)
    {
        if !self.eqctx.left_game_inst_ctx().game().invariants.is_empty() {
            claims.push(Claim {
                admitted: false,
                dependencies: vec!["no-abort".to_string()],
                ty: ClaimType::LeftGameInvariant,
                name: format!(
                    "game-invariant!{}!",
                    self.eqctx.left_game_inst_ctx().game_inst().name(),
                ),
            })
        }
    }

    fn push_right_game_invariant_claim_if_exists(
        &self, 
        claims: &mut Vec<Claim>)
    {
        if !self
            .eqctx
            .right_game_inst_ctx()
            .game()
            .invariants
            .is_empty()
        {
            claims.push(Claim {
                admitted: false,
                dependencies: vec!["no-abort".to_string()],
                ty: ClaimType::RightGameInvariant,
                name: format!(
                    "game-invariant!{}!",
                    self.eqctx.right_game_inst_ctx().game_inst().name(),
                ),
            })
        }
    }

    fn verify_oracle<UI: TheoremUI + Send>(
        &self,
        ui: Arc<Mutex<&mut UI>>,
        equivalence_smt: &Vec<SmtExpr>,
        oracle: &Export,
    ) -> Vec<Result<()>> {
        let mut smt = Vec::new();
        let eq = self.eqctx.equivalence();
        let proofstep_name = format!("{} == {}", eq.left_name(), eq.right_name());

        let mut claims = self
            .eqctx
            .equivalence()
            .proof_tree_by_oracle_name(oracle.name());

        claims.extend(self.generate_left_package_invariant_claims());
        claims.extend(self.generate_right_package_invariant_claims());

        self.push_left_game_invariant_claim_if_exists(&mut claims);
        self.push_right_game_invariant_claim_if_exists(&mut claims);

        let claim_group_name = oracle.name().to_string();

        ui.lock().unwrap().start_claim_group(
            &self.eqctx.theorem().name,
            &proofstep_name,
            &claim_group_name,
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
                self.verify_claim(ui.clone(), equivalence_smt, &smt, oracle.name(), claim)
            })
            .collect();

        ui.lock().unwrap().finish_claim_group(
            &self.eqctx.theorem().name,
            &proofstep_name,
            &claim_group_name,
        );

        result
    }

    fn verify_claim<UI: TheoremUI>(
        &self,
        ui: Arc<Mutex<&mut UI>>,
        equivalence_smt: &Vec<SmtExpr>,
        oracle_smt: &Vec<SmtExpr>,
        oracle_name: &str,
        claim: &Claim
    ) -> Result<()> {
        let eq = self.eqctx.equivalence();
        let proofstep_name = format!("{} == {}", eq.left_name(), eq.right_name());
        ui.lock().unwrap().start_claim(
            &self.eqctx.theorem().name,
            &proofstep_name,
            oracle_name,
            claim.name(),
        );

        let result = self.do_verify_claim(equivalence_smt, oracle_smt, oracle_name, claim);

        ui.lock().unwrap().finish_claim(
            &self.eqctx.theorem().name,
            &proofstep_name,
            oracle_name,
            claim.name(),
        );

        result
    }

    fn do_verify_claim(
        &self,
        equivalence_smt: &Vec<SmtExpr>,
        oracle_smt: &Vec<SmtExpr>,
        oracle_name: &str,
        claim: &Claim
    ) -> Result<()> {
        if claim.is_admitted() {
            return Ok(());
        }

        let mut smt = equivalence_smt.clone();
        smt.append(&mut oracle_smt.clone());
        smt.push(self.eqctx.emit_oracle_claim_assert(claim, oracle_name));
        self.verify_with_solver(
            smt,
            oracle_name,
            claim.name(),
            oracle_name,
            claim.name()
        )
    }

    fn verify_with_solver(&self,
        smt: Vec<SmtExpr>,
        claim_group_name: &str,
        claim_name: &str,
        transcript_file_claim_group_name: &str,
        transcript_file_claim_name: &str
    ) -> Result<()> {
        let eq = self.eqctx.equivalence();
        let mut solver = {
            if self.transcript {
                let transcript_file: std::fs::File = self
                    .project
                    .get_joined_smt_file(
                        eq.left_name(),
                        eq.right_name(),
                        transcript_file_claim_group_name,
                        transcript_file_claim_name,
                    )
                    .unwrap();

                self.backend.new_smtsolver_with_transcript(transcript_file)
            } else {
                self.backend.new_smtsolver()
            }
        }
        .map_err(|err| Error::prover_process_error(claim_name, claim_group_name, err))?;
        std::thread::sleep(std::time::Duration::from_millis(20));

        for entry in smt
        {
            solver
                .write_smt(entry.clone())
                .map_err(|err| Error::prover_process_error(claim_name, claim_group_name, err))?;
        }

        match solver
            .check_sat()
            .map_err(|err| Error::prover_process_error(claim_name, claim_group_name, err))?
        {
            SmtSolverResponse::Unsat => Ok(()),
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
                    claim_name: claim_name.to_string(),
                    claim_group_name: claim_group_name.to_string(),
                    response,
                    modelfile,
                }
                .into());
            }
        }
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
