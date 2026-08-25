// SPDX-License-Identifier: MIT OR Apache-2.0

use rayon::iter::{IntoParallelRefIterator, ParallelIterator};
use wildcard::Wildcard;

use std::io::Write as _;
use std::sync::{Arc, Mutex};

use crate::writers::smt::contexts::GameInstanceContext;
use crate::{
    gamehops::equivalence::error::{ClaimTheoremFailedError, Error, Result},
    package::Export,
    project::Project,
    theorem::{Claim, ClaimType},
    ui::TheoremUI,
    util::smtsolver::{SmtSolver, SmtSolverBackend, SmtSolverResponse},
    writers::smt::{
        contexts::{EquivalenceContext, RandomnessMappingInjectivityCheck},
        exprs::SmtExpr,
    },
};

pub(crate) struct EquivalenceSmtDriver<'a, Backend: SmtSolverBackend + Sync, Proj: Project + Sync> {
    eqctx: &'a EquivalenceContext<'a>,
    project: &'a Proj,
    backend: &'a Backend,
    transcript: bool,
    req_oracle: Option<&'a str>,
    req_claim: Option<Wildcard<'a>>,
    parallel: usize,
    invariant_start: bool,
    injective_randmap: bool,
}

enum ClaimGroup {
    Oracle { oracle_name: String },
    InvariantStart,
}

impl ClaimGroup {
    fn ui_name(&self) -> String {
        match self {
            Self::Oracle { oracle_name } => oracle_name.clone(),
            Self::InvariantStart => "invariant-start".to_string(),
        }
    }

    fn error_name(&self) -> String {
        match self {
            Self::Oracle { oracle_name } => format!("oracle {oracle_name}").to_string(),
            Self::InvariantStart => "invariant start".to_string(),
        }
    }

    fn file_system_name(&self) -> String {
        match self {
            Self::Oracle { oracle_name } => oracle_name.clone(),
            Self::InvariantStart => "!invariant-start!".to_string(),
        }
    }
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
        invariant_start: bool,
        injective_randmap: bool,
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
            invariant_start,
            injective_randmap,
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

        ui.lock().unwrap().proofstep_set_claim_groups_count(
            &self.eqctx.theorem().name,
            &proofstep_name,
            (oracle_sequence.len() + 1) // 1 is for invariant start
                .try_into()
                .unwrap(),
        );

        let claims = rayon::ThreadPoolBuilder::new()
            .num_threads(self.parallel + 1) // one process is reserved for the "main" method
            .build()
            .unwrap()
            .install(|| -> Vec<Result<()>> {
                let verify_invariant_start = rayon::iter::once(())
                    .map(|_| self.verify_invariant_start(ui.clone(), &smt))
                    .flatten();

                if self.invariant_start {
                    return verify_invariant_start.collect();
                }

                let verify_oracle_claims = oracle_sequence
                    .par_iter()
                    .map(|oracle| self.verify_oracle(ui.clone(), &smt, oracle))
                    .flatten();

                if self.req_oracle.is_some() {
                    return verify_oracle_claims.collect();
                }

                verify_invariant_start.chain(verify_oracle_claims).collect()
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

    fn generate_game_or_package_invariant_start_asserts(&self) -> Vec<(String, SmtExpr)> {
        self.generate_game_or_package_invariant_claims()
            .iter()
            .map(|claim| {
                let smt = self
                    .eqctx
                    .emit_game_or_package_invariant_start_assert(claim);
                (claim.name().to_string(), smt)
            })
            .collect()
    }

    fn verify_invariant_start<UI: TheoremUI + Send>(
        &self,
        ui: Arc<Mutex<&mut UI>>,
        equivalence_smt: &[SmtExpr],
    ) -> Vec<Result<()>> {
        let eq = self.eqctx.equivalence();
        let proofstep_name = format!("{} == {}", eq.left_name(), eq.right_name());

        let claim_group = ClaimGroup::InvariantStart;

        log::info!("verify: invariants at initial state");

        let mut base_smt = equivalence_smt.to_owned();
        // TODO (#365): this is temporary workaround until we make the invariants equivalence-wide.
        // For future: It's fine to unwrap for now as we accept games that don't expose any oracles.
        let oracle_name = self.oracle_sequence().first().unwrap().name();
        base_smt.append(&mut self.eqctx.emit_invariant(oracle_name));
        base_smt.append(&mut self.eqctx.emit_initial_state_values());

        let mut checks: Vec<(String, SmtExpr)> = vec![(
            "invariant".to_string(),
            self.eqctx.emit_invariant_start_assert(),
        )];
        checks.append(&mut self.generate_game_or_package_invariant_start_asserts());

        ui.lock().unwrap().start_claim_group(
            &self.eqctx.theorem().name,
            &proofstep_name,
            &claim_group.ui_name(),
            checks.len().try_into().unwrap(),
        );

        let result: Vec<_> = checks
            .par_iter()
            .filter(|(claim_name, _)| self.is_claim_requested(claim_name))
            .map(|(claim_name, assert)| {
                let mut smt = base_smt.clone();
                smt.push(assert.clone());
                self.verify_with_solver(smt, &claim_group, claim_name)
            })
            .collect();

        ui.lock().unwrap().finish_claim_group(
            &self.eqctx.theorem().name,
            &proofstep_name,
            &claim_group.ui_name(),
        );

        result
    }

    fn generate_package_invariant_claims(
        &self,
        gctx: GameInstanceContext<'a>,
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

    fn generate_game_invariant_claim_if_exists(
        &self,
        gctx: GameInstanceContext<'a>,
        claim_type: ClaimType,
    ) -> Option<Claim> {
        if !gctx.game().invariants.is_empty() {
            Some(Claim {
                admitted: false,
                dependencies: vec!["no-abort".to_string()],
                ty: claim_type,
                name: format!("game-invariant!{}!", gctx.game_inst_name(),),
            })
        } else {
            None
        }
    }

    fn generate_game_or_package_invariant_claims(&self) -> Vec<Claim> {
        let mut claims = vec![];
        claims.extend(self.generate_package_invariant_claims(
            self.eqctx.left_game_inst_ctx(),
            ClaimType::LeftPackageInvariant,
        ));
        claims.extend(self.generate_package_invariant_claims(
            self.eqctx.right_game_inst_ctx(),
            ClaimType::RightPackageInvariant,
        ));

        if let Some(claim) = self.generate_game_invariant_claim_if_exists(
            self.eqctx.left_game_inst_ctx(),
            ClaimType::LeftGameInvariant,
        ) {
            claims.push(claim);
        }
        if let Some(claim) = self.generate_game_invariant_claim_if_exists(
            self.eqctx.right_game_inst_ctx(),
            ClaimType::RightGameInvariant,
        ) {
            claims.push(claim);
        }
        claims
    }

    fn verify_randomness_mapping_injectivity<UI: TheoremUI + Send>(
        &self,
        ui: Arc<Mutex<&mut UI>>,
        equivalence_smt: &[SmtExpr],
        oracle_name: &str,
        claim_group: &ClaimGroup
    ) -> Vec<Result<()>> {
        log::info!("verify: randomness mapping injectivity of oracle {oracle_name}");

        // the randomness mapping is either defined by the invariant file (custom randomness) or
        // generated for us (simple/no randomness), so we need both of them here.
        let mut base_smt = equivalence_smt.to_owned();
        base_smt.append(&mut self.eqctx.emit_auto_randomness(oracle_name));
        base_smt.append(&mut self.eqctx.emit_invariant(oracle_name));

        RandomnessMappingInjectivityCheck::ALL
            .as_slice()
            .par_iter()
            .filter(|check| self.is_claim_requested(check.name()))
            .map(|check| {
                let claim_name = check.name();

                let mut smt = base_smt.clone();
                smt.extend(check.emit_randomness_mapping_injectivity_check(oracle_name));

                self.verify_claim_with_ui(ui.clone(), claim_group, claim_name, || {
                    self.verify_with_solver(smt, claim_group, claim_name)
                })
            })
            .collect()
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

        let mut claims = self
            .eqctx
            .equivalence()
            .proof_tree_by_oracle_name(oracle.name());

        claims.append(&mut self.generate_game_or_package_invariant_claims());

        let claim_group = ClaimGroup::Oracle {
            oracle_name: oracle.name().to_string(),
        };

        let num_claims = if self.injective_randmap {
            RandomnessMappingInjectivityCheck::ALL.len()
        } else {
            claims.len() + RandomnessMappingInjectivityCheck::ALL.len()
        };

        ui.lock().unwrap().start_claim_group(
            &self.eqctx.theorem().name,
            &proofstep_name,
            &claim_group.ui_name(),
            num_claims.try_into().unwrap(),
        );

        log::info!("verify: oracle:{oracle:?}");
        smt.extend(&mut self.eqctx.emit_return_value_helpers(oracle.name()));
        smt.append(&mut self.eqctx.emit_auto_randomness(oracle.name()));
        smt.append(&mut self.eqctx.emit_invariant(oracle.name()));

        let result = self.do_verify_oracle(ui.clone(), equivalence_smt, &smt, oracle, &claims, &claim_group);

        ui.lock().unwrap().finish_claim_group(
            &self.eqctx.theorem().name,
            &proofstep_name,
            &claim_group.ui_name(),
        );

        result
    }

    fn do_verify_oracle<UI: TheoremUI + Send>(
        &self,
        ui: Arc<Mutex<&mut UI>>,
        equivalence_smt: &[SmtExpr],
        oracle_smt: &[SmtExpr],
        oracle: &Export,
        claims: &Vec<Claim>,
        claim_group: &ClaimGroup
    ) -> Vec<Result<()>> {
        let verify_randomness_mapping_injectivity = rayon::iter::once(())
            .map(|_| {
                self.verify_randomness_mapping_injectivity(
                    ui.clone(),
                    equivalence_smt,
                    oracle.name(),
                    claim_group
                )
            })
            .flatten();

        if self.injective_randmap {
            return verify_randomness_mapping_injectivity.collect();
        }

        let verify_oracle_claims = claims
            .par_iter()
            .filter(|claim| self.is_claim_requested(&claim.name))
            .map(|claim| -> Result<()> {
                self.verify_claim(
                    ui.clone(),
                    equivalence_smt,
                    oracle_smt,
                    oracle.name(),
                    claim,
                    claim_group
                )
            });

        verify_randomness_mapping_injectivity
            .chain(verify_oracle_claims)
            .collect()
    }

    fn verify_claim<UI: TheoremUI>(
        &self,
        ui: Arc<Mutex<&mut UI>>,
        equivalence_smt: &[SmtExpr],
        oracle_smt: &[SmtExpr],
        oracle_name: &str,
        claim: &Claim,
        claim_group: &ClaimGroup
    ) -> Result<()> {
        self.verify_claim_with_ui(ui, &claim_group, claim.name(), || {
            self.do_verify_claim(equivalence_smt, oracle_smt, oracle_name, claim, &claim_group)
        })
    }

    /// Runs `verify` for the given claim, telling the ui when it starts and when it finishes.
    fn verify_claim_with_ui<UI: TheoremUI>(
        &self,
        ui: Arc<Mutex<&mut UI>>,
        claim_group: &ClaimGroup,
        claim_name: &str,
        verify: impl FnOnce() -> Result<()>,
    ) -> Result<()> {
        let eq = self.eqctx.equivalence();
        let proofstep_name = format!("{} == {}", eq.left_name(), eq.right_name());

        ui.lock().unwrap().start_claim(
            &self.eqctx.theorem().name,
            &proofstep_name,
            &claim_group.ui_name(),
            claim_name,
        );

        let result = verify();

        ui.lock().unwrap().finish_claim(
            &self.eqctx.theorem().name,
            &proofstep_name,
            &claim_group.ui_name(),
            claim_name,
        );

        result
    }

    fn is_claim_requested(&self, claim_name: &str) -> bool {
        match &self.req_claim {
            Some(req_claim) => req_claim.is_match(claim_name.as_bytes()),
            None => true,
        }
    }

    fn do_verify_claim(
        &self,
        equivalence_smt: &[SmtExpr],
        oracle_smt: &[SmtExpr],
        oracle_name: &str,
        claim: &Claim,
        claim_group: &ClaimGroup
    ) -> Result<()> {
        if claim.is_admitted() {
            return Ok(());
        }

        let mut smt = equivalence_smt.to_owned();
        smt.append(&mut oracle_smt.to_owned());
        smt.push(self.eqctx.emit_oracle_claim_assert(claim, oracle_name));
        let claim_group = ClaimGroup::Oracle {
            oracle_name: oracle_name.to_string(),
        };
        self.verify_with_solver(smt, &claim_group, claim.name())
    }

    fn verify_with_solver(
        &self,
        smt: Vec<SmtExpr>,
        claim_group: &ClaimGroup,
        claim_name: &str,
    ) -> Result<()> {
        let eq = self.eqctx.equivalence();
        let mut solver = {
            if self.transcript {
                let transcript_file: std::fs::File = self
                    .project
                    .get_smt_file(
                        eq.theorem_name(),
                        eq.left_name(),
                        eq.right_name(),
                        &claim_group.file_system_name(),
                        claim_name,
                    )
                    .unwrap();

                self.backend.new_smtsolver_with_transcript(transcript_file)
            } else {
                self.backend.new_smtsolver()
            }
        }
        .map_err(|err| Error::prover_process_error(claim_name, &claim_group.error_name(), err))?;
        std::thread::sleep(std::time::Duration::from_millis(20));

        for entry in smt {
            solver.write_smt(entry.clone()).map_err(|err| {
                Error::prover_process_error(claim_name, &claim_group.error_name(), err)
            })?;
        }

        match solver.check_sat().map_err(|err| {
            Error::prover_process_error(claim_name, &claim_group.error_name(), err)
        })? {
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
                Err(ClaimTheoremFailedError {
                    claim_name: claim_name.to_string(),
                    claim_group_name: claim_group.error_name(),
                    response,
                    modelfile,
                }
                .into())
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
