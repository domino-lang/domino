// SPDX-License-Identifier: MIT OR Apache-2.0

use rayon::iter::{IntoParallelIterator, ParallelIterator};
use wildcard::Wildcard;

use std::io::Write;

use crate::{
    gamehops::equivalence::{
        error::{ClaimTheoremFailedError, Error, Result},
        ResolvedClaim,
    },
    package::Export,
    project::Project,
    theorem::RandomnessMappingInjectivityCheck,
    ui::{ProveClaimUI, ProveGamehopUI, ProveInvariantStartUI, ProveOracleUI},
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

#[derive(Debug, Clone)]
struct SmtBuf<'a> {
    slices: Vec<&'a [SmtExpr]>,
}

impl<'a> SmtBuf<'a> {
    fn push(&mut self, slice: &'a [SmtExpr]) {
        self.slices.push(slice);
    }
}

impl<'a> From<&'a [SmtExpr]> for SmtBuf<'a> {
    fn from(slice: &'a [SmtExpr]) -> Self {
        Self {
            slices: vec![slice],
        }
    }
}

impl<'a> IntoIterator for SmtBuf<'a> {
    type Item = &'a SmtExpr;
    type IntoIter = std::iter::Flatten<std::vec::IntoIter<&'a [SmtExpr]>>;

    fn into_iter(self) -> Self::IntoIter {
        self.slices.into_iter().flatten()
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

    fn is_claim_requested(&self, claim_name: &str) -> bool {
        match &self.req_claim {
            Some(req_claim) => req_claim.is_match(claim_name.as_bytes()),
            None => true,
        }
    }

    pub(crate) fn verify(&mut self, ui: impl ProveGamehopUI) -> Result<()> {
        self.eqctx.verify_exports_match()?;

        self.verify_equivalence(ui)
    }

    fn verify_equivalence(&self, ui: impl ProveGamehopUI) -> Result<()> {
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

        smt.append(&mut self.eqctx.emit_invariant());

        let equivalence_smt = SmtBuf::from(smt.as_slice());

        let oracle_sequence = self.oracle_sequence();

        let claims = rayon::ThreadPoolBuilder::new()
            .num_threads(self.parallel)
            .build()
            .unwrap()
            .install(|| -> Vec<Result<()>> {
                let verify_invariant_start = rayon::iter::once(())
                    .map(|_| {
                        self.verify_invariant_start(
                            ui.start_invariant_start(ClaimGroup::InvariantStart.ui_name()),
                            &equivalence_smt,
                        )
                    })
                    .flatten();

                if self.invariant_start {
                    return verify_invariant_start.collect();
                }

                let oracle_sequence: Vec<_> = oracle_sequence
                    .iter()
                    .map(|oracle| {
                        let ui = ui.start_oracle(oracle);
                        (oracle, ui)
                    })
                    .collect();

                let verify_oracle_claims = oracle_sequence
                    .into_par_iter()
                    .map(|(oracle, ui)| self.verify_oracle(ui, &equivalence_smt, oracle))
                    .flatten();

                if self.req_oracle.is_some() || self.injective_randmap {
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
        ui.finish();
        Ok(())
    }

    fn verify_invariant_start(
        &self,
        ui: impl ProveInvariantStartUI,
        equivalence_smt: &SmtBuf,
    ) -> Vec<Result<()>> {
        let claim_group = ClaimGroup::InvariantStart;

        log::info!("verify: invariants at initial state");

        let initial_state_values = self.eqctx.emit_initial_state_values();
        let mut base_smt = equivalence_smt.to_owned();
        base_smt.push(initial_state_values.as_slice());

        let mut checks: Vec<(String, SmtExpr)> = vec![(
            "invariant".to_string(),
            self.eqctx.emit_invariant_start_assert(),
        )];
        checks.append(
            &mut self
                .eqctx
                .generate_game_or_package_invariant_start_asserts(),
        );

        ui.run(|ui| {
            let checks: Vec<_> = checks
                .iter()
                .filter(|(claim_name, _)| self.is_claim_requested(claim_name))
                .map(|(claim_name, assert)| {
                    let ui = ui.start_claim(claim_name);

                    (claim_name, assert, ui)
                })
                .collect();

            checks
                .into_par_iter()
                .map(|(name, assert, ui)| {
                    let claim_smt = [assert.clone()];
                    let mut smt = base_smt.to_owned();
                    smt.push(&claim_smt);

                    ui.run(|| self.verify_with_solver(smt, &claim_group, name))
                })
                .collect()
        })
    }

    fn verify_oracle(
        &self,
        ui: impl ProveOracleUI,
        equivalence_smt: &SmtBuf,
        oracle: &Export,
    ) -> Vec<Result<()>> {
        let mut claims = self.eqctx.claims_by_oracle_name(oracle.name());

        claims.append(&mut self.eqctx.generate_game_or_package_invariant_claims());

        let claim_group = ClaimGroup::Oracle {
            oracle_name: oracle.name().to_string(),
        };

        ui.run(|ui| self.do_verify_oracle(ui, equivalence_smt, oracle, &claims, &claim_group))
    }

    fn do_verify_oracle(
        &self,
        ui: &impl ProveOracleUI,
        equivalence_smt: &SmtBuf,
        oracle: &Export,
        claims: &[ResolvedClaim],
        claim_group: &ClaimGroup,
    ) -> Vec<Result<()>> {
        log::info!("verify: oracle:{oracle:?}");
        let auto_randomness = self.eqctx.emit_auto_randomness(oracle.name());
        let mut oracle_smt = equivalence_smt.to_owned();
        oracle_smt.push(auto_randomness.as_slice());

        let return_value_helpers = self.eqctx.emit_return_value_helpers(oracle.name());
        oracle_smt.push(return_value_helpers.as_slice());

        let randomness_mapping_condition =
            self.eqctx.emit_randomness_mapping_condition(oracle.name());
        oracle_smt.push(randomness_mapping_condition.as_slice());

        let mut tasks: Vec<_> = RandomnessMappingInjectivityCheck::ALL
            .as_slice()
            .iter()
            .filter(|check| self.is_claim_requested(check.name()))
            .map(|check| {
                let claim_name = check.name();
                let claim_smt = check.emit_randomness_mapping_injectivity_check(oracle.name());
                let ui = ui.start_injectivity(claim_name);

                (claim_name, claim_smt, ui)
            })
            .collect();

        if !self.injective_randmap {
            tasks.extend(
                claims
                    .iter()
                    .filter(|claim| !claim.is_admitted() && self.is_claim_requested(&claim.name))
                    .map(|claim| {
                        let claim_smt =
                            vec![self.eqctx.emit_oracle_claim_assert(claim, oracle.name())];
                        let ui = ui.start_claim(claim);

                        (claim.name(), claim_smt, ui)
                    }),
            );
        }

        tasks
            .into_par_iter()
            .map(|(name, assert, ui)| {
                let mut smt = oracle_smt.to_owned();
                smt.push(&assert);

                ui.run(|| self.verify_with_solver(smt, claim_group, name))
            })
            .collect()
    }

    fn verify_with_solver(
        &self,
        smt: SmtBuf,
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
}
