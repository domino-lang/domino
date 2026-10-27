// SPDX-License-Identifier: MIT OR Apache-2.0

use rayon::iter::{IntoParallelIterator, ParallelIterator};

use std::io::Write;

use crate::{
    gamehops::equivalence::{
        error::{self, ClaimTheoremFailedError, Error, Result},
        smtrewrite, ClaimType, ResolvedClaim, ResolvedDependency, SmtStatementKind, SmtStmt,
    },
    package::Export,
    project::{configuration::ProveConfiguration, Project},
    theorem::{Claim, RandomnessMappingInjectivityCheck},
    ui::{ProveClaimUI, ProveGamehopUI, ProveInvariantStartUI, ProveOracleUI},
    util::smtsolver::{SmtSolver, SmtSolverBackend, SmtSolverResponse},
    writers::smt::{
        contexts::{EquivalenceContext, GameInstanceContext},
        exprs::SmtExpr,
    },
};

pub(crate) struct EquivalenceSmtDriver<
    'a,
    Proj: Project + Sync,
    ProveConf: ProveConfiguration + Sync,
> {
    eqctx: &'a EquivalenceContext<'a>,
    project: &'a Proj,
    config: &'a ProveConf,
    invariants: Vec<SmtStmt>,
    claims: Vec<(String, Vec<ResolvedClaim>)>,
    left_invariants: Vec<SmtStmt>,
    right_invariants: Vec<SmtStmt>,
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

fn load_equivalence_invariants(
    eqctx: &EquivalenceContext,
    project: &impl Project,
) -> Result<Vec<SmtStmt>> {
    let mut result = Vec::new();

    // Load the main Invariant
    for file_name in eqctx.equivalence().invariants() {
        log::info!("reading file {file_name}");
        let file_contents = project.read_input_file(file_name).map_err(|err| {
            let file_name = file_name.clone();
            error::new_invariant_file_read_error(file_name, err)
        })?;
        log::info!("read file {file_name}");
        result.extend(smtrewrite::rewrite(eqctx, &file_contents)?);
    }

    Ok(result)
}

fn load_game_invariants(
    gctx: &GameInstanceContext,
    project: &impl Project,
) -> Result<Vec<SmtStmt>> {
    let mut result = Vec::new();

    // Load Game Invariants
    for pkg in &gctx.game().pkgs {
        for file_name in &pkg.pkg.invariants {
            let file_contents = project.read_input_file(file_name).map_err(|err| {
                let file_name = file_name.to_string();
                error::new_invariant_file_read_error(file_name, err)
            })?;

            let stmts = smtrewrite::rewrite_package(gctx, pkg, &file_contents)?;

            result.extend(stmts);
        }
    }

    // Load Game Invariants
    for file_name in &gctx.game().invariants {
        let file_contents = project.read_input_file(file_name).map_err(|err| {
            let file_name = file_name.to_string();
            error::new_invariant_file_read_error(file_name, err)
        })?;

        let stmts = smtrewrite::rewrite_game(gctx, &file_contents)?;

        result.extend(stmts);
    }

    Ok(result)
}

pub(crate) fn resolve_claims(
    eqctx: &EquivalenceContext,
    invariants: &[SmtStmt],
) -> Vec<(String, Vec<ResolvedClaim>)> {
    let claims = &eqctx.equivalence().trees;
    claims
        .iter()
        .map(|(oracle, claims)| {
            let claims = claims
                .iter()
                .map(|claim| {
                    let Claim {
                        name,
                        dependencies,
                        admitted,
                    } = claim.clone();

                    let ty = ClaimType::read_from_smt(&name, invariants)
                        .unwrap_or_else(|| ClaimType::guess_from_name(&name));

                    let dependencies = dependencies
                        .into_iter()
                        .map(|name| {
                            let ty = ClaimType::read_from_smt(&name, invariants)
                                .unwrap_or_else(|| ClaimType::guess_from_name(&name));
                            ResolvedDependency { name, ty }
                        })
                        .collect();

                    ResolvedClaim {
                        name,
                        ty,
                        dependencies,
                        admitted,
                    }
                })
                .collect();

            (oracle.clone(), claims)
        })
        .collect()
}

impl<'a, Proj, ProveConf> EquivalenceSmtDriver<'a, Proj, ProveConf>
where
    Proj: Project + Sync,
    ProveConf: ProveConfiguration + Sync,
{
    pub(crate) fn new(
        eqctx: &'a EquivalenceContext<'a>,
        project: &'a Proj,
        config: &'a ProveConf,
    ) -> Result<Self> {
        let invariants = load_equivalence_invariants(eqctx, project)?;
        let left_invariants = load_game_invariants(&eqctx.left_game_inst_ctx(), project)?;
        let right_invariants = load_game_invariants(&eqctx.right_game_inst_ctx(), project)?;
        let claims = resolve_claims(eqctx, &invariants);

        Ok(Self {
            eqctx,
            project,
            config,
            invariants,
            claims,
            left_invariants,
            right_invariants,
        })
    }

    fn oracle_sequence(&self) -> Vec<&'a Export> {
        let game_inst = self
            .eqctx
            .theorem()
            .find_game_instance(self.eqctx.equivalence().left_name())
            .unwrap();

        game_inst
            .game()
            .exports
            .iter()
            .filter(|export| self.config.oracle_requested(export.name()))
            .collect()
    }

    fn claims_by_oracle_name(&self, oracle_name: &str) -> Vec<ResolvedClaim> {
        self.claims
            .iter()
            .find(|(name, _tree)| name == oracle_name)
            .map(|(_oname, tree)| tree.clone())
            .unwrap_or_else(|| panic!("can't find proof tree for {oracle_name}"))
    }

    fn generate_game_or_package_invariant_claims(&self) -> Vec<ResolvedClaim> {
        fn new_claim(ty: ClaimType, name: String) -> Option<ResolvedClaim> {
            Some(ResolvedClaim {
                admitted: false,
                dependencies: vec![ResolvedDependency {
                    name: "no-abort".to_string(),
                    ty: ClaimType::Lemma,
                }],
                ty,
                name,
            })
        }

        self.left_invariants
            .iter()
            .filter_map(|stmt| match stmt.kind {
                SmtStatementKind::PackageInvariant { .. } => {
                    new_claim(ClaimType::LeftPackageInvariant, stmt.kind.name())
                }
                SmtStatementKind::GameInvariant { .. } => {
                    new_claim(ClaimType::LeftGameInvariant, stmt.kind.name())
                }
                _ => None,
            })
            .chain(
                self.right_invariants
                    .iter()
                    .filter_map(|stmt| match stmt.kind {
                        SmtStatementKind::PackageInvariant { .. } => {
                            new_claim(ClaimType::RightPackageInvariant, stmt.kind.name())
                        }
                        SmtStatementKind::GameInvariant { .. } => {
                            new_claim(ClaimType::RightGameInvariant, stmt.kind.name())
                        }
                        _ => None,
                    }),
            )
            .collect()
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

        smt.extend(
            self.invariants
                .iter()
                .chain(self.left_invariants.iter())
                .chain(self.right_invariants.iter())
                .map(|stmt| stmt.expr.clone()),
        );

        let equivalence_smt = SmtBuf::from(smt.as_slice());

        let oracle_sequence = self.oracle_sequence();

        let claims = rayon::ThreadPoolBuilder::new()
            .num_threads(self.config.parallel())
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

                if self.config.invariant_start_requested() {
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

                if self.config.restricted_requests() {
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
        checks.append(&mut self.generate_game_or_package_invariant_start_asserts());

        ui.run(|ui| {
            let checks: Vec<_> = checks
                .iter()
                .filter(|(claim_name, _)| self.config.claim_requested(claim_name))
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
        let mut claims = self.claims_by_oracle_name(oracle.name());

        claims.append(&mut self.generate_game_or_package_invariant_claims());

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
            .filter(|check| self.config.claim_requested(check.name()))
            .map(|check| {
                let claim_name = check.name();
                let claim_smt = check.emit_randomness_mapping_injectivity_check(oracle.name());
                let ui = ui.start_injectivity(claim_name);

                (claim_name, claim_smt, ui)
            })
            .collect();

        if !self.config.injectivity_requested() {
            tasks.extend(
                claims
                    .iter()
                    .filter(|claim| {
                        !claim.is_admitted() && self.config.claim_requested(&claim.name)
                    })
                    .map(|claim| {
                        let claim_smt = vec![self.eqctx.emit_oracle_claim_assert(
                            claim,
                            oracle.name(),
                            &self.left_invariants,
                            &self.right_invariants,
                        )];
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
            if self.config.transcript() {
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

                self.config
                    .solver_backend()
                    .new_smtsolver_with_transcript(transcript_file)
            } else {
                self.config.solver_backend().new_smtsolver()
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
