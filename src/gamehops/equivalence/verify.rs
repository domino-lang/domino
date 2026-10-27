use std::io::Write;

use crate::{
    gamehops::equivalence::{
        error::{self, ClaimTheoremFailedError},
        smtrewrite, ClaimType, Error, ResolvedClaim, ResolvedDependency, Result, SmtStmt,
    },
    project::configuration::ProveConfiguration,
    project::Project,
    theorem::Claim,
    util::smtsolver::{SmtSolver, SmtSolverBackend, SmtSolverResponse},
    writers::smt::{
        contexts::{EquivalenceContext, GameInstanceContext},
        exprs::SmtExpr,
    },
};

pub(super) mod equivalence;

pub(super) enum ClaimGroup {
    Oracle { oracle_name: String },
    InvariantStart,
}

impl ClaimGroup {
    pub(super) fn ui_name(&self) -> String {
        match self {
            Self::Oracle { oracle_name } => oracle_name.clone(),
            Self::InvariantStart => "invariant-start".to_string(),
        }
    }

    pub(super) fn error_name(&self) -> String {
        match self {
            Self::Oracle { oracle_name } => format!("oracle {oracle_name}").to_string(),
            Self::InvariantStart => "invariant start".to_string(),
        }
    }

    pub(super) fn file_system_name(&self) -> String {
        match self {
            Self::Oracle { oracle_name } => oracle_name.clone(),
            Self::InvariantStart => "!invariant-start!".to_string(),
        }
    }
}

#[derive(Debug, Clone)]
pub(super) struct SmtBuf<'a> {
    slices: Vec<&'a [SmtExpr]>,
}

impl<'a> SmtBuf<'a> {
    pub(super) fn push(&mut self, slice: &'a [SmtExpr]) {
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

pub(super) trait SmtDriver<'a, Proj: Project + Sync, ProveConf: ProveConfiguration + Sync> {
    fn config(&self) -> &ProveConf;

    fn project(&self) -> &Proj;

    fn transcript_file(&self, claim_group: &ClaimGroup, claim_name: &str) -> std::fs::File;

    fn verify_with_solver(
        &self,
        smt: SmtBuf,
        claim_group: &ClaimGroup,
        claim_name: &str,
    ) -> Result<()> {
        let mut solver = {
            if self.config().transcript() {
                let transcript_file = self.transcript_file(claim_group, claim_name);

                self.config()
                    .solver_backend()
                    .new_smtsolver_with_transcript(transcript_file)
            } else {
                self.config().solver_backend().new_smtsolver()
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
