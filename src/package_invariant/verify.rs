// SPDX-License-Identifier: MIT OR Apache-2.0

use std::io::Write as _;
use std::sync::{Arc, Mutex};

use rayon::iter::{IntoParallelRefIterator, ParallelIterator};

use crate::{
    project::Project,
    ui::TheoremUI,
    util::smtsolver::{SmtSolver, SmtSolverBackend, SmtSolverResponse},
    writers::smt::exprs::SmtExpr,
};

use super::{
    context::PackageInvariantContext,
    error::{ClaimFailedError, Error, Result},
};

/// The name the package invariant checks appear under in the UI, in place of a theorem name.
pub(crate) const UI_SECTION_NAME: &str = "Package Invariants";

/// The name of the claim group that checks the invariant holds in the initial state.
pub(crate) const INVARIANT_START: &str = "invariant-start";

/// One thing we prove about a package invariant.
#[derive(Clone, Debug, PartialEq, Eq)]
enum ClaimGroup {
    /// the invariant holds in the initial state of the package
    InvariantStart,
    /// the invariant is preserved by a call to this oracle
    Oracle { oracle_name: String },
}

impl ClaimGroup {
    fn ui_name(&self) -> &str {
        match self {
            Self::InvariantStart => INVARIANT_START,
            Self::Oracle { oracle_name } => oracle_name,
        }
    }

    fn file_system_name(&self) -> String {
        match self {
            Self::InvariantStart => "!invariant-start!".to_string(),
            Self::Oracle { oracle_name } => oracle_name.clone(),
        }
    }
}

/// Proves the invariant of a single package against its synthetic game.
pub(crate) struct PackageInvariantSmtDriver<
    'a,
    Backend: SmtSolverBackend + Sync,
    Proj: Project + Sync,
> {
    ctx: &'a PackageInvariantContext<'a>,
    project: &'a Proj,
    backend: &'a Backend,
    transcript: bool,
    req_oracle: Option<&'a str>,
    parallel: usize,
    invariant_start_only: bool,
}

impl<'a, Backend: SmtSolverBackend + Sync, Proj: Project + Sync>
    PackageInvariantSmtDriver<'a, Backend, Proj>
{
    pub(crate) fn new(
        ctx: &'a PackageInvariantContext<'a>,
        project: &'a Proj,
        backend: &'a Backend,
        transcript: bool,
        req_oracle: Option<&'a str>,
        parallel: usize,
        invariant_start_only: bool,
    ) -> Self {
        Self {
            ctx,
            project,
            backend,
            transcript,
            req_oracle,
            parallel,
            invariant_start_only,
        }
    }

    /// Returns the claim groups to verify, honouring `--oracle` and `--invariant-start`.
    fn claim_groups(&self) -> Result<Vec<ClaimGroup>> {
        if self.invariant_start_only {
            return Ok(vec![ClaimGroup::InvariantStart]);
        }

        let oracle_names = self.ctx.oracle_names();

        if let Some(req_oracle) = self.req_oracle {
            if !oracle_names.iter().any(|name| name == req_oracle) {
                return Err(Error::UnknownOracle {
                    pkg_name: self.ctx.pkg_name().to_string(),
                    oracle_name: req_oracle.to_string(),
                    known_oracle_names: oracle_names,
                });
            }

            return Ok(vec![ClaimGroup::Oracle {
                oracle_name: req_oracle.to_string(),
            }]);
        }

        Ok(std::iter::once(ClaimGroup::InvariantStart)
            .chain(
                oracle_names
                    .into_iter()
                    .map(|oracle_name| ClaimGroup::Oracle { oracle_name }),
            )
            .collect())
    }

    pub(crate) fn verify<UI: TheoremUI + Send>(&self, ui: &mut UI) -> Result<()> {
        let pkg_name = self.ctx.pkg_name();
        let claim_groups = self.claim_groups()?;

        log::info!("verify: package invariant of {pkg_name}");

        // the declarations every claim needs
        let mut base_smt = Vec::new();
        base_smt.push(SmtExpr::Comment("base declarations:\n".to_string()));
        base_smt.extend(self.ctx.emit_base_declarations());
        base_smt.push(SmtExpr::Comment("theorem param funcs:\n".to_string()));
        base_smt.extend(self.ctx.emit_theorem_paramfuncs());
        base_smt.push(SmtExpr::Comment("game definitions:\n".to_string()));
        base_smt.extend(self.ctx.emit_game_definitions());

        let ui = Arc::new(Mutex::new(ui));
        ui.lock().unwrap().proofstep_set_claim_groups_count(
            UI_SECTION_NAME,
            pkg_name,
            claim_groups.len().try_into().unwrap(),
        );

        let results: Vec<Result<()>> = rayon::ThreadPoolBuilder::new()
            .num_threads(self.parallel + 1) // one thread is reserved for the "main" method
            .build()
            .unwrap()
            .install(|| {
                claim_groups
                    .par_iter()
                    .map(|claim_group| self.verify_claim_group(ui.clone(), &base_smt, claim_group))
                    .collect()
            });

        let failed_claims: Vec<_> = results.into_iter().filter_map(Result::err).collect();
        if !failed_claims.is_empty() {
            return Err(Error::Parallel {
                pkg_name: pkg_name.to_string(),
                failed_claims,
            });
        }

        Ok(())
    }

    fn verify_claim_group<UI: TheoremUI + Send>(
        &self,
        ui: Arc<Mutex<&mut UI>>,
        base_smt: &[SmtExpr],
        claim_group: &ClaimGroup,
    ) -> Result<()> {
        let pkg_name = self.ctx.pkg_name();

        // at the moment every group holds exactly one claim. Once packages can declare several
        // named invariants, this is where the claims of a group get enumerated.
        ui.lock()
            .unwrap()
            .start_claim_group(UI_SECTION_NAME, pkg_name, claim_group.ui_name(), 1);
        ui.lock().unwrap().start_claim(
            UI_SECTION_NAME,
            pkg_name,
            claim_group.ui_name(),
            "package-invariant",
        );

        let mut smt = base_smt.to_owned();
        smt.extend(self.ctx.emit_invariant());

        match claim_group {
            ClaimGroup::InvariantStart => {
                smt.extend(self.ctx.emit_initial_state_values());
                smt.push(self.ctx.emit_invariant_start_assert());
            }
            ClaimGroup::Oracle { oracle_name } => {
                smt.extend(self.ctx.emit_constant_declarations());
                smt.push(self.ctx.emit_oracle_claim_assert(oracle_name));
            }
        }

        let result = self.verify_with_solver(smt, claim_group);

        ui.lock().unwrap().finish_claim(
            UI_SECTION_NAME,
            pkg_name,
            claim_group.ui_name(),
            "package-invariant",
        );
        ui.lock()
            .unwrap()
            .finish_claim_group(UI_SECTION_NAME, pkg_name, claim_group.ui_name());

        result
    }

    fn verify_with_solver(&self, smt: Vec<SmtExpr>, claim_group: &ClaimGroup) -> Result<()> {
        let pkg_name = self.ctx.pkg_name();
        let claim_group_name = claim_group.ui_name();

        let mut solver = if self.transcript {
            let transcript_file = self
                .project
                .get_package_invariant_smt_file(pkg_name, &claim_group.file_system_name())
                .unwrap();

            self.backend.new_smtsolver_with_transcript(transcript_file)
        } else {
            self.backend.new_smtsolver()
        }
        .map_err(|err| Error::prover_process(pkg_name, claim_group_name, err))?;

        for entry in smt {
            solver
                .write_smt(entry)
                .map_err(|err| Error::prover_process(pkg_name, claim_group_name, err))?;
        }

        match solver
            .check_sat()
            .map_err(|err| Error::prover_process(pkg_name, claim_group_name, err))?
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

                Err(ClaimFailedError {
                    pkg_name: pkg_name.to_string(),
                    claim_group_name: claim_group_name.to_string(),
                    response,
                    modelfile,
                }
                .into())
            }
        }
    }
}
