// SPDX-License-Identifier: MIT OR Apache-2.0

use rayon::iter::{IntoParallelRefIterator, ParallelIterator};
use std::io::Write as _;
use std::sync::{Arc, Mutex};
use std::path::PathBuf;

use crate::{
    gamehops::equivalence::{
        error::{ClaimTheoremFailedError, Error, Result},
        ClaimScope,
    },
    package::Export,
    project::Project,
    theorem::{Claim, ClaimType, INITIAL_STATE_CLAIM_NAME},
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
    req_claim: Option<&'a str>,
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

    /// The initial-state invariant check isn't scoped to any one oracle, so `--oracle` (which
    /// asks for a specific oracle's claims) excludes it; `--claim` can still single it out via
    /// `INITIAL_STATE_CLAIM_NAME`.
    fn should_verify_initial_state(&self) -> bool {
        self.req_oracle.is_none()
            && self
                .req_claim
                .is_none_or(|req_claim| req_claim == INITIAL_STATE_CLAIM_NAME)
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
        let verify_initial_state = self.should_verify_initial_state();

        ui.lock().unwrap().proofstep_set_oracles(
            &self.eqctx.theorem().name,
            &proofstep_name,
            (oracle_sequence.len() + usize::from(verify_initial_state))
                .try_into()
                .unwrap(),
        );

        let claims: Vec<Result<()>> = rayon::ThreadPoolBuilder::new()
            .num_threads(self.parallel + 1) // one process is reserved for the "main" method
            .build()
            .unwrap()
            .install(|| -> Vec<Result<()>> {
                rayon::iter::once(())
                    .map(|_| {
                        if verify_initial_state {
                            vec![self.verify_invariants_in_initial_state(ui.clone(), &smt)]
                        } else {
                            vec![]
                        }
                    })
                    .chain(oracle_sequence.par_iter().map(|oracle| -> Vec<Result<()>> {
                        self.verify_oracle(ui.clone(), &smt, oracle)
                    }))
                    .flatten()
                    .collect()
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

    /// Checks that the invariant holds on the two game instances' basic initial states (all
    /// package state fields at their type's default value). This is the "induction start" /
    /// base-case obligation for the equivalence's invariant: `domino prove` proving every oracle
    /// preserves the invariant only shows it's an *inductive* invariant; this additionally
    /// checks it actually holds at the start.
    fn verify_invariants_in_initial_state<UI: TheoremUI + Send>(
        &self,
        ui: Arc<Mutex<&mut UI>>,
        equivalence_smt: &[SmtExpr],
    ) -> Result<()> {
        let mut smt = vec![];
        let eq = self.eqctx.equivalence();
        let proofstep_name = format!("{} == {}", eq.left_name(), eq.right_name());

        let claim = Claim {
            name: INITIAL_STATE_CLAIM_NAME.to_string(),
            dependencies: vec![],
            ty: ClaimType::InitialState,
            admitted: false,
            user_declared: false,
            invariant_scope: None,
        };

        let claim_scope = ClaimScope::InitialState;

        ui.lock().unwrap().start_scope(
            &self.eqctx.theorem().name,
            &proofstep_name,
            claim_scope.name(),
            1,
        );

        log::info!("verify: invariants in initial state");
        // TODO: this is temporary workaround until we make the invariants equivalence-wide.
        // For future: It's fine to unwrap for now as we accept games that don't expose any oracles.
        let oracle_name = self.eqctx.oracle_sequence().first().unwrap().name();
        smt.append(&mut self.eqctx.emit_invariant(oracle_name));
        smt.append(&mut self.eqctx.emit_initial_state_values());

        let result = self.verify_claim(ui.clone(), equivalence_smt, &smt, &claim, &claim_scope);

        ui.lock().unwrap().finish_scope(
            &self.eqctx.theorem().name,
            &proofstep_name,
            claim_scope.name(),
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

        let mut claims = self
            .eqctx
            .equivalence()
            .proof_tree_by_oracle_name(oracle.name());

        self.reconcile_invariant_fragment_claims(&mut claims, oracle.name());

        claims.extend(
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
                            user_declared: false,
                            invariant_scope: None,
                        })
                    }
                }),
        );
        claims.extend(
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
                            user_declared: false,
                            invariant_scope: None,
                        })
                    }
                }),
        );
        if !self.eqctx.left_game_inst_ctx().game().invariants.is_empty() {
            claims.push(Claim {
                admitted: false,
                dependencies: vec!["no-abort".to_string()],
                ty: ClaimType::LeftGameInvariant,
                name: format!(
                    "game-invariant!{}!",
                    self.eqctx.left_game_inst_ctx().game_inst().name(),
                ),
                user_declared: false,
                invariant_scope: None,
            })
        }
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
                user_declared: false,
                invariant_scope: None,
            })
        }

        if let Err(err) = self.validate_claim_dependencies(&claims, oracle.name()) {
            return vec![Err(err)];
        }
        if let Err(err) = self.validate_invariant_scopes(&claims, oracle.name()) {
            return vec![Err(err)];
        }

        let claim_scope = ClaimScope::Oracle(oracle.name().to_string());

        ui.lock().unwrap().start_scope(
            &self.eqctx.theorem().name,
            &proofstep_name,
            claim_scope.name(),
            claims.len().try_into().unwrap(),
        );

        log::info!("verify: oracle:{oracle:?}");
        smt.extend(&mut self.eqctx.emit_return_value_helpers(oracle.name()));
        smt.append(&mut self.eqctx.emit_auto_randomness(oracle.name()));
        smt.append(&mut self.eqctx.emit_invariant(oracle.name()));

        let result: Vec<_> = claims
            .par_iter()
            .filter(|claim| {
                if let Some(req_claim) = self.req_claim {
                    claim.name == req_claim
                } else {
                    true
                }
            })
            .map(|claim| -> Result<()> {
                self.verify_claim(ui.clone(), equivalence_smt, &smt, claim, &claim_scope)
            })
            .collect();

        ui.lock().unwrap().finish_scope(
            &self.eqctx.theorem().name,
            &proofstep_name,
            claim_scope.name(),
        );

        result
    }

    /// Reconciles this oracle's invariant fragments (every `define-state-relation` declared in
    /// its main invariant files) into `claims`, in place. A state relation's name is never
    /// special — one the user happens to name `invariant` is just another fragment — so this
    /// applies uniformly, regardless of whether one of the fragments happens to be named
    /// `invariant`.
    ///
    /// Any claim (auto or user-declared) named after a fragment that `ClaimType::guess_from_name`
    /// would otherwise call `Lemma` gets its `ClaimType` corrected to `Invariant` — `guess_from_name`
    /// only looks at the name prefix, and a `Lemma`-shaped SMT call never worked for a fragment
    /// not conventionally prefixed `invariant`/`relation` anyway (there's no matching
    /// `define-lemma` to call), so this is a strict bugfix. Fragments already recognized as
    /// `relation-*` are deliberately left alone: that's the pre-existing convention (proven and
    /// chained by hand in the `lemmas {}` block, e.g. in the 4WHS example project) for using a
    /// state relation as an explicit dependency of another claim, which still works exactly as
    /// before.
    ///
    /// Every fragment becomes its own claim, each individually reported on failure: every
    /// fragment not already covered by an explicit `lemmas {}` entry gets an auto-generated
    /// claim depending only on `no-abort`. Domino never proves a monolithic AND of them as its
    /// own claim automatically — see `theorem::DOMINO_INVARIANT_FN_NAME` for the (differently
    /// named) function that plays that role internally.
    fn reconcile_invariant_fragment_claims(&self, claims: &mut Vec<Claim>, oracle_name: &str) {
        let fragment_names = self.eqctx.state_relation_names(oracle_name);

        for claim in claims.iter_mut() {
            if claim.ty == ClaimType::Lemma && fragment_names.iter().any(|name| name == &claim.name)
            {
                claim.ty = ClaimType::Invariant;
            }
        }

        for name in fragment_names {
            if !claims.iter().any(|claim| &claim.name == name) {
                claims.push(Claim {
                    name: name.clone(),
                    ty: ClaimType::Invariant,
                    dependencies: vec!["no-abort".to_string()],
                    admitted: false,
                    user_declared: false,
                    invariant_scope: None,
                });
            }
        }
    }

    /// Validates every claim's `with invariants [...]` scope (if any) for this oracle: each named
    /// fragment must actually be a `define-state-relation` declared here (never a `define-lemma`
    /// claim). Since every fragment is always auto-proved regardless of whether the user declares
    /// it explicitly, there's no separate "must already be proved" requirement to check here.
    fn validate_invariant_scopes(&self, claims: &[Claim], oracle_name: &str) -> Result<()> {
        let fragment_names = self.eqctx.state_relation_names(oracle_name);

        for claim in claims {
            let Some(scope) = &claim.invariant_scope else {
                continue;
            };
            for fragment_name in scope {
                if !fragment_names.iter().any(|name| name == fragment_name) {
                    return Err(Error::UnknownInvariantScopeReference {
                        oracle_name: oracle_name.to_string(),
                        claim_name: claim.name().to_string(),
                        fragment_name: fragment_name.clone(),
                    });
                }
            }
        }
        Ok(())
    }

    /// Rejects claims that list an invariant (or invariant fragment, or package/game invariant)
    /// as an explicit dependency — `emit_oracle_claim_assert`'s `dep_calls` construction has no
    /// meaningful call shape for those (they're already assumed automatically for every claim,
    /// so referencing one by name as a dependency is never necessary and would otherwise hit an
    /// internal `unreachable!()`).
    fn validate_claim_dependencies(&self, claims: &[Claim], oracle_name: &str) -> Result<()> {
        for claim in claims {
            for dep in claim.dependencies() {
                if !matches!(
                    ClaimType::guess_from_name(dep),
                    ClaimType::Lemma | ClaimType::Relation
                ) {
                    return Err(Error::InvariantUsedAsDependency {
                        oracle_name: oracle_name.to_string(),
                        claim_name: claim.name().to_string(),
                        dependency_name: dep.clone(),
                    });
                }
            }
        }
        Ok(())
    }

    fn verify_claim<UI: TheoremUI>(
        &self,
        ui: Arc<Mutex<&mut UI>>,
        equivalence_smt: &[SmtExpr],
        scope_smt: &[SmtExpr],
        claim: &Claim,
        claim_scope: &ClaimScope,
    ) -> Result<()> {
        let eq = self.eqctx.equivalence();
        let proofstep_name = format!("{} == {}", eq.left_name(), eq.right_name());
        ui.lock().unwrap().start_lemma(
            &self.eqctx.theorem().name,
            &proofstep_name,
            claim_scope.name(),
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
                            claim_scope.name(),
                            claim.name(),
                        )
                        .unwrap();

                    self.backend.new_smtsolver_with_transcript(transcript_file)
                } else {
                    self.backend.new_smtsolver()
                }
            }
            .map_err(|err| Error::prover_process_error(claim.name(), claim_scope.name(), err))?;
            std::thread::sleep(std::time::Duration::from_millis(20));

            let model_info = self.eqctx.emit_model_info(claim_scope, claim);

            for entry in equivalence_smt
                .iter()
                .chain(scope_smt)
                .chain(model_info.iter())
                .chain(std::iter::once(
                    &self.eqctx.emit_claim_assert(claim, claim_scope),
                ))
            {
                solver.write_smt(entry.clone()).map_err(|err| {
                    Error::prover_process_error(claim.name(), claim_scope.name(), err)
                })?;
            }

            match solver
                .check_sat()
                .map_err(|err| Error::prover_process_error(claim.name(), claim_scope.name(), err))?
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

                    ui.lock().unwrap().println(&format!("{:?}",
                    miette::Report::new(ClaimTheoremFailedError {
                        claim_name: claim.name().to_string(),
                        scope_name: claim_scope.name().to_string(),
                        response,
                        modelfile: Ok(PathBuf::new()),
                    })));

                    return Err(
                        ClaimTheoremFailedError {
                            claim_name: claim.name().to_string(),
                            scope_name: claim_scope.name().to_string(),
                            response,
                            modelfile,
                        }
                        .into()
                    );
                }
            }
        }
        ui.lock().unwrap().finish_lemma(
            &self.eqctx.theorem().name,
            &proofstep_name,
            claim_scope.name(),
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
