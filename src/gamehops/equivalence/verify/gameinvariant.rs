use rayon::iter::{IntoParallelIterator, ParallelIterator};

use crate::{
    gamehops::equivalence::{
        error::{Error, Result},
        verify::load_game_invariants,
        verify::{ClaimGroup, SmtBuf, SmtDriver},
        ClaimType, ResolvedClaim, ResolvedDependency, SmtStatementKind, SmtStmt,
    },
    project::{configuration::ProveConfiguration, Project},
    ui::{ProveGameClaimUI, ProveGameInvariantStartUI, ProveGameOracleUI, ProveGameUI},
    writers::smt::{contexts::GameInstanceContext, declare::declare_const},
};

pub(crate) struct GameInvariantSmtDriver<
    'a,
    Proj: Project + Sync,
    ProveConf: ProveConfiguration + Sync,
> {
    gctx: GameInstanceContext<'a>,
    project: &'a Proj,
    config: &'a ProveConf,
    pub(super) invariants: Vec<SmtStmt>,
}

impl<'a, Proj, ProveConf> SmtDriver<'a, Proj, ProveConf>
    for GameInvariantSmtDriver<'a, Proj, ProveConf>
where
    Proj: Project + Sync,
    ProveConf: ProveConfiguration + Sync,
{
    fn config(&self) -> &ProveConf {
        self.config
    }
    fn project(&self) -> &Proj {
        self.project
    }
    fn transcript_file(&self, claim_group: &ClaimGroup, claim_name: &str) -> std::fs::File {
        self.project
            .get_smt_file(
                "!Game-and-Package-Invariants!",
                self.gctx.game_inst_name(),
                &claim_group.file_system_name(),
                claim_name,
            )
            .unwrap()
    }
}

impl<'a, Proj, ProveConf> GameInvariantSmtDriver<'a, Proj, ProveConf>
where
    Proj: Project + Sync,
    ProveConf: ProveConfiguration + Sync,
{
    pub fn new(
        gctx: GameInstanceContext<'a>,
        project: &'a Proj,
        config: &'a ProveConf,
    ) -> Result<Self> {
        let invariants = load_game_invariants(&gctx, project)?;

        Ok(Self {
            gctx,
            project,
            config,
            invariants,
        })
    }

    pub fn verify_game_invariants(&self, ui: &impl ProveGameUI) -> Result<()> {
        let mut smt = Vec::new();

        smt.append(&mut self.gctx.emit_base_declarations());
        smt.extend(&mut self.gctx.emit_game_paramfuncs());

        smt.extend(self.gctx.smt_composition_randomness());
        smt.extend(self.gctx.smt_package_const_definitions());
        smt.extend(self.gctx.smt_package_state_definitions());
        smt.push(self.gctx.smt_game_const_definition());
        smt.push(self.gctx.smt_game_state_definition());
        smt.extend(self.gctx.smt_game_pkg_const_mapping_definitions());
        smt.extend(self.gctx.smt_package_return_definitions());
        smt.extend(self.gctx.smt_oracle_function_definitions());

        for export in &self.gctx.game().exports {
            let orcl_ctx = self
                .gctx
                .exported_oracle_ctx_by_name(export.name())
                .unwrap();

            for (arg_name, arg_type) in &export.sig().args {
                smt.push(declare_const(
                    orcl_ctx.smt_arg_name(arg_name),
                    arg_type.clone().into(),
                ));
            }
        }

        smt.extend(self.gctx.emit_constant_declarations(None));

        smt.extend(self.invariants.iter().map(|stmt| stmt.expr.clone()));

        let game_inst_smt = SmtBuf::from(smt.as_slice());

        let claim_sequence: Vec<_> = self
            .generate_game_or_package_invariant_claims()
            .map(|claim| (ui.start_claim(&claim), claim))
            .collect();

        let claims = rayon::ThreadPoolBuilder::new()
            .num_threads(self.config.parallel())
            .build()
            .unwrap()
            .install(|| -> Vec<Result<()>> {
                claim_sequence
                    .into_par_iter()
                    .map(|(ui, claim)| self.verify_claim(ui, game_inst_smt.clone(), &claim))
                    .flatten()
                    .collect()
            });

        let failed_claims: Vec<_> = claims.into_iter().filter_map(Result::err).collect();
        if !failed_claims.is_empty() {
            return Err(Error::ParallelGameInvariantError {
                game_inst_name: self.gctx.game_name().to_string(),
                failed_claims,
            });
        }

        Ok(())
    }

    fn verify_invariant_start(
        &self,
        ui: impl ProveGameInvariantStartUI,
        game_inst_smt: &SmtBuf,
        claim: &ResolvedClaim,
    ) -> Result<()> {
        let claim_group = ClaimGroup::InvariantStart;

        let mut game_inst_smt = game_inst_smt.clone();

        let initial_state_values = self.gctx.emit_game_initial_state_values();
        game_inst_smt.push(initial_state_values.as_slice());

        let assert = self.gctx.emit_game_or_package_invariant_start_assert(claim);

        let claim_smt = [assert.clone()];
        let mut smt = game_inst_smt.clone();
        smt.push(&claim_smt);

        ui.run(|| self.verify_with_solver(smt, &claim_group, &claim.name))
    }

    fn verify_claim(
        &self,
        ui: impl ProveGameClaimUI,
        game_inst_smt: SmtBuf,
        claim: &ResolvedClaim,
    ) -> Vec<Result<()>> {
        ui.run(|ui| {
            let oracle_sequence: Vec<_> = self
                .gctx
                .game()
                .exports
                .iter()
                .filter_map(|export| {
                    if self.config.oracle_requested(export.name()) {
                        Some((ui.start_oracle(export), export))
                    } else {
                        None
                    }
                })
                .collect();

            rayon::iter::once(self.verify_invariant_start(
                ui.start_invariant_start(),
                &game_inst_smt,
                claim,
            ))
            .chain(oracle_sequence.into_par_iter().map(|(ui, export)| {
                let claim_group = ClaimGroup::Oracle {
                    oracle_name: export.name().to_string(),
                };
                let mut smt = game_inst_smt.clone();

                let assert = vec![self.gctx.emit_oracle_claim_assert(
                    claim,
                    export.name(),
                    &self.invariants,
                )];
                smt.push(&assert);

                ui.run(|| self.verify_with_solver(smt, &claim_group, &claim.name))
            }))
            .collect()
        })
    }

    fn generate_game_or_package_invariant_claims(
        &'a self,
    ) -> impl Iterator<Item = ResolvedClaim> + use<'a, Proj, ProveConf> {
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

        self.invariants.iter().filter_map(|stmt| match stmt.kind {
            SmtStatementKind::PackageInvariant { .. } => {
                new_claim(ClaimType::PackageInvariant, stmt.kind.name())
            }
            SmtStatementKind::GameInvariant { .. } => {
                new_claim(ClaimType::GameInvariant, stmt.kind.name())
            }
            _ => unreachable!(),
        })
    }
}
