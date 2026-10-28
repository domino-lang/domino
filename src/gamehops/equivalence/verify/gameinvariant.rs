use crate::{
    gamehops::equivalence::{
        error::Result,
        verify::load_game_invariants,
        verify::{ClaimGroup, SmtDriver},
        SmtStmt,
    },
    project::{configuration::ProveConfiguration, Project},
    writers::smt::contexts::GameInstanceContext,
};

pub(crate) struct GameInvariantSmtDriver<
    'a,
    Proj: Project + Sync,
    ProveConf: ProveConfiguration + Sync,
> {
    gctx: &'a GameInstanceContext<'a>,
    project: &'a Proj,
    config: &'a ProveConf,
    invariants: Vec<SmtStmt>,
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
        gctx: &'a GameInstanceContext<'a>,
        project: &'a Proj,
        config: &'a ProveConf,
    ) -> Result<Self> {
        let invariants = load_game_invariants(gctx, project)?;

        Ok(Self {
            gctx,
            project,
            config,
            invariants,
        })
    }

    pub fn verify_game_invariants(&self) -> Result<()> {
        let mut smt = Vec::new();

        smt.extend(self.invariants.iter().map(|stmt| stmt.expr.clone()));

        Ok(())
    }
}
