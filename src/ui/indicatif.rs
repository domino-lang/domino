// SPDX-License-Identifier: MIT OR Apache-2.0

use indicatif::{MultiProgress, ProgressBar, ProgressIterator};
use indicatif_log_bridge::LogWrapper;

use super::{
    LatexUI, ProveClaimUI, ProveGamehopUI, ProveInvariantStartUI, ProveOracleUI, ProveTheoremUI,
    ProveUI, UI,
};

use crate::{
    gamehops::{
        equivalence::{error::Result, ResolvedClaim},
        GameHop,
    },
    package::Export,
};

#[derive(Clone)]
pub struct IndicatifUI {
    multi_progress: MultiProgress,
}

impl IndicatifUI {
    pub fn new() -> Self {
        let multi_progress = MultiProgress::new();
        let logger = env_logger::Builder::from_default_env().build();
        LogWrapper::new(multi_progress.clone(), logger)
            .try_init()
            .unwrap();
        Self { multi_progress }
    }

    fn insert_before(&self, before: &ProgressBar, progress: ProgressBar) -> ProgressBar {
        self.multi_progress.insert_before(before, progress)
    }
}

impl Default for IndicatifUI {
    fn default() -> Self {
        Self::new()
    }
}

impl UI for IndicatifUI {
    type ProveUI = IndicatifProveUI;
    type LatexUI = IndicatifLatexUI;

    fn println(&self, line: &str) -> std::io::Result<()> {
        self.multi_progress.println(line)
    }

    fn prove_ui(&self) -> Self::ProveUI {
        let progress = self.multi_progress.add(ProgressBar::new(0));

        progress.set_style(indicatif_style::theorem_bar());
        progress.set_message("Project");

        IndicatifProveUI {
            main_ui: self.clone(),
            progress,
        }
    }

    fn latex_ui(&self) -> Self::LatexUI {
        IndicatifLatexUI {
            main_ui: self.clone(),
        }
    }
}

#[derive(Clone)]
pub struct IndicatifProveUI {
    main_ui: IndicatifUI,
    progress: ProgressBar,
}

impl IndicatifProveUI {
    fn insert_before(&self, before: &ProgressBar, progress: ProgressBar) -> ProgressBar {
        self.main_ui.insert_before(before, progress)
    }

    fn tick(&self) {
        self.progress.tick();
    }
}

impl ProveUI for IndicatifProveUI {
    type ProveTheoremUI = IndicatifProveTheoremUI;

    fn println(&self, line: &str) -> std::io::Result<()> {
        self.main_ui.println(line)
    }

    fn start(&self) {}
    fn finish(&self) {
        self.progress.finish()
    }

    fn start_theorem(&self, theorem_name: &str) -> Self::ProveTheoremUI {
        self.progress.inc_length(1);

        IndicatifProveTheoremUI {
            prove_ui: self.clone(),
            name: theorem_name.to_string(),
            progress: None,
        }
    }
}

#[derive(Clone)]
pub struct IndicatifProveTheoremUI {
    prove_ui: IndicatifProveUI,
    name: String,
    progress: Option<ProgressBar>,
}

impl IndicatifProveTheoremUI {
    fn insert_before(&self, before: &ProgressBar, progress: ProgressBar) -> ProgressBar {
        self.prove_ui.insert_before(before, progress)
    }
    fn tick(&self) {
        self.prove_ui.tick();
        if let Some(progress) = &self.progress {
            progress.tick();
        }
    }
}

impl ProveTheoremUI for IndicatifProveTheoremUI {
    type ProveGamehopUI = IndicatifProveGamehopUI;

    fn println(&self, line: &str) -> std::io::Result<()> {
        self.prove_ui.println(line)
    }

    fn start(&mut self) {
        let new_progress = self.insert_before(&self.prove_ui.progress, ProgressBar::new(0));
        new_progress.set_style(indicatif_style::theorem_bar());
        new_progress.set_message(self.name.clone());
        self.progress = Some(new_progress);
        self.tick();
    }

    fn finish(&self) {
        self.prove_ui.progress.inc(1);
        self.tick();
        if let Some(progress) = &self.progress {
            progress.finish()
        }
    }

    fn start_gamehop(&self, gamehop: &GameHop) -> Self::ProveGamehopUI {
        if let Some(progress) = &self.progress {
            progress.inc_length(1);
        }
        self.tick();

        IndicatifProveGamehopUI {
            theorem_ui: self.clone(),
            name: format!("{gamehop}"),
            progress: None,
        }
    }
}

#[derive(Clone)]
pub struct IndicatifProveGamehopUI {
    theorem_ui: IndicatifProveTheoremUI,
    name: String,
    progress: Option<ProgressBar>,
}

impl IndicatifProveGamehopUI {
    fn insert_before(&self, before: &ProgressBar, progress: ProgressBar) -> ProgressBar {
        self.theorem_ui.insert_before(before, progress)
    }
    fn tick(&self) {
        self.theorem_ui.tick();
        if let Some(progress) = &self.progress {
            progress.tick();
        }
    }
}

impl ProveGamehopUI for IndicatifProveGamehopUI {
    type ProveOracleUI = IndicatifProveOracleUI;
    type ProveInvariantStartUI = IndicatifProveOracleUI;

    fn println(&self, line: &str) -> std::io::Result<()> {
        self.theorem_ui.println(line)
    }

    fn is_reduction(&self) {
        if let Some(progress) = &self.progress {
            progress.set_length(1);
            progress.inc(1);
        }
        self.tick()
    }

    fn start(&mut self) {
        if let Some(progress) = &self.theorem_ui.progress {
            let new_progress = self.insert_before(progress, ProgressBar::new(0));
            new_progress.set_style(indicatif_style::proofstep_bar());
            new_progress.set_message(self.name.clone());
            self.progress = Some(new_progress);
            self.tick()
        }
    }

    fn finish(&self) {
        if let Some(progress) = &self.theorem_ui.progress {
            progress.inc(1);
        }
        self.tick();
        if let Some(progress) = &self.progress {
            progress.finish();
        }
    }

    fn start_oracle(&self, export: &Export) -> Self::ProveOracleUI {
        if let Some(progress) = &self.progress {
            progress.inc_length(1);
        }
        self.tick();

        IndicatifProveOracleUI {
            proofstep_ui: self.clone(),
            name: export.name().to_string(),
            progress: None,
        }
    }
    fn start_invariant_start(&self, name: String) -> Self::ProveInvariantStartUI {
        if let Some(progress) = &self.progress {
            progress.inc_length(1);
        }
        self.tick();

        IndicatifProveOracleUI {
            proofstep_ui: self.clone(),
            name,
            progress: None,
        }
    }
}

#[derive(Clone)]
pub struct IndicatifProveOracleUI {
    proofstep_ui: IndicatifProveGamehopUI,
    name: String,
    progress: Option<ProgressBar>,
}

impl IndicatifProveOracleUI {
    fn insert_before(&self, before: &ProgressBar, progress: ProgressBar) -> ProgressBar {
        self.proofstep_ui.insert_before(before, progress)
    }
    fn tick(&self) {
        self.proofstep_ui.tick();
        if let Some(progress) = &self.progress {
            progress.tick();
        }
    }
    fn start(&mut self) {
        if let Some(progress) = &self.proofstep_ui.progress {
            let new_progress = self.insert_before(progress, ProgressBar::new(0));
            new_progress.set_style(indicatif_style::oracle_bar());
            new_progress.set_message(self.name.clone());
            self.progress = Some(new_progress);
            self.tick();
        }
    }

    fn finish(&self) {
        if let Some(progress) = &self.proofstep_ui.progress {
            progress.inc(1);
        }
        self.tick();
        if let Some(progress) = &self.progress {
            progress.finish();
        }
    }
    fn println(&self, line: &str) -> std::io::Result<()> {
        self.proofstep_ui.println(line)
    }
}

impl ProveOracleUI for IndicatifProveOracleUI {
    type ProveClaimUI = IndicatifProveClaimUI;

    fn println(&self, line: &str) -> std::io::Result<()> {
        self.println(line)
    }

    fn run(mut self, fun: impl FnOnce(&Self) -> Vec<Result<()>>) -> Vec<Result<()>> {
        self.start();
        let result = fun(&self);
        self.finish();
        result
    }

    fn start_claim(&self, claim: &ResolvedClaim) -> Self::ProveClaimUI {
        if let Some(progress) = &self.progress {
            progress.inc_length(1);
        }
        self.tick();

        IndicatifProveClaimUI {
            oracle_ui: self.clone(),
            name: claim.name().to_string(),
        }
    }
    fn start_injectivity(&self, claim: &str) -> Self::ProveClaimUI {
        if let Some(progress) = &self.progress {
            progress.inc_length(1);
        }
        self.tick();

        IndicatifProveClaimUI {
            oracle_ui: self.clone(),
            name: claim.to_string(),
        }
    }
}

impl ProveInvariantStartUI for IndicatifProveOracleUI {
    type ProveClaimUI = IndicatifProveClaimUI;

    fn println(&self, line: &str) -> std::io::Result<()> {
        self.proofstep_ui.println(line)
    }

    fn run(mut self, fun: impl FnOnce(&Self) -> Vec<Result<()>>) -> Vec<Result<()>> {
        self.start();
        let result = fun(&self);
        self.finish();
        result
    }

    fn start_claim(&self, claim: &str) -> Self::ProveClaimUI {
        if let Some(progress) = &self.progress {
            progress.inc_length(1);
        }
        self.tick();

        IndicatifProveClaimUI {
            oracle_ui: self.clone(),
            name: claim.to_string(),
        }
    }
}

pub struct IndicatifProveClaimUI {
    oracle_ui: IndicatifProveOracleUI,
    name: String,
}

impl IndicatifProveClaimUI {
    fn start(&mut self) {
        if let Some(progress) = &self.oracle_ui.progress {
            progress.set_message(format!("{} (cur: {})", self.oracle_ui.name, self.name));
        }
        self.oracle_ui.tick();
    }

    fn success(&self) {
        if let Some(progress) = &self.oracle_ui.progress {
            progress.inc(1);
            progress.set_message(self.oracle_ui.name.to_string());
            self.oracle_ui.tick();
        }
    }
    fn failure(&self) {
        if let Some(progress) = &self.oracle_ui.progress {
            progress.inc(1);
            progress.set_message(self.oracle_ui.name.to_string());
            self.oracle_ui.tick();
        }
    }
}

impl ProveClaimUI for IndicatifProveClaimUI {
    fn println(&self, line: &str) -> std::io::Result<()> {
        self.oracle_ui.println(line)
    }

    fn run(mut self, fun: impl FnOnce() -> Result<()>) -> Result<()> {
        self.start();
        let result = fun();
        if result.is_err() {
            self.failure();
        } else {
            self.success();
        }
        result
    }
}

pub struct IndicatifLatexUI {
    main_ui: IndicatifUI,
}

impl LatexUI for IndicatifLatexUI {
    fn game_iterator<Item>(
        &self,
        iter: impl ExactSizeIterator<Item = Item>,
        caption: String,
    ) -> impl Iterator<Item = Item> {
        let progress = self
            .main_ui
            .multi_progress
            .add(ProgressBar::new(iter.len().try_into().unwrap()));
        progress.set_style(indicatif_style::latex_bar());
        progress.set_message(caption);

        iter.progress_with(progress)
    }
}

mod indicatif_style {
    use indicatif::ProgressStyle;

    pub(super) fn theorem_bar() -> ProgressStyle {
        ProgressStyle::with_template(
            "[{elapsed_precise}] {bar:80.cyan/blue} {pos:>3}/{len:3} {msg}",
        )
        .unwrap()
        .progress_chars("#>-")
    }

    pub(super) fn proofstep_bar() -> ProgressStyle {
        ProgressStyle::with_template(
            "[{elapsed_precise}] {bar:80.yellow/white} {pos:>3}/{len:3} {msg}",
        )
        .unwrap()
        .progress_chars("#>-")
    }

    pub(super) fn oracle_bar() -> ProgressStyle {
        ProgressStyle::with_template(
            "[{elapsed_precise}] {bar:80.magenta/white} {pos:>3}/{len:3} {msg}",
        )
        .unwrap()
        .progress_chars("#>-")
    }

    pub(super) fn latex_bar() -> ProgressStyle {
        ProgressStyle::with_template(
            "[{elapsed_precise}] {bar:80.cyan/blue} {pos:>3}/{len:3} {msg}",
        )
        .unwrap()
        .progress_chars("#>-")
    }
}
