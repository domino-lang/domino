// SPDX-License-Identifier: MIT OR Apache-2.0

use indicatif::{MultiProgress, ProgressBar};
use indicatif_log_bridge::LogWrapper;

use super::{ProveLemmaUI, ProveOracleUI, ProveProofstepUI, ProveTheoremUI, ProveUI, UI};

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

impl UI for IndicatifUI {
    fn println(&self, line: &str) -> std::io::Result<()> {
        self.multi_progress.println(line)
    }

    fn prove_ui(&self) -> impl ProveUI {
        let progress = self.multi_progress.add(ProgressBar::new(0));

        progress.set_style(indicatif_style::theorem_bar());
        progress.set_message("Project");

        IndicatifProveUI {
            main_ui: self.clone(),
            progress,
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
    fn println(&self, line: &str) -> std::io::Result<()> {
        self.main_ui.println(line)
    }

    fn start(&self) {}
    fn finish(&self) {
        self.progress.finish()
    }

    fn start_theorem(&self, theorem_name: &str) -> impl ProveTheoremUI {
        self.progress.inc_length(1);

        IndicatifProveTheoremUI {
            prove_ui: self.clone(),
            name: theorem_name.to_string(),
            progress: None,
        }
    }
}

#[derive(Clone)]
pub(crate) struct IndicatifProveTheoremUI {
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

    fn start_proofstep(&self, name: String) -> impl ProveProofstepUI {
        if let Some(progress) = &self.progress {
            progress.inc_length(1);
        }
        self.tick();

        IndicatifProveProofstepUI {
            theorem_ui: self.clone(),
            name,
            progress: None,
        }
    }
}

#[derive(Clone)]
pub(crate) struct IndicatifProveProofstepUI {
    theorem_ui: IndicatifProveTheoremUI,
    name: String,
    progress: Option<ProgressBar>,
}

impl IndicatifProveProofstepUI {
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

impl ProveProofstepUI for IndicatifProveProofstepUI {
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

    fn start_oracle(&self, name: String) -> impl ProveOracleUI {
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
pub(crate) struct IndicatifProveOracleUI {
    proofstep_ui: IndicatifProveProofstepUI,
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
}

impl ProveOracleUI for IndicatifProveOracleUI {
    fn println(&self, line: &str) -> std::io::Result<()> {
        self.proofstep_ui.println(line)
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

    fn start_lemma(&self, lemma_name: &str) -> impl ProveLemmaUI {
        if let Some(progress) = &self.progress {
            progress.inc_length(1);
        }
        self.tick();

        IndicatifProveLemmaUI {
            oracle_ui: self.clone(),
            name: lemma_name.to_string(),
        }
    }
}

pub(crate) struct IndicatifProveLemmaUI {
    oracle_ui: IndicatifProveOracleUI,
    name: String,
}

impl ProveLemmaUI for IndicatifProveLemmaUI {
    fn println(&self, line: &str) -> std::io::Result<()> {
        self.oracle_ui.println(line)
    }

    fn start(&mut self) {
        if let Some(progress) = &self.oracle_ui.progress {
            progress.set_message(format!("{} (cur: {})", self.oracle_ui.name, self.name));
        }
        self.oracle_ui.tick();
    }

    fn finish(&self) {
        if let Some(progress) = &self.oracle_ui.progress {
            progress.inc(1);
            progress.set_message(self.oracle_ui.name.to_string());
            self.oracle_ui.tick();
        }
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
}
