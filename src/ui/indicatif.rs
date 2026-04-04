// SPDX-License-Identifier: MIT OR Apache-2.0

use indicatif::{MultiProgress, ProgressBar};
use indicatif_log_bridge::LogWrapper;
use itertools::Itertools;
use std::collections::HashMap;

use super::{BaseUI, TheoremUI};

pub struct IndicatifTheoremUI {
    main_progress: MultiProgress,
    project_progress: Option<ProgressBar>,
    seq_theorem_progress: HashMap<String, ProgressBar>,
    seq_proofstep_progress: HashMap<(String, String), ProgressBar>,
    seq_oracle_progress: HashMap<(String, String, String), ProgressBar>,
}

impl IndicatifTheoremUI {
    pub fn new(num_theorems: u64) -> impl TheoremUI {
        let base_ui = IndicatifBaseUI::new();
        base_ui.into_theorem_ui(num_theorems)
    }
}

impl TheoremUI for IndicatifTheoremUI {
    fn println(&self, line: &str) -> std::io::Result<()> {
        self.main_progress.println(line)
    }

    fn start_theorem(&mut self, theorem_name: &str, num_proofsteps: u64) {
        let theorem_progress = self.main_progress.add(ProgressBar::new(num_proofsteps));

        theorem_progress.set_style(indicatif_style::theorem_bar());
        theorem_progress.set_message(theorem_name.to_string());

        self.seq_theorem_progress
            .insert(theorem_name.to_string(), theorem_progress);
    }

    fn finish_theorem(&mut self, theorem_name: &str) {
        if let Some(project_progress) = &self.project_progress {
            project_progress.inc(1);
        };
        if let Some(theorem_progress) = self.seq_theorem_progress.get(theorem_name) {
            theorem_progress.finish();
        }
    }

    fn start_proofstep(&mut self, theorem_name: &str, proofstep_name: &str) {
        let proofstep_progress = self.main_progress.add(ProgressBar::new(1));
        proofstep_progress.set_style(indicatif_style::proofstep_bar());
        proofstep_progress.set_message(proofstep_name.to_string());

        self.seq_proofstep_progress.insert(
            (theorem_name.to_string(), proofstep_name.to_string()),
            proofstep_progress,
        );
    }

    fn proofstep_is_reduction(&mut self, theorem_name: &str, proofstep_name: &str) {
        if let Some(proofstep_progress) = self
            .seq_proofstep_progress
            .get(&(theorem_name.to_string(), proofstep_name.to_string()))
        {
            proofstep_progress.set_length(1);
            proofstep_progress.inc(1);
            proofstep_progress.tick();
        } else {
            unreachable!("{theorem_name} -- {proofstep_name}");
        };
    }

    fn proofstep_set_oracles(
        &mut self,
        theorem_name: &str,
        proofstep_name: &str,
        num_oracles: u64,
    ) {
        if let Some(proofstep_progress) = self
            .seq_proofstep_progress
            .get(&(theorem_name.to_string(), proofstep_name.to_string()))
        {
            proofstep_progress.set_length(num_oracles);
            proofstep_progress.tick();
        } else {
            unreachable!("{theorem_name} -- {proofstep_name}");
        };
    }

    fn finish_proofstep(&mut self, theorem_name: &str, proofstep_name: &str) {
        if let Some(theorem_progress) = self.seq_theorem_progress.get(theorem_name) {
            theorem_progress.inc(1);
        };

        if let Some(proofstep_progress) = self
            .seq_proofstep_progress
            .get(&(theorem_name.to_string(), proofstep_name.to_string()))
        {
            proofstep_progress.finish();
        }

        log::info!(
            "Successfully finished proofstep {}; Times: {}",
            proofstep_name,
            self.seq_oracle_progress
                .iter()
                .filter_map(|(k, v)| {
                    if k.0 == theorem_name && k.1 == proofstep_name {
                        let duration = v.elapsed();
                        v.finish_and_clear();
                        let seconds = duration.as_secs() % 60;
                        let minutes = (duration.as_secs() / 60) % 60;
                        let hours = (duration.as_secs() / 60) / 60;
                        Some(format!(
                            "{}: [{:0>2}:{:0>2}:{:0>2}]",
                            k.2, hours, minutes, seconds
                        ))
                    } else {
                        None
                    }
                })
                .join("; ")
        );

        self.seq_oracle_progress
            .retain(|k, _v| !(k.0 == theorem_name && k.1 == proofstep_name))
    }

    fn start_oracle(
        &mut self,
        theorem_name: &str,
        proofstep_name: &str,
        oracle_name: &str,
        num_lemmata: u64,
    ) {
        let oracle_progress = self.main_progress.add(ProgressBar::new(num_lemmata));
        oracle_progress.set_style(indicatif_style::oracle_bar());
        oracle_progress.set_message(oracle_name.to_string());

        self.seq_oracle_progress.insert(
            (
                theorem_name.to_string(),
                proofstep_name.to_string(),
                oracle_name.to_string(),
            ),
            oracle_progress,
        );
    }

    fn finish_oracle(&mut self, theorem_name: &str, proofstep_name: &str, oracle_name: &str) {
        if let Some(proofstep_progress) = self
            .seq_proofstep_progress
            .get(&(theorem_name.to_string(), proofstep_name.to_string()))
        {
            proofstep_progress.inc(1);
        };
        if let Some(oracle_progress) = self.seq_oracle_progress.get(&(
            theorem_name.to_string(),
            proofstep_name.to_string(),
            oracle_name.to_string(),
        )) {
            oracle_progress.finish();
        }
    }

    fn start_lemma(
        &mut self,
        theorem_name: &str,
        proofstep_name: &str,
        oracle_name: &str,
        lemma_name: &str,
    ) {
        if let Some(oracle_progress) = self.seq_oracle_progress.get(&(
            theorem_name.to_string(),
            proofstep_name.to_string(),
            oracle_name.to_string(),
        )) {
            oracle_progress.set_message(format!("{oracle_name} (cur: {lemma_name})"));
        }
    }

    fn finish_lemma(
        &mut self,
        theorem_name: &str,
        proofstep_name: &str,
        oracle_name: &str,
        _lemma_name: &str,
    ) {
        if let Some(oracle_progress) = self.seq_oracle_progress.get(&(
            theorem_name.to_string(),
            proofstep_name.to_string(),
            oracle_name.to_string(),
        )) {
            oracle_progress.inc(1);
            oracle_progress.set_message(oracle_name.to_string());
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

pub struct IndicatifBaseUI {
    main_progress: MultiProgress,
}

impl IndicatifBaseUI {
    pub fn new() -> Self {
        let main_progress = MultiProgress::new();
        let logger = env_logger::Builder::from_default_env().build();
        LogWrapper::new(main_progress.clone(), logger)
            .try_init()
            .unwrap();

        IndicatifBaseUI { main_progress }
    }
}

impl BaseUI for IndicatifBaseUI {
    fn into_theorem_ui(self, num_theorems: u64) -> impl TheoremUI {
        let main_progress = self.main_progress;
        let project_progress = if num_theorems > 1 {
            let project_progress = main_progress.add(ProgressBar::new(num_theorems));

            project_progress.set_style(indicatif_style::theorem_bar());
            project_progress.set_message("Project");
            Some(project_progress)
        } else {
            None
        };
        let logger = env_logger::Builder::from_default_env().build();
        LogWrapper::new(main_progress.clone(), logger)
            .try_init()
            .unwrap();

        IndicatifTheoremUI {
            main_progress,
            project_progress,
            seq_theorem_progress: HashMap::new(),
            seq_proofstep_progress: HashMap::new(),
            seq_oracle_progress: HashMap::new(),
        }
    }
}
