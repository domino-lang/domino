use indicatif::{MultiProgress, ProgressBar};
use indicatif_log_bridge::LogWrapper;
use itertools::Itertools;
use std::collections::HashMap;

use super::TheoremUI;

pub(crate) struct IndicatifTheoremUI {
    main_progress: MultiProgress,
    project_progress: Option<ProgressBar>,
    seq_theorem_progress: HashMap<String, ProgressBar>,
    seq_theoremstep_progress: HashMap<(String, String), ProgressBar>,
    seq_oracle_progress: HashMap<(String, String, String), ProgressBar>,
}

impl IndicatifTheoremUI {
    pub(crate) fn new(num_theorems: u64) -> Self {
        let main_progress = MultiProgress::new();
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
            seq_theoremstep_progress: HashMap::new(),
            seq_oracle_progress: HashMap::new(),
        }
    }
}

impl TheoremUI for IndicatifTheoremUI {
    fn println(&self, line: &str) -> std::io::Result<()> {
        self.main_progress.println(line)
    }

    fn start_theorem(&mut self, theorem_name: &str, num_theoremsteps: u64) {
        let theorem_progress = self.main_progress.add(ProgressBar::new(num_theoremsteps));

        theorem_progress.set_style(indicatif_style::theorem_bar());
        theorem_progress.set_message(theorem_name.to_string());

        self.seq_theorem_progress
            .insert(theorem_name.to_string(), theorem_progress);
    }

    fn finish_theorem(&mut self, theorem_name: &str) {
        if let Some(project_progress) = &self.project_progress {
            project_progress.inc(1);
        };
        if let Some(theorem_progress) = self.seq_theorem_progress.get(&(theorem_name.to_string())) {
            theorem_progress.finish();
        }
    }

    fn start_theoremstep(&mut self, theorem_name: &str, theoremstep_name: &str) {
        let theoremstep_progress = self.main_progress.add(ProgressBar::new(1));
        theoremstep_progress.set_style(indicatif_style::theoremstep_bar());
        theoremstep_progress.set_message(theoremstep_name.to_string());

        self.seq_theoremstep_progress.insert(
            (theorem_name.to_string(), theoremstep_name.to_string()),
            theoremstep_progress,
        );
    }

    fn theoremstep_is_reduction(&mut self, theorem_name: &str, theoremstep_name: &str) {
        if let Some(theoremstep_progress) = self
            .seq_theoremstep_progress
            .get(&(theorem_name.to_string(), theoremstep_name.to_string()))
        {
            theoremstep_progress.set_length(1);
            theoremstep_progress.inc(1);
            theoremstep_progress.tick();
        } else {
            unreachable!("{theorem_name} -- {theoremstep_name}");
        };
    }

    fn theoremstep_set_oracles(&mut self, theorem_name: &str, theoremstep_name: &str, num_oracles: u64) {
        if let Some(theoremstep_progress) = self
            .seq_theoremstep_progress
            .get(&(theorem_name.to_string(), theoremstep_name.to_string()))
        {
            theoremstep_progress.set_length(num_oracles);
            theoremstep_progress.tick();
        } else {
            unreachable!("{theorem_name} -- {theoremstep_name}");
        };
    }

    fn finish_theoremstep(&mut self, theorem_name: &str, theoremstep_name: &str) {
        if let Some(theorem_progress) = self.seq_theorem_progress.get(&(theorem_name.to_string())) {
            theorem_progress.inc(1);
        };

        if let Some(theoremstep_progress) = self
            .seq_theoremstep_progress
            .get(&(theorem_name.to_string(), theoremstep_name.to_string()))
        {
            theoremstep_progress.finish();
        }

        log::info!(
            "Successfully finished theoremstep {}; Times: {}",
            theoremstep_name,
            self.seq_oracle_progress
                .iter()
                .filter_map(|(k, v)| {
                    if k.0 == theorem_name && k.1 == theoremstep_name {
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
            .retain(|k, _v| !(k.0 == theorem_name && k.1 == theoremstep_name))
    }

    fn start_oracle(
        &mut self,
        theorem_name: &str,
        theoremstep_name: &str,
        oracle_name: &str,
        num_lemmata: u64,
    ) {
        let oracle_progress = self.main_progress.add(ProgressBar::new(num_lemmata));
        oracle_progress.set_style(indicatif_style::oracle_bar());
        oracle_progress.set_message(oracle_name.to_string());

        self.seq_oracle_progress.insert(
            (
                theorem_name.to_string(),
                theoremstep_name.to_string(),
                oracle_name.to_string(),
            ),
            oracle_progress,
        );
    }

    fn finish_oracle(&mut self, theorem_name: &str, theoremstep_name: &str, oracle_name: &str) {
        if let Some(theoremstep_progress) = self
            .seq_theoremstep_progress
            .get(&(theorem_name.to_string(), theoremstep_name.to_string()))
        {
            theoremstep_progress.inc(1);
        };
        if let Some(oracle_progress) = self.seq_oracle_progress.get(&(
            theorem_name.to_string(),
            theoremstep_name.to_string(),
            oracle_name.to_string(),
        )) {
            oracle_progress.finish();
        }
    }

    fn start_lemma(
        &mut self,
        theorem_name: &str,
        theoremstep_name: &str,
        oracle_name: &str,
        lemma_name: &str,
    ) {
        if let Some(oracle_progress) = self.seq_oracle_progress.get(&(
            theorem_name.to_string(),
            theoremstep_name.to_string(),
            oracle_name.to_string(),
        )) {
            oracle_progress.set_message(format!("{oracle_name} (cur: {lemma_name})"));
        }
    }

    fn finish_lemma(
        &mut self,
        theorem_name: &str,
        theoremstep_name: &str,
        oracle_name: &str,
        _lemma_name: &str,
    ) {
        if let Some(oracle_progress) = self.seq_oracle_progress.get(&(
            theorem_name.to_string(),
            theoremstep_name.to_string(),
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

    pub(super) fn theoremstep_bar() -> ProgressStyle {
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
