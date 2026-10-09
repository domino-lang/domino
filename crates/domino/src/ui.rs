// SPDX-License-Identifier: MIT OR Apache-2.0

use std::sync::{Arc, Mutex};

use itertools::Itertools;

use indicatif::{MultiProgress, ProgressBar, ProgressIterator};
use indicatif_log_bridge::LogWrapper;

use sspverif::ui::{
    GamehopUI, LatexUI, ProveClaimUI, ProveGamehopUI, ProveInvariantStartUI, ProveOracleUI,
    ProveTheoremUI, ProveUI, UI,
};

use sspverif::{
    gamehops::{
        equivalence::{error::Result, ResolvedClaim},
        GameHop,
    },
    package::Export,
    parser::ast::Identifier,
    proof::Proof,
    theorem::Theorem,
};

#[derive(Clone)]
pub struct IndicatifUI {
    multi_progress: MultiProgress,
    known_progress: Arc<Mutex<Vec<ProgressBar>>>,
}

impl IndicatifUI {
    pub fn new() -> Self {
        let multi_progress = MultiProgress::new();
        let logger = env_logger::Builder::from_default_env().build();
        LogWrapper::new(multi_progress.clone(), logger)
            .try_init()
            .unwrap();
        Self {
            multi_progress,
            known_progress: Arc::default(),
        }
    }

    fn insert_before(&self, before: &ProgressBar, progress: ProgressBar) -> ProgressBar {
        let progress = self.multi_progress.insert_before(before, progress);

        // we need to keep references to all progress bars as else a
        // println() will remove finished progress bars
        self.known_progress.lock().unwrap().push(progress.clone());
        progress
    }
}

impl Default for IndicatifUI {
    fn default() -> Self {
        Self::new()
    }
}

impl UI for IndicatifUI {
    type GamehopUI = IndicatifGamehopUI;
    type ProveUI = IndicatifProveUI;
    type LatexUI = IndicatifLatexUI;

    fn println(&self, line: &str) -> std::io::Result<()> {
        self.multi_progress.println(line)
    }

    fn gamehop_ui(&self) -> Self::GamehopUI {
        IndicatifGamehopUI {
            main_ui: self.clone(),
        }
    }

    fn prove_ui(&self) -> Self::ProveUI {
        let progress = self.multi_progress.add(ProgressBar::new(0));

        progress.set_style(indicatif_style::theorem_bar());
        progress.set_message("Project");

        IndicatifProveUI {
            main_ui: self.clone(),
            progress,
            reports: Arc::default(),
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
    reports: Arc<Mutex<Vec<String>>>,
}

impl IndicatifProveUI {
    fn insert_before(&self, before: &ProgressBar, progress: ProgressBar) -> ProgressBar {
        self.main_ui.insert_before(before, progress)
    }

    fn tick(&self) {
        self.progress.tick();
    }

    fn add_report(&self, report: String) {
        self.reports.lock().unwrap().push(report)
    }
}

impl ProveUI for IndicatifProveUI {
    type ProveTheoremUI = IndicatifProveTheoremUI;

    fn println(&self, line: &str) -> std::io::Result<()> {
        self.main_ui.println(line)
    }

    fn start(&self) {}
    fn finish(&self) {
        self.progress.finish();

        println!("\n\n# Success. The following Propositions verify:\n");
        for report in self.reports.lock().unwrap().iter() {
            println!("{}", report)
        }
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

    fn finish(&self, theorem: &Theorem) {
        self.prove_ui.progress.inc(1);
        self.tick();
        if let Some(progress) = &self.progress {
            progress.finish()
        }
        for proof in &theorem.proofs {
            self.prove_ui
                .add_report(PropositionBox::new(&theorem.name, proof).into());
        }
    }
    fn skip(&self) {
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
            children: Arc::default(),
        }
    }
}

#[derive(Clone)]
pub struct IndicatifProveGamehopUI {
    theorem_ui: IndicatifProveTheoremUI,
    name: String,
    progress: Option<ProgressBar>,
    children: Arc<Mutex<Vec<ProgressBar>>>,
}

impl IndicatifProveGamehopUI {
    fn insert_before(&self, before: &ProgressBar, progress: ProgressBar) -> ProgressBar {
        self.children.lock().unwrap().push(progress.clone());
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
        if let Some(progress) = &self.theorem_ui.progress {
            progress.inc(1);
        }
        if let Some(progress) = &self.progress {
            progress.set_length(1);
            progress.inc(1);
            progress.finish();
        }
        self.tick()
    }

    fn start(&mut self) {
        if let Some(progress) = &self.theorem_ui.progress {
            let new_progress = self.theorem_ui.insert_before(progress, ProgressBar::new(0));
            new_progress.set_style(indicatif_style::gamehop_bar());
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
            for child in self.children.lock().unwrap().iter() {
                child.finish_and_clear();
            }
            progress.finish();
        }
    }

    fn start_oracle(&self, export: &Export) -> Self::ProveOracleUI {
        if let Some(progress) = &self.progress {
            progress.inc_length(1);
        }
        self.tick();

        IndicatifProveOracleUI {
            gamehop_ui: self.clone(),
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
            gamehop_ui: self.clone(),
            name,
            progress: None,
        }
    }
}

#[derive(Clone)]
pub struct IndicatifProveOracleUI {
    gamehop_ui: IndicatifProveGamehopUI,
    name: String,
    progress: Option<ProgressBar>,
}

impl IndicatifProveOracleUI {
    fn insert_before(&self, before: &ProgressBar, progress: ProgressBar) -> ProgressBar {
        self.gamehop_ui.insert_before(before, progress)
    }
    fn tick(&self) {
        self.gamehop_ui.tick();
        if let Some(progress) = &self.progress {
            progress.tick();
        }
    }
    fn start(&mut self) {
        if let Some(progress) = &self.gamehop_ui.progress {
            let new_progress = self.insert_before(progress, ProgressBar::new(0));
            new_progress.set_style(indicatif_style::oracle_bar());
            new_progress.set_message(self.name.clone());
            self.progress = Some(new_progress);
            self.tick();
        }
    }

    fn finish(&self) {
        if let Some(progress) = &self.gamehop_ui.progress {
            progress.inc(1);
        }
        self.tick();
    }
    fn println(&self, line: &str) -> std::io::Result<()> {
        self.gamehop_ui.println(line)
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
        self.gamehop_ui.println(line)
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
        self.oracle_ui
            .println(&format!(
                "{} {} {} failed",
                console::style("✘").bold().red(),
                self.oracle_ui.name,
                self.name
            ))
            .unwrap();

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

pub struct IndicatifGamehopUI {
    main_ui: IndicatifUI,
}

impl GamehopUI for IndicatifGamehopUI {
    fn println(&self, line: &str) -> std::io::Result<()> {
        self.main_ui.println(line)
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

    pub(super) fn gamehop_bar() -> ProgressStyle {
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

struct PropositionBox<'a> {
    theorem: &'a str,
    proof: &'a Proof<'a>,
}

impl<'a> PropositionBox<'a> {
    fn new(theorem: &'a str, proof: &'a Proof) -> Self {
        Self { theorem, proof }
    }

    fn reductions(&self) -> String {
        self.proof
            .reductions()
            .enumerate()
            .map(|(rednum, _red)| format!("R{}", rednum + 1))
            .join(", ")
    }
    fn reduction_advantages(&self) -> impl Iterator<Item = String> + use<'a> {
        self.proof.reductions().enumerate().map(|(rednum, red)| {
            format!(
                "Adv(A->R{}, {}, {})",
                rednum + 1,
                red.right().assumption_game_instance_name().as_str(),
                red.left().assumption_game_instance_name().as_str(),
            )
        })
    }

    fn intro(&self) -> Vec<String> {
        wrap_lines(
            &format!(
                "For all adversaries A, there are reductions {} such that",
                self.reductions()
            ),
            93,
        )
    }

    fn advantages(&self) -> Vec<String> {
        let mut lines = Vec::new();
        let mut red_adv = self.reduction_advantages();
        let leftstring = format!(
            "Adv(A, {}, {}) ",
            self.proof.left_name(),
            self.proof.right_name()
        );
        let padstring = console::pad_str(
            "",
            console::measure_text_width(&leftstring),
            console::Alignment::Left,
            None,
        );

        if let Some(adv) = red_adv.next() {
            lines.push(format!("{leftstring}≤   {}", adv));
        } else {
            lines.push(format!("{leftstring}= 0",));
        }

        lines.extend(red_adv.map(|adv| format!("{padstring}  + {adv}")));

        lines
    }

    fn conclusion(&self) -> Vec<String> {
        let conjectures = self
            .proof
            .conjectures()
            .map(|conj| {
                format!(
                    "{} ~ {}",
                    conj.left_name().as_str(),
                    conj.right_name().as_str()
                )
            })
            .join(", ");

        if conjectures.is_empty() {
            Vec::new()
        } else {
            wrap_lines(&format!("using conjectures {conjectures}"), 93)
        }
    }
}

fn wrap_lines(input: &str, len: usize) -> Vec<String> {
    let mut lines = Vec::new();
    let mut worditer = input.split(' ');

    let mut next = if let Some(first) = worditer.next() {
        first.to_string()
    } else {
        return Vec::new();
    };

    for word in worditer {
        let candidate = format!("{next} {word}");
        if console::measure_text_width(&candidate) < len {
            next = candidate;
        } else {
            lines.push(next);
            next = word.to_string();
        }
    }
    lines.push(next);

    lines
}

impl From<PropositionBox<'_>> for String {
    fn from(val: PropositionBox) -> Self {
        console::style(
            std::iter::once(format!(
                "╔{}╗",
                console::pad_str_with(
                    &format!(" {}: {} ", val.theorem, val.proof.name),
                    95,
                    console::Alignment::Left,
                    None,
                    '═'
                )
            ))
            .chain(val.intro().into_iter().map(|line| {
                format!(
                    "║ {} ║",
                    console::pad_str(&line, 93, console::Alignment::Left, None)
                )
            }))
            .chain(val.advantages().into_iter().map(|line| {
                format!(
                    "║ {} ║",
                    console::pad_str(&line, 93, console::Alignment::Left, None)
                )
            }))
            .chain(val.conclusion().into_iter().map(|line| {
                format!(
                    "║ {} ║",
                    console::pad_str(&line, 93, console::Alignment::Left, None)
                )
            }))
            .chain(std::iter::once(format!(
                "╚{}╝",
                console::pad_str_with("", 95, console::Alignment::Left, None, '═')
            )))
            .join("\n"),
        )
        .green()
        .to_string()
    }
}
