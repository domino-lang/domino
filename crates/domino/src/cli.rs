// SPDX-License-Identifier: MIT OR Apache-2.0

use clap::Subcommand;
use sspverif::util::smtsolver::process::SolverVariant;

/// How `domino debug` renders its live exploration progress (on stderr).
#[derive(Copy, Clone, Debug, PartialEq, Eq, clap::ValueEnum)]
pub(crate) enum ProgressMode {
    /// An `indicatif` bar on a terminal, plain stderr log lines when piped.
    Auto,
    /// One terse stderr line per `(left, right)` pair. For logs and CI.
    Plain,
    /// A live `indicatif` two-bar display (goes quiet when stderr is not a TTY).
    Bar,
    /// No progress output at all.
    None,
}

/// Which per-path SMT files `domino debug` writes under `<out>/smt/` (story 11).
#[derive(Copy, Clone, Debug, PartialEq, Eq, clap::ValueEnum)]
pub(crate) enum SmtOutArg {
    /// Write nothing — no `smt/` directory.
    None,
    /// Self-contained, directly runnable `.smt2` for each goal-fails /
    /// inconclusive pair (the default).
    Failures,
    /// Self-contained files for every explored pair (large — one copy of the
    /// base frame per pair).
    All,
    /// `base.smt2` plus the small per-path deltas only; reassemble with `cat`.
    Deltas,
}

#[derive(Subcommand, Debug)]
pub(crate) enum Commands {
    /// Export to LaTeX
    Latex(Latex),

    /// Prove the whole project.
    Prove(Prove),

    /// Reformat file or directory
    Format(Format),

    Proofsteps(Proofsteps),

    /// Symbolically execute both sides of an equivalence proofstep and debug one claim.
    Debug(Debug),

    /// Inline the code of an oracle for both sides of an equivalence proofstep, side by side.
    Inline(Inline),

    /// Export a Domino theorem to an EasyCrypt project.
    Easycrypt(Easycrypt),
}

#[derive(clap::Args, Debug)]
#[clap(author, version, about, long_about = None)]
#[clap(group(clap::ArgGroup::new("ec_mode").args(["check_alignment", "tactics"]).multiple(true)))]
pub(crate) struct Easycrypt {
    /// Path to the Domino project. Defaults to searching the current
    /// directory and its ancestors for an `ssp.toml`.
    #[clap(long)]
    pub(crate) project: Option<std::path::PathBuf>,
    /// Name of the theorem to export. Without it, every theorem in the
    /// project is exported.
    #[clap(long)]
    pub(crate) theorem: Option<String>,
    /// Output directory holding one subdirectory per exported theorem.
    /// Defaults to `<project>/_build/easycrypt`.
    #[clap(long)]
    pub(crate) out: Option<std::path::PathBuf>,
    /// After exporting, start EasyCrypt (`DOMINO_EASYCRYPT`, an `easycrypt cli -json`
    /// binary) and check that the decision skeleton of every oracle's program after
    /// `proc; inline.` aligns with the one the debugger's lowering has. The base case is
    /// admitted, so no prover runs. Exits non-zero on any mismatch and writes
    /// `<out>/<theorem>/alignment.txt`.
    #[clap(long)]
    pub(crate) check_alignment: bool,
    /// After exporting, prove as much of each oracle as possible: run lockstep execution
    /// on it, walk the joint tree alongside a live EasyCrypt (`DOMINO_EASYCRYPT`, an
    /// `easycrypt cli -json` binary), and write the accepted tactics into `Eq_*.ec`. What
    /// could not be closed stays an `admit` labelled with the claim, the id (`J`/`S`) and
    /// what Domino concluded. Writes `Eq_*.report.txt` and `progress/ec-transcript.jsonl`
    /// next to the export. Needs the `cvc5-lib` build. Never run it on 4WHS or yao: it runs
    /// lockstep execution, which is the debugger.
    #[clap(long)]
    pub(crate) tactics: bool,
    /// With `--tactics`: seconds one EasyCrypt sentence may run before it is interrupted.
    #[clap(long, requires = "tactics", default_value_t = 60)]
    pub(crate) ec_timeout: u64,
    /// With `--tactics`: the seconds splitting one leaf by meaning may take before its
    /// remaining parts are admitted (each sentence of a deep goal costs seconds).
    #[clap(long, requires = "tactics", default_value_t = 300)]
    pub(crate) leaf_budget: u64,
    /// With `--tactics`: skip rung 0 (`auto => /#.` on every program goal), so the walk of
    /// the joint tree is exercised even where one tactic closes an oracle. For testing.
    #[clap(long, requires = "tactics", hide = true)]
    pub(crate) no_rung0: bool,
    /// With `--check-alignment` or `--tactics`: only this proofstep (as printed by
    /// `domino proofsteps`). Without `--tactics` the export is not affected.
    #[clap(long, requires = "ec_mode")]
    pub(crate) proofstep: Option<usize>,
    /// With `--check-alignment` or `--tactics`: only this exported oracle; with `--tactics`
    /// the rest keep `+ proc; inline. admit.`.
    #[clap(long, requires = "ec_mode")]
    pub(crate) oracle: Option<String>,
}

#[derive(clap::Args, Debug)]
#[clap(author, version, about, long_about = None)]
pub(crate) struct Inline {
    /// Path to the Domino project. Defaults to searching the current
    /// directory and its ancestors for an `ssp.toml`.
    #[clap(long)]
    pub(crate) path: Option<std::path::PathBuf>,
    /// Name of the theorem the equivalence proofstep belongs to.
    #[clap(long)]
    pub(crate) proof: String,
    /// Index (starting at 0) of the equivalence proofstep within the theorem,
    /// as printed by `domino proofsteps`.
    #[clap(long)]
    pub(crate) proofstep: usize,
    /// Name of the oracle to inline, as exported by the games in the proofstep.
    #[clap(long)]
    pub(crate) oracle: String,
    /// Print without line numbers (useful for diffing two runs).
    #[clap(long)]
    pub(crate) no_line_numbers: bool,
    /// Show the generated EasyCrypt code (as `domino easycrypt` exports it)
    /// instead of the Domino code, on both sides.
    #[clap(long)]
    pub(crate) easycrypt: bool,
}

#[derive(clap::Args, Debug)]
#[clap(author, version, about, long_about = None)]
pub(crate) struct Debug {
    /// Path to the Domino project. Defaults to searching the current
    /// directory and its ancestors for an `ssp.toml`.
    #[clap(long)]
    pub(crate) path: Option<std::path::PathBuf>,
    /// Name of the theorem.
    #[clap(long)]
    pub(crate) proof: String,
    /// Index (starting at 0) of the equivalence proofstep, as printed by `domino proofsteps`.
    #[clap(long)]
    pub(crate) proofstep: usize,
    /// Exported oracle name.
    #[clap(long)]
    pub(crate) oracle: String,
    /// Run lockstep execution on the generated EasyCrypt code instead of the
    /// sequential exploration: both oracles advance together and each decision is
    /// resolved jointly, as an EasyCrypt proof would. Both claims (equal-output and
    /// invariant) are always checked, so `--claim` is not accepted; output goes to
    /// `_build/debug/<theorem>/<left>-<right>/<oracle>/easycrypt/`.
    #[clap(long)]
    pub(crate) easycrypt: bool,
    /// Claim to debug. Required (one claim per run) unless `--easycrypt` is given.
    #[clap(long, required_unless_present = "easycrypt", conflicts_with = "easycrypt")]
    pub(crate) claim: Option<String>,
    /// Do NOT prune unreachable LEFT branches early (default: it does). With this
    /// set, every syntactic left path is explored. Sequential mode only.
    #[clap(long, conflicts_with = "easycrypt")]
    pub(crate) no_check_left: bool,
    /// Do NOT prune unreachable RIGHT branches early (default: it does). This only
    /// disables early branch pruning; the terminal-pair vacuity check that
    /// distinguishes `unreachable` from `verified` still runs unconditionally.
    /// Sequential mode only.
    #[clap(long, conflicts_with = "easycrypt")]
    pub(crate) no_check_right: bool,
    /// Per-query solver timeout in milliseconds (cvc5 `tlimit-per`). A timeout counts
    /// as `unknown` (explored, never pruned, never "verified").
    #[clap(long)]
    pub(crate) timeout: Option<u64>,
    /// Stop after this many explored paths (left paths + right paths per left
    /// path; with `--easycrypt`, joint paths). Unlimited by default; `Ctrl-C` is
    /// the interactive stop.
    #[clap(long)]
    pub(crate) max_paths: Option<usize>,
    /// Live progress while exploring, on stderr (stdout carries only the final
    /// concise report): `auto` shows a bar on a terminal and plain log lines when
    /// piped; `plain` and `bar` force one; `none` is silent.
    #[clap(long, value_enum, default_value_t = ProgressMode::Auto)]
    pub(crate) progress: ProgressMode,
    /// Which per-path SMT files to write under `<out>/smt/`. `failures` (the
    /// default) writes a self-contained, directly runnable `.smt2` for each
    /// goal-fails / inconclusive pair; `all` does it for every pair (large — one
    /// copy of the base frame per pair); `deltas` writes only `base.smt2` plus
    /// the small per-path deltas; `none` writes nothing.
    #[clap(long, value_enum, default_value_t = SmtOutArg::Failures)]
    pub(crate) smt: SmtOutArg,
    /// Also write the raw incremental solver transcript to `transcript.smt2`
    /// (large; for debugging `domino debug` itself).
    #[clap(long)]
    pub(crate) transcript: bool,
    /// Output directory. Defaults to
    /// `_build/debug/<theorem>/<left>-<right>/<oracle>/<claim>/` (with
    /// `--easycrypt`: `.../<oracle>/easycrypt/`).
    #[clap(long)]
    pub(crate) out: Option<std::path::PathBuf>,
}

#[derive(clap::Args, Debug)]
#[clap(author, version, about, long_about = None)]
pub(crate) struct Format {
    /// Input to reformat
    pub(crate) input: Option<std::path::PathBuf>,
}

#[derive(clap::Args, Debug)]
#[clap(author, version, about, long_about = None)]
pub(crate) struct Latex {
    /// Solver for graph layouting
    /// TODO: given we have a default here, it seems impossible to choose none
    #[clap(short, long, default_value = "z3")]
    pub(crate) smtsolver: Option<SolverVariant>,
    /// Path to the Domino project. Defaults to searching the current
    /// directory and its ancestors for an `ssp.toml`.
    #[clap(long)]
    pub(crate) path: Option<std::path::PathBuf>,
}

#[derive(clap::Args, Debug)]
#[clap(author, version, about, long_about = None)]
pub(crate) struct Prove {
    /// Path to the Domino project. Defaults to searching the current
    /// directory and its ancestors for an `ssp.toml`.
    #[clap(long)]
    pub(crate) path: Option<std::path::PathBuf>,
    #[clap(short, long, default_value = "cvc5")]
    pub(crate) smtsolver: SolverVariant,
    #[clap(short, long)]
    pub(crate) transcript: bool,
    // only check randomness mapping is injective
    #[clap(long)]
    pub(crate) injective_randmap: bool,
    #[clap(long)]
    pub(crate) invariant_start: bool,
    #[clap(long)]
    pub(crate) proofstep: Option<usize>,
    #[clap(long)]
    pub(crate) proof: Option<String>,
    #[clap(long)]
    pub(crate) oracle: Option<String>,
    #[clap(long)]
    pub(crate) claim: Option<String>,
    #[clap(long, default_value_t = 1)]
    pub(crate) parallel: usize,
}

#[derive(clap::Args, Debug)]
#[clap(author, version, about, long_about = None)]
pub(crate) struct Proofsteps {
    /// Path to the Domino project. Defaults to searching the current
    /// directory and its ancestors for an `ssp.toml`.
    #[clap(long)]
    pub(crate) path: Option<std::path::PathBuf>,
}
