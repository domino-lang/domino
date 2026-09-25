// SPDX-License-Identifier: MIT OR Apache-2.0

//! `domino easycrypt --check-alignment` (story 26 §3.4).
//!
//! For each equivalence of an exported theorem: open an EasyCrypt session, feed the `Eq_*.ec`
//! file up to and including `call (…); last first.` (the base case is admitted instead of
//! proved, so no prover runs), then for each oracle pick its goal **from the JSON** (the
//! `equivF` of that oracle's procedures, never by position), send `proc; inline.`, align both
//! programs with the lowering's IR, and `undo`.
//!
//! [`align_goal`] is the piece story 27 reuses on every oracle it translates.

use std::fmt::Write as _;
use std::path::Path;
use std::time::{Duration, Instant};

use thiserror::Error;

use crate::debug::ir::InlinedOracle;
use crate::theorem::Theorem;
use crate::transforms::theorem_transforms::EasyCryptTransform;
use crate::transforms::TheoremTransform;
use crate::writers::easycrypt::export::{EquivalenceReport, ExportedTheorem};
use crate::writers::easycrypt::game::router_module_and_flag;
use crate::writers::easycrypt::lower::inline_oracle_ec;
use crate::writers::easycrypt::names::{NameKind, Names};
use crate::writers::easycrypt::EcExportError;

use super::align::{align_router, Alignment, Mismatch, PathStep};
use super::json::{Goal, Response, Status};
use super::session::{split_sentences, Session, SessionError};
use super::skeleton::{ec_skeleton, ir_skeleton, Arm};

#[derive(Debug, Error)]
pub enum CheckError {
    #[error(transparent)]
    Session(#[from] SessionError),
    #[error(transparent)]
    Export(#[from] EcExportError),
    #[error(transparent)]
    Name(#[from] crate::writers::easycrypt::names::NameError),
    #[error(transparent)]
    Transform(#[from] crate::transforms::theorem_transforms::EquivalenceTransformError),
    #[error("EasyCrypt rejected `{sentence}` of {file}: {msg}")]
    Rejected {
        file: String,
        sentence: String,
        msg: String,
    },
    #[error("{file} has no `call (…); last first.` sentence")]
    NoCallSentence { file: String },
    #[error("the export has no file {file}")]
    MissingFile { file: String },
    #[error("the theorem has no oracle `{oracle}` in equivalence {file}")]
    NoSuchOracle { oracle: String, file: String },
}

#[derive(Debug, Clone, Default)]
pub struct CheckOptions {
    /// Only this proofstep (index into the theorem's game hops).
    pub proofstep: Option<usize>,
    /// Only this exported oracle.
    pub oracle: Option<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SideName {
    Left,
    Right,
}

#[derive(Debug, Clone)]
pub struct SideAlignment {
    pub side: SideName,
    /// Number of statements at the top level of EasyCrypt's program (assignments included).
    pub ec_top_statements: usize,
    pub alignment: Alignment,
}

/// The outcome for one oracle of one equivalence.
#[derive(Debug, Clone)]
pub struct OracleAlignment {
    pub oracle: String,
    /// Set when EasyCrypt could not be brought to the goal to compare (no goal for the oracle,
    /// or `proc; inline.` failed): this counts as a failure.
    pub problem: Option<String>,
    pub sides: Vec<SideAlignment>,
    pub elapsed: Duration,
}

impl OracleAlignment {
    pub fn is_aligned(&self) -> bool {
        self.problem.is_none() && self.sides.iter().all(|s| s.alignment.is_aligned())
    }
}

#[derive(Debug, Clone)]
pub struct EquivalenceAlignment {
    pub proofstep: usize,
    pub proof_file: String,
    pub left: String,
    pub right: String,
    pub oracles: Vec<OracleAlignment>,
    pub elapsed: Duration,
}

#[derive(Debug, Clone)]
pub struct TheoremAlignment {
    pub theorem: String,
    pub equivalences: Vec<EquivalenceAlignment>,
    pub elapsed: Duration,
}

impl TheoremAlignment {
    pub fn oracles_checked(&self) -> usize {
        self.equivalences.iter().map(|e| e.oracles.len()).sum()
    }

    pub fn mismatch_count(&self) -> usize {
        self.equivalences
            .iter()
            .flat_map(|e| &e.oracles)
            .map(|o| {
                usize::from(o.problem.is_some())
                    + o.sides
                        .iter()
                        .map(|s| s.alignment.mismatches.len())
                        .sum::<usize>()
            })
            .sum()
    }

    pub fn is_aligned(&self) -> bool {
        self.mismatch_count() == 0
    }
}

/// Aligns the program of a goal that is an `equivS` after `proc; inline.` with the two IRs.
/// `left`/`right` pair each side's inlined oracle with the router's abort flag as EasyCrypt
/// prints it. `None` if the goal is not an `equivS`.
pub fn align_goal(
    goal: &Goal,
    left: (&InlinedOracle, &str),
    right: (&InlinedOracle, &str),
) -> Option<[SideAlignment; 2]> {
    if goal.concl.kind != "equivS" {
        return None;
    }
    let side = |name: SideName, ec: &super::json::Side, (ir, flag): (&InlinedOracle, &str)| {
        SideAlignment {
            side: name,
            ec_top_statements: ec.stmt.len(),
            alignment: align_router(&ec_skeleton(&ec.stmt), &ir_skeleton(ir), flag),
        }
    };
    Some([
        side(SideName::Left, goal.concl.left.as_ref()?, left),
        side(SideName::Right, goal.concl.right.as_ref()?, right),
    ])
}

/// The sentences of `file` up to and including the one that ends `last first.`.
pub(crate) fn sentences_until_call(file: &str, source: &str) -> Result<Vec<String>, CheckError> {
    let mut out = Vec::new();
    for sentence in split_sentences(source) {
        let done = sentence.starts_with("call") && sentence.ends_with("last first.");
        out.push(sentence);
        if done {
            return Ok(out);
        }
    }
    Err(CheckError::NoCallSentence {
        file: file.to_string(),
    })
}

pub(crate) fn ok_or_reject<'r>(
    response: &'r Response,
    file: &str,
    sentence: &str,
) -> Result<&'r Response, CheckError> {
    if response.status == Status::Ok {
        return Ok(response);
    }
    Err(CheckError::Rejected {
        file: file.to_string(),
        sentence: sentence.to_string(),
        msg: response
            .error
            .as_ref()
            .map_or_else(|| format!("{:?}", response.status), |e| e.msg.clone()),
    })
}

/// Checks the alignment of every selected equivalence of `exported` (the export of `theorem`,
/// already written to `out_dir`, the theorem's own output directory).
pub fn check_alignment(
    theorem: &Theorem<'_>,
    exported: &ExportedTheorem,
    out_dir: &Path,
    options: &CheckOptions,
) -> Result<TheoremAlignment, CheckError> {
    let started = Instant::now();
    let (theorem_ec, _aux) = EasyCryptTransform.transform_theorem(theorem)?;
    let out_dir = std::fs::canonicalize(out_dir).unwrap_or_else(|_| out_dir.to_path_buf());

    let mut equivalences = Vec::new();
    for eq in &exported.equivalences {
        if options.proofstep.is_some_and(|p| p != eq.proofstep) {
            continue;
        }
        equivalences.push(check_equivalence(
            &theorem_ec,
            exported,
            eq,
            &out_dir,
            options,
        )?);
    }
    Ok(TheoremAlignment {
        theorem: theorem.name.clone(),
        equivalences,
        elapsed: started.elapsed(),
    })
}

/// What both story 26's alignment check and story 27's tactic generation need to know about one
/// exported equivalence: its two game instances (after `EasyCryptTransform`), their routers'
/// abort flags as EasyCrypt prints them, and the exported oracles with their EasyCrypt names.
pub(crate) struct EquivalenceSetup<'t> {
    pub left_inst: &'t crate::theorem::GameInstance,
    pub right_inst: &'t crate::theorem::GameInstance,
    pub left_router: String,
    pub right_router: String,
    pub left_flag: String,
    pub right_flag: String,
    /// `(exported name, EasyCrypt's procedure name)`, in the game interface's order.
    pub oracles: Vec<(String, String)>,
}

pub(crate) fn equivalence_setup<'t>(
    theorem_ec: &'t Theorem<'_>,
    eq: &EquivalenceReport,
) -> Result<EquivalenceSetup<'t>, CheckError> {
    let left_inst = theorem_ec
        .find_game_instance(&eq.left_name)
        .expect("an exported equivalence names a game instance of its theorem");
    let right_inst = theorem_ec
        .find_game_instance(&eq.right_name)
        .expect("an exported equivalence names a game instance of its theorem");
    let (left_router, flag) = router_module_and_flag(left_inst.game())?;
    let (right_router, _) = router_module_and_flag(right_inst.game())?;
    let mut oracles = Vec::new();
    for export in &left_inst.game().exports {
        let proc_name = Names::new().mangle(NameKind::Proc, export.name())?;
        oracles.push((export.name().to_string(), proc_name));
    }
    Ok(EquivalenceSetup {
        left_inst,
        right_inst,
        left_flag: format!("{left_router}.{flag}"),
        right_flag: format!("{right_router}.{flag}"),
        left_router,
        right_router,
        oracles,
    })
}

impl EquivalenceSetup<'_> {
    /// The exported oracle whose `equivF` `goal` is, identified from the JSON: the procedure
    /// name and both routers.
    pub(crate) fn oracle_of_goal(&self, goal: &Goal) -> Option<String> {
        let (l, r) = goal.concl.equiv_procs()?;
        self.oracles
            .iter()
            .find(|(_, proc_name)| {
                *proc_name == l.name
                    && l.name == r.name
                    && l.top.ends_with(&self.left_router)
                    && r.top.ends_with(&self.right_router)
            })
            .map(|(name, _)| name.clone())
    }
}

fn check_equivalence(
    theorem_ec: &Theorem<'_>,
    exported: &ExportedTheorem,
    eq: &EquivalenceReport,
    out_dir: &Path,
    options: &CheckOptions,
) -> Result<EquivalenceAlignment, CheckError> {
    let started = Instant::now();
    let file = eq.proof_file.clone();
    let source = exported
        .files
        .get(Path::new(&file))
        .ok_or_else(|| CheckError::MissingFile { file: file.clone() })?;

    let setup = equivalence_setup(theorem_ec, eq)?;
    let (left_inst, right_inst) = (setup.left_inst, setup.right_inst);
    let (left_flag, right_flag) = (&setup.left_flag, &setup.right_flag);
    let oracles = &setup.oracles;
    if let Some(wanted) = &options.oracle {
        if !oracles.iter().any(|(name, _)| name == wanted) {
            return Err(CheckError::NoSuchOracle {
                oracle: wanted.clone(),
                file,
            });
        }
    }

    let mut session = Session::start(out_dir)?;
    for sentence in sentences_until_call(&file, source)? {
        let response = session.send(&sentence)?;
        ok_or_reject(response, &file, &sentence)?;
    }

    let mut results: Vec<OracleAlignment> = Vec::new();
    // The goals are handled from the first one on; each is identified from its JSON.
    while let Some(goal) = session.goals().first() {
        let target = setup.oracle_of_goal(goal);
        if let Some(oracle) = target.filter(|name| {
            options
                .oracle
                .as_ref()
                .is_none_or(|wanted| wanted == name)
        }) {
            let began = Instant::now();
            let result = align_one(
                &mut session,
                &file,
                left_inst,
                right_inst,
                &oracle,
                (left_flag, right_flag),
            )?;
            results.push(OracleAlignment {
                elapsed: began.elapsed(),
                ..result
            });
        }
        // the base case, a goal of another oracle, or the one just compared: admitted
        let response = session.send("admit.")?;
        ok_or_reject(response, &file, "admit.")?;
    }

    // every selected oracle must have had its goal
    for (name, _) in oracles {
        if options.oracle.as_ref().is_some_and(|w| w != name) {
            continue;
        }
        if !results.iter().any(|r| &r.oracle == name) {
            results.push(OracleAlignment {
                oracle: name.clone(),
                problem: Some("no goal for this oracle after `call (…); last first.`".into()),
                sides: vec![],
                elapsed: Duration::ZERO,
            });
        }
    }
    let position = |name: &str| oracles.iter().position(|(n, _)| n == name);
    results.sort_by_key(|r| position(&r.oracle));

    Ok(EquivalenceAlignment {
        proofstep: eq.proofstep,
        proof_file: file,
        left: eq.left_name.clone(),
        right: eq.right_name.clone(),
        oracles: results,
        elapsed: started.elapsed(),
    })
}

/// Sends `proc; inline.` on the first goal, aligns, and undoes.
fn align_one(
    session: &mut Session,
    file: &str,
    left_inst: &crate::theorem::GameInstance,
    right_inst: &crate::theorem::GameInstance,
    oracle: &str,
    (left_flag, right_flag): (&str, &str),
) -> Result<OracleAlignment, CheckError> {
    let before = session.last().map_or(0, |r| r.state);
    let left_ir = inline_oracle_ec(left_inst, oracle)?;
    let right_ir = inline_oracle_ec(right_inst, oracle)?;

    let response = session.send("proc; inline.")?;
    let mut out = OracleAlignment {
        oracle: oracle.to_string(),
        problem: None,
        sides: vec![],
        elapsed: Duration::ZERO,
    };
    if response.status != Status::Ok {
        out.problem = Some(format!(
            "`proc; inline.` failed: {}",
            response.error.as_ref().map_or("", |e| e.msg.as_str())
        ));
    } else {
        match session
            .goals()
            .first()
            .and_then(|g| align_goal(g, (&left_ir, left_flag), (&right_ir, right_flag)))
        {
            Some(sides) => out.sides = sides.into(),
            None => out.problem = Some("`proc; inline.` did not give an equivS goal".into()),
        }
    }
    let response = session.undo_to(before)?;
    ok_or_reject(response, file, "undo")?;
    Ok(out)
}

fn describe_path(path: &[PathStep]) -> String {
    if path.is_empty() {
        return "top level".to_string();
    }
    path.iter()
        .map(|step| {
            let arm = match step.arm {
                Arm::Then => "then",
                Arm::Else => "else",
            };
            format!("@L{} {arm}", step.ir_label)
        })
        .collect::<Vec<_>>()
        .join(" > ")
}

pub(crate) fn describe_mismatch(m: &Mismatch) -> String {
    let mut s = format!("{} at {}", m.kind.slug(), describe_path(&m.path));
    if let Some(ec) = &m.ec {
        let _ = write!(s, "\n        EasyCrypt: {}", ec.replace('\n', " "));
    }
    if let Some(ir) = &m.ir {
        let _ = write!(s, "\n        Domino IR: {ir}");
    }
    s
}

impl TheoremAlignment {
    /// The report `domino easycrypt --check-alignment` prints and writes to `alignment.txt`.
    pub fn render(&self) -> String {
        let mut out = String::new();
        let _ = writeln!(out, "alignment of theorem {}", self.theorem);
        for eq in &self.equivalences {
            let _ = writeln!(
                out,
                "  proofstep {}: {} ~ {} ({})",
                eq.proofstep, eq.left, eq.right, eq.proof_file
            );
            for o in &eq.oracles {
                if o.is_aligned() {
                    let decisions: usize = o.sides.iter().map(|s| s.alignment.matches.len()).sum();
                    let _ = writeln!(
                        out,
                        "    {:<16} aligned ({decisions} decisions, {:.1}s)",
                        o.oracle,
                        o.elapsed.as_secs_f32()
                    );
                    continue;
                }
                let _ = writeln!(out, "    {:<16} MISMATCH", o.oracle);
                if let Some(problem) = &o.problem {
                    let _ = writeln!(out, "      problem: {problem}");
                }
                for side in &o.sides {
                    for m in &side.alignment.mismatches {
                        let name = match side.side {
                            SideName::Left => "left",
                            SideName::Right => "right",
                        };
                        let _ = writeln!(out, "      {name}: {}", describe_mismatch(m));
                    }
                }
            }
        }
        let _ = writeln!(
            out,
            "{} oracles checked, {} mismatches, {:.1}s",
            self.oracles_checked(),
            self.mismatch_count(),
            self.elapsed.as_secs_f32()
        );
        out
    }
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use super::*;
    use crate::easycrypt::align::MismatchKind;
    use crate::easycrypt::json::parse_response;
    use crate::easycrypt::session::json_binary_configured;
    use crate::easycrypt::skeleton::{ec_skeleton, ir_skeleton};
    use crate::project::{DirectoryFiles, DirectoryProject, Project};
    use crate::writers::easycrypt::export::{export_theorem, write_files};

    /// EasyCrypt's answer to `proc; inline.` on hello-world's `UsefulOracle`
    /// (`medium_composition ~ small_composition`), recorded with story 25's binary.
    const FIXTURE: &str =
        include_str!("../../testdata/easycrypt/story25/hello_world_useful_oracle_after_inline.json");

    #[test]
    fn the_recorded_goal_aligns_with_the_lowering_without_easycrypt() {
        let dir = PathBuf::from("example-projects/hello-world");
        let files = DirectoryFiles::load(&dir).unwrap();
        let project = DirectoryProject::load(dir, &files).unwrap();
        let theorem = project.get_theorem("Proof").unwrap();
        let (theorem_ec, _) = EasyCryptTransform.transform_theorem(theorem).unwrap();
        let left = inline_oracle_ec(
            theorem_ec.find_game_instance("medium_composition").unwrap(),
            "UsefulOracle",
        )
        .unwrap();
        let right = inline_oracle_ec(
            theorem_ec.find_game_instance("small_composition").unwrap(),
            "UsefulOracle",
        )
        .unwrap();
        let response = parse_response(FIXTURE).unwrap();
        let goal = &response.proof.as_ref().unwrap().goals[0];

        let [l, r] = align_goal(
            goal,
            (&left, "Game_MediumComposition.abort_flag"),
            (&right, "Game_SmallComposition.abort_flag"),
        )
        .unwrap();
        assert!(l.alignment.is_aligned(), "{:?}", l.alignment);
        assert!(r.alignment.is_aligned(), "{:?}", r.alignment);
        // the sampling is tied to EasyCrypt's own `rnd`, with its name
        let sample_labels: Vec<_> = l
            .alignment
            .matches
            .iter()
            .filter(|m| m.ec.lvalue.is_some())
            .collect();
        assert_eq!(sample_labels.len(), 1);
        assert_eq!(sample_labels[0].ec.lvalue.as_deref(), Some("rand"));

        // a program with an unexpected extra sampling is a mismatch, not a silent match
        let mut ir = ir_skeleton(&left);
        ir.remove(0);
        let ec = ec_skeleton(&goal.concl.left.as_ref().unwrap().stmt);
        let a = align_router(&ec, &ir, "Game_MediumComposition.abort_flag");
        assert!(!a.is_aligned());
        assert_eq!(a.mismatches[0].kind, MismatchKind::ExtraEcDecision);

        // and the wrong router is a router-shape mismatch
        let a = align_router(&ec, &ir_skeleton(&left), "Game_Other.abort_flag");
        assert_eq!(a.mismatches[0].kind, MismatchKind::RouterShape);
    }

    #[test]
    fn hello_world_aligns_in_a_live_easycrypt() {
        if !json_binary_configured() {
            eprintln!("DOMINO_EASYCRYPT not set, skipping");
            return;
        }
        let dir = PathBuf::from("example-projects/hello-world");
        let files = DirectoryFiles::load(&dir).unwrap();
        let project = DirectoryProject::load(dir, &files).unwrap();
        let theorem = project.get_theorem("Proof").unwrap();
        let exported = export_theorem(theorem, &project).unwrap();
        let out = tempfile::tempdir().unwrap();
        write_files(out.path(), &exported.files).unwrap();

        let alignment =
            check_alignment(theorem, &exported, out.path(), &CheckOptions::default()).unwrap();
        assert_eq!(alignment.oracles_checked(), 1);
        assert!(alignment.is_aligned(), "{}", alignment.render());
        assert!(alignment.render().contains("UsefulOracle"));

        // an unknown oracle is refused before EasyCrypt is started
        let err = check_alignment(
            theorem,
            &exported,
            out.path(),
            &CheckOptions {
                oracle: Some("Nope".into()),
                proofstep: None,
            },
        )
        .unwrap_err();
        assert!(matches!(err, CheckError::NoSuchOracle { .. }));

        // a proofstep that is not an equivalence selects nothing
        let none = check_alignment(
            theorem,
            &exported,
            out.path(),
            &CheckOptions {
                oracle: None,
                proofstep: Some(99),
            },
        )
        .unwrap();
        assert_eq!(none.oracles_checked(), 0);
    }
}
