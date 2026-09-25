// SPDX-License-Identifier: MIT OR Apache-2.0

//! The claims of an oracle, checked at a terminal pair (story 19).
//!
//! An **all-claim run** explores an oracle once and asks every claim of its obligation set
//! about each terminal pair. The pair's path conditions and what every claim shares are on the
//! solver stack already; a claim adds only its **own declared dependencies** (`no-abort`,
//! project lemmas, …) and its negated goal, in one `push` / `check-sat` / `pop`.
//!
//! Verdicts are meant to be comparable to `domino prove`'s, which grants each claim its own
//! dependencies, so the claim's dependencies are never dropped. What moving them from the base
//! frame to the terminal pair adds is *scope* for [`Verdict::Unreachable`]: the pair may be
//! infeasible ([`Unreachability::PairInfeasible`]), or feasible with this claim's premise
//! false on it ([`Unreachability::DependencyFalse`]).

use std::path::Path;

use crate::debug::driver::{
    write_model, ClaimVerdict, DebugError, Unreachability, Verdict,
};
use crate::debug::layout::Layout;
use crate::gamehops::equivalence::Equivalence;
use crate::theorem::Claim;
use crate::util::smtsolver::{SmtSolver, SmtSolverResponse};
use crate::writers::smt::contexts::EquivalenceContext;
use crate::writers::smt::exprs::SmtExpr;

/// A claim of the oracle's obligation set, ready to be checked at a terminal pair.
pub struct ClaimQuery {
    pub name: String,
    /// The claim's own declared dependencies, by name, with the assertion each one is —
    /// what a single-claim run has in its base frame.
    pub dependencies: Vec<(String, SmtExpr)>,
    /// `(assert (not <goal>))`.
    pub negated: SmtExpr,
}

impl ClaimQuery {
    pub fn of(eqctx: &EquivalenceContext<'_>, claim: &Claim, oracle: &str) -> Self {
        let assumptions = eqctx.emit_claim_own_assumptions(claim, oracle);
        debug_assert_eq!(assumptions.len(), claim.dependencies().len());
        Self {
            name: claim.name().to_string(),
            dependencies: claim
                .dependencies()
                .iter()
                .cloned()
                .zip(assumptions)
                .collect(),
            negated: eqctx.emit_claim_goal_negated(claim, oracle),
        }
    }

    /// A claim with no dependencies and an explicit negated goal (the EasyCrypt listing's
    /// `equal-output`, which is a grouping of two claims).
    pub fn without_dependencies(name: &str, negated: SmtExpr) -> Self {
        Self {
            name: name.to_string(),
            dependencies: Vec::new(),
            negated,
        }
    }
}

/// The full obligation set of `oracle`: what `domino prove` discharges. `equal-aborts`,
/// `same-output` and `invariant` come first, then the rest of the proof tree in declaration
/// order, then the generated package/game invariant claims — so a report reads like `prove`'s.
pub(crate) fn obligations(
    eqctx: &EquivalenceContext<'_>,
    eq: &Equivalence,
    oracle: &str,
) -> Vec<Claim> {
    const FIRST: [&str; 3] = ["equal-aborts", "same-output", "invariant"];
    let mut ranked: Vec<(usize, Claim)> = eq
        .proof_tree_by_oracle_name(oracle)
        .into_iter()
        .map(|claim| {
            let rank = FIRST
                .iter()
                .position(|name| *name == claim.name())
                .unwrap_or(FIRST.len());
            (rank, claim)
        })
        .collect();
    ranked.extend(
        eqctx
            .generate_game_or_package_invariant_claims()
            .into_iter()
            .map(|claim| (FIRST.len() + 1, claim)),
    );
    ranked.sort_by_key(|(rank, _)| *rank);
    ranked.into_iter().map(|(_, claim)| claim).collect()
}

/// Which side(s) of a terminal pair abort. The driver knows this syntactically.
#[derive(Debug, Clone, Copy)]
pub struct PairAborts {
    pub left: bool,
    pub right: bool,
}

/// Is the dependency `name` false on a pair with these aborts — decided **without the solver**?
/// `build_no_abort` is `left_no_abort ∧ right_no_abort` over the two return values' abort
/// constructors, so for the dependencies every default and generated claim uses the answer is
/// read off the terminals. `None`: not one of these, only the solver can tell.
fn false_by_terminals(name: &str, aborts: PairAborts) -> Option<bool> {
    match name {
        "no-abort" => Some(aborts.left || aborts.right),
        "left-no-abort" => Some(aborts.left),
        "right-no-abort" => Some(aborts.right),
        "equal-aborts" => Some(aborts.left != aborts.right),
        _ => None,
    }
}

/// Check `claim` on the pair whose path conditions are on the solver stack (and found
/// satisfiable by the pair's vacuity check). The stack is as it was on return.
///
/// 1. A dependency false on the terminals settles it: `Unreachable { DependencyFalse }`, no
///    solver call.
/// 2. Otherwise `push`, assert the claim's dependencies, `push`, assert the negated goal,
///    `check-sat`. `sat` fails the claim, `unknown` is inconclusive.
/// 3. `unsat` verifies the claim *unless the dependencies alone are unsatisfiable here*: a
///    dependency that is a project lemma or a user relation may be false on a pair whose
///    terminals do not say so. That is one more `check-sat`, asked only after an `unsat`
///    (a `sat` goal check already proves the dependencies satisfiable), and only for a claim
///    with such a dependency.
///
/// `model_id` names the model file of a failing check under `models/`; `queries` counts the
/// `check-sat` calls made.
pub(crate) fn check_claim<S: SmtSolver>(
    solver: &mut S,
    claim: &ClaimQuery,
    aborts: PairAborts,
    out_dir: &Path,
    layout: Layout,
    model_id: &str,
    queries: &mut usize,
) -> Result<(Verdict, Option<String>), DebugError> {
    for (name, _) in &claim.dependencies {
        if false_by_terminals(name, aborts) == Some(true) {
            return Ok((
                Verdict::Unreachable {
                    reason: Unreachability::DependencyFalse {
                        dependency: name.clone(),
                    },
                },
                None,
            ));
        }
    }

    let has_dependencies = !claim.dependencies.is_empty();
    if has_dependencies {
        solver.push()?;
        for (_, assertion) in &claim.dependencies {
            solver.write_smt(assertion.clone())?;
        }
    }
    solver.push()?;
    solver.write_smt(claim.negated.clone())?;
    *queries += 1;
    let answer = solver.check_sat()?;
    let outcome = match answer {
        SmtSolverResponse::Unsat => (Verdict::Verified, None),
        SmtSolverResponse::Sat => {
            let (rel, text) = write_model(solver, out_dir, layout, model_id)?;
            (Verdict::GoalFails { model: rel }, Some(text))
        }
        SmtSolverResponse::Unknown => match write_model(solver, out_dir, layout, model_id) {
            Ok((rel, text)) => (Verdict::Inconclusive { model: Some(rel) }, Some(text)),
            Err(_) => (Verdict::Inconclusive { model: None }, None),
        },
    };
    solver.pop()?;

    let verdict_and_model = outcome;
    if has_dependencies {
        let by_solver: Vec<&(String, SmtExpr)> = claim
            .dependencies
            .iter()
            .filter(|(name, _)| false_by_terminals(name, aborts).is_none())
            .collect();
        if matches!(verdict_and_model.0, Verdict::Verified)
            && !by_solver.is_empty()
            && {
                *queries += 1;
                matches!(solver.check_sat()?, SmtSolverResponse::Unsat)
            }
        {
            solver.pop()?;
            let dependency = dependency_false_here(solver, &by_solver, queries)?;
            return Ok((
                Verdict::Unreachable {
                    reason: Unreachability::DependencyFalse { dependency },
                },
                None,
            ));
        }
        solver.pop()?;
    }
    Ok(verdict_and_model)
}

/// Which dependency is false on the pair: the first of `dependencies` unsatisfiable on its own,
/// or all of them, joined, when only their conjunction is. On entry the solver holds the pair,
/// and nothing of the claim.
fn dependency_false_here<S: SmtSolver>(
    solver: &mut S,
    dependencies: &[&(String, SmtExpr)],
    queries: &mut usize,
) -> Result<String, DebugError> {
    for (name, assertion) in dependencies {
        solver.push()?;
        solver.write_smt(assertion.clone())?;
        *queries += 1;
        let unsat = matches!(solver.check_sat()?, SmtSolverResponse::Unsat);
        solver.pop()?;
        if unsat {
            return Ok(name.clone());
        }
    }
    Ok(dependencies
        .iter()
        .map(|(name, _)| name.as_str())
        .collect::<Vec<_>>()
        .join(", "))
}

/// Check every claim of `claims` on the pair, in order. `skip` says a claim is not checked on
/// this pair (`--first-failure-per-claim`, once the claim has failed). Each returned verdict
/// comes with the model text of a failing check.
pub(crate) fn check_claims<S: SmtSolver>(
    solver: &mut S,
    claims: &[ClaimQuery],
    aborts: PairAborts,
    out_dir: &Path,
    layout: Layout,
    pair_id: &str,
    queries: &mut usize,
    mut skip: impl FnMut(&str) -> bool,
) -> Result<Vec<(ClaimVerdict, Option<String>)>, DebugError> {
    let mut verdicts = Vec::with_capacity(claims.len());
    for claim in claims {
        if skip(&claim.name) {
            continue;
        }
        let model_id = format!("{pair_id}.{}", claim.name);
        let (verdict, model) = check_claim(solver, claim, aborts, out_dir, layout, &model_id, queries)?;
        verdicts.push((
            ClaimVerdict {
                claim: claim.name.clone(),
                verdict,
                relations: Vec::new(),
            },
            model,
        ));
    }
    Ok(verdicts)
}

/// The one verdict that stands for a pair the claims were checked on: a failure if any claim
/// failed (`goal-fails` before `inconclusive`), otherwise `verified` if any claim verified,
/// otherwise every claim was unreachable and the first one's reason stands. The model text is
/// the standing failure's.
pub(crate) fn aggregate(
    checked: &[(ClaimVerdict, Option<String>)],
) -> (Verdict, Option<String>) {
    let pick = |wanted: fn(&Verdict) -> bool| checked.iter().find(|(c, _)| wanted(&c.verdict));
    if let Some((c, model)) = pick(|v| matches!(v, Verdict::GoalFails { .. })) {
        return (c.verdict.clone(), model.clone());
    }
    if let Some((c, model)) = pick(|v| matches!(v, Verdict::Inconclusive { .. })) {
        return (c.verdict.clone(), model.clone());
    }
    if checked.iter().any(|(c, _)| matches!(c.verdict, Verdict::Verified)) {
        return (Verdict::Verified, None);
    }
    match checked.first() {
        Some((c, _)) => (c.verdict.clone(), None),
        // every claim admitted, or skipped: nothing was asked, so nothing can fail
        None => (Verdict::Verified, None),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn aborts(left: bool, right: bool) -> PairAborts {
        PairAborts { left, right }
    }

    #[test]
    fn the_four_dependencies_the_defaults_use_are_read_off_the_terminals() {
        assert_eq!(false_by_terminals("no-abort", aborts(false, false)), Some(false));
        assert_eq!(false_by_terminals("no-abort", aborts(true, false)), Some(true));
        assert_eq!(false_by_terminals("no-abort", aborts(false, true)), Some(true));
        assert_eq!(false_by_terminals("left-no-abort", aborts(true, false)), Some(true));
        assert_eq!(false_by_terminals("left-no-abort", aborts(false, true)), Some(false));
        assert_eq!(false_by_terminals("right-no-abort", aborts(true, false)), Some(false));
        assert_eq!(false_by_terminals("right-no-abort", aborts(false, true)), Some(true));
        assert_eq!(false_by_terminals("equal-aborts", aborts(true, true)), Some(false));
        assert_eq!(false_by_terminals("equal-aborts", aborts(true, false)), Some(true));
        assert_eq!(false_by_terminals("my-lemma", aborts(true, true)), None);
    }

    fn claim(name: &str, verdict: Verdict) -> (ClaimVerdict, Option<String>) {
        (
            ClaimVerdict {
                claim: name.to_string(),
                verdict,
                relations: Vec::new(),
            },
            None,
        )
    }

    fn dependency_false(name: &str) -> Verdict {
        Verdict::Unreachable {
            reason: Unreachability::DependencyFalse {
                dependency: name.to_string(),
            },
        }
    }

    #[test]
    fn a_failing_claim_stands_for_the_pair() {
        let checked = [
            claim("a", Verdict::Verified),
            claim("b", Verdict::Inconclusive { model: None }),
            claim("c", Verdict::GoalFails { model: "m".into() }),
        ];
        assert!(matches!(aggregate(&checked).0, Verdict::GoalFails { .. }));
    }

    #[test]
    fn a_verified_claim_outranks_an_unreachable_one() {
        let checked = [claim("a", dependency_false("no-abort")), claim("b", Verdict::Verified)];
        assert!(matches!(aggregate(&checked).0, Verdict::Verified));
    }

    #[test]
    fn a_pair_where_every_claim_is_unreachable_keeps_the_reason() {
        let checked = [claim("a", dependency_false("no-abort"))];
        assert!(matches!(
            aggregate(&checked).0,
            Verdict::Unreachable {
                reason: Unreachability::DependencyFalse { .. }
            }
        ));
    }
}
