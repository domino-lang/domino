// SPDX-License-Identifier: MIT OR Apache-2.0

//! Reading goals as EasyCrypt's JSON shows them (story 27 §3.2.4): subgoals are told apart by
//! their **kind** (an ambient formula, an `equivS`, an `hoareS` under a quantifier) and by the
//! head of their programs, never by position in EasyCrypt's list or in our listing.

use crate::easycrypt::json::{Form, Goal, Instr, Side};

/// A relational program goal: `equiv[ S1 ~ S2 : pre ==> post ]`.
pub(super) fn is_program(goal: &Goal) -> bool {
    goal.concl.kind == "equivS"
}

/// Whether the goal is a formula of the ambient logic, possibly with a program judgement under
/// its quantifier (what `rcondt` leaves as its side goal): anything that is not itself a
/// program judgement.
pub(super) fn is_ambient(goal: &Goal) -> bool {
    !matches!(
        goal.concl.kind.as_str(),
        "equivS"
            | "equivF"
            | "hoareS"
            | "hoareF"
            | "phoareS"
            | "phoareF"
            | "ehoareS"
            | "ehoareF"
            | "eagerF"
    )
}

pub(super) fn sides(goal: &Goal) -> Option<(&Side, &Side)> {
    if !is_program(goal) {
        return None;
    }
    Some((goal.concl.left.as_ref()?, goal.concl.right.as_ref()?))
}

/// Both programs are empty (`<skip> ~ <skip>`).
pub(super) fn is_skip_pair(goal: &Goal) -> bool {
    sides(goal).is_some_and(|(l, r)| l.stmt.is_empty() && r.stmt.is_empty())
}

/// The number of assignments at the start of a statement list: what `sp k l` consumes.
pub(super) fn leading_assignments(stmts: &[Instr]) -> usize {
    stmts.iter().take_while(|s| s.kind == "asgn").count()
}

/// The `(k, l)` of `sp k l` for a program goal.
pub(super) fn sp_counts(goal: &Goal) -> Option<(usize, usize)> {
    let (l, r) = sides(goal)?;
    Some((leading_assignments(&l.stmt), leading_assignments(&r.stmt)))
}

/// The first instruction that is not an assignment, and how many assignments precede it.
pub(super) fn head_after_assignments(stmts: &[Instr]) -> (usize, Option<&Instr>) {
    let k = leading_assignments(stmts);
    (k, stmts.get(k))
}

pub(super) fn op_name(form: &Form) -> Option<&str> {
    form.op.as_deref()
}

fn op_is(form: &Form, last: &str) -> bool {
    form.kind == "app"
        && op_name(form).is_some_and(|op| op.rsplit_once('.').is_some_and(|(_, n)| n == last))
}

/// `A => B`.
pub(super) fn as_implication(form: &Form) -> Option<(&Form, &Form)> {
    if op_is(form, "=>") && form.args.len() == 2 {
        Some((&form.args[0], &form.args[1]))
    } else {
        None
    }
}

/// `A /\ B`.
pub(super) fn as_conjunction(form: &Form) -> Option<(&Form, &Form)> {
    if op_is(form, "/\\") && form.args.len() == 2 {
        Some((&form.args[0], &form.args[1]))
    } else {
        None
    }
}

/// `forall b1 … bk, body`: the names of the binders as a tactic can spell them, and the body.
pub(super) fn as_forall(form: &Form) -> Option<(Vec<&str>, &Form)> {
    if form.kind == "quant" && form.quantifier.as_deref() == Some("forall") {
        let names = form
            .binders
            .iter()
            .filter(|b| b.kind != "type")
            .map(|b| b.name.as_str())
            .collect();
        return Some((names, form.body.as_deref()?));
    }
    None
}

/// A quantifier over a program judgement: `forall &m0, hoare[…]`.
pub(super) fn wraps_program(form: &Form) -> bool {
    match form.kind.as_str() {
        "quant" => form.body.as_deref().is_some_and(|b| {
            matches!(
                b.kind.as_str(),
                "equivS" | "hoareS" | "phoareS" | "ehoareS" | "equivF" | "hoareF"
            ) || wraps_program(b)
        }),
        _ => false,
    }
}

/// The last path component of an application's operator: `Domino_rel` for
/// `Top.Eq_A_B_Invariants.Domino_rel`.
pub(super) fn app_op_leaf(form: &Form) -> Option<&str> {
    if form.kind != "app" {
        return None;
    }
    op_name(form).map(|op| op.rsplit_once('.').map_or(op, |(_, n)| n))
}

/// Whether any node of the formula tree is an application of an operator named `name`.
pub(super) fn mentions_op(form: &Form, name: &str) -> bool {
    if op_is(form, name) {
        return true;
    }
    let children = form
        .head
        .iter()
        .map(|b| &**b)
        .chain(form.args.iter())
        .chain(form.body.iter().map(|b| &**b))
        .chain(form.pre.iter().map(|b| &**b))
        .chain(form.post.iter().map(|b| &**b));
    children.into_iter().any(|c| mentions_op(c, name))
}

/// A hypothesis name that no hypothesis of the goal has.
pub(super) fn fresh_name(goal: &Goal, base: &str) -> String {
    let taken = |n: &str| goal.hyps.iter().any(|h| h.name == n);
    if !taken(base) {
        return base.to_string();
    }
    (1..)
        .map(|i| format!("{base}{i}"))
        .find(|n| !taken(n))
        .expect("an unused name exists")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::easycrypt::json::parse_response;

    const FIXTURE: &str = include_str!(
        "../../../testdata/easycrypt/story25/hello_world_useful_oracle_after_inline.json"
    );

    #[test]
    fn the_recorded_goal_is_a_program_goal_and_its_prefix_is_counted() {
        let response = parse_response(FIXTURE).unwrap();
        let goal = &response.proof.as_ref().unwrap().goals[0];
        assert!(is_program(goal));
        assert!(!is_ambient(goal));
        assert!(!is_skip_pair(goal));
        // `ec_result <- None; if (…) {…}`: one assignment on each side, then the router guard
        assert_eq!(sp_counts(goal), Some((1, 1)));
        let (l, _) = sides(goal).unwrap();
        let (k, head) = head_after_assignments(&l.stmt);
        assert_eq!(k, 1);
        assert_eq!(head.unwrap().kind, "if");
    }

    #[test]
    fn implications_conjunctions_and_operators_are_read_from_the_formula_tree() {
        let response = parse_response(FIXTURE).unwrap();
        let goal = &response.proof.as_ref().unwrap().goals[0];
        let pre = goal.concl.pre.as_ref().unwrap();
        // the precondition is `true /\ inv …` (or a conjunction with it)
        assert!(mentions_op(pre, "inv"), "{}", pre.pp);
        let post = goal.concl.post.as_ref().unwrap();
        let (a, b) = as_conjunction(post).expect("equal-output /\\ inv");
        assert!(!mentions_op(a, "inv"));
        assert_eq!(app_op_leaf(b), Some("inv"));
    }
}
