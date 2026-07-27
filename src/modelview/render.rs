// SPDX-License-Identifier: MIT OR Apache-2.0

//! Turns a [`Trace`] plus the parsed [`SmtModel`] into a human-readable text report.

use std::fmt;

use crate::modelview::ctors::{self, Category, CtorMap, EntryLabels, Side};
use crate::modelview::trace::Trace;
use crate::modelview::value::{self, Pretty};
use crate::theorem::INITIAL_STATE_CLAIM_NAME;
use crate::util::smtmodel::SmtModel;

pub struct Report {
    text: String,
}

impl fmt::Display for Report {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.text)
    }
}

pub fn render(trace: &Trace, model: &SmtModel) -> Report {
    let mut out = String::new();

    render_header(&mut out, trace);

    let (ctors, labels) = match &trace.matched {
        Some(matched) => ctors::build_maps(matched.theorem, &matched.left, &matched.right),
        None => (ctors::builtin_ctors(), EntryLabels::new()),
    };

    // The initial-state claim isn't scoped to an oracle call: the `old`/`new` game states and
    // oracle args/returns/aborts sections below are meaningless noise for it (those consts are
    // declared in every transcript regardless of claim, but are only *constrained* -- and thus
    // only meaningful to inspect -- when actually proving that claim). Show the initial states
    // instead.
    let is_initial_state_claim = trace.claim_name.as_deref() == Some(INITIAL_STATE_CLAIM_NAME);

    if trace.matched.is_some() && is_initial_state_claim {
        render_initial_state_claim_description(&mut out);

        out.push_str("\n== Left/Right initial game state ==\n");
        render_state_columns(
            &mut out,
            model,
            &ctors,
            &format!("<<game-state-{}-initial>>", side_name(trace, Side::Left)),
            &format!("<<game-state-{}-initial>>", side_name(trace, Side::Right)),
            &format!("left ({})", side_name(trace, Side::Left)),
            &format!("right ({})", side_name(trace, Side::Right)),
        );
    } else if trace.matched.is_some() {
        render_claim_description(&mut out, trace, model, &ctors, &labels);

        out.push_str("\n== Left/Right old game state ==\n");
        render_state_columns(
            &mut out,
            model,
            &ctors,
            &format!("<<game-state-{}-old>>", side_name(trace, Side::Left)),
            &format!("<<game-state-{}-old>>", side_name(trace, Side::Right)),
            &format!("left ({})", side_name(trace, Side::Left)),
            &format!("right ({})", side_name(trace, Side::Right)),
        );

        if let Some(oracle) = &trace.oracle_name {
            out.push_str(&format!(
                "\n== Left/Right new game state (after calling `{oracle}`) ==\n"
            ));
            render_state_columns(
                &mut out,
                model,
                &ctors,
                &format!(
                    "<<game-state-{}-new-{oracle}>>",
                    side_name(trace, Side::Left)
                ),
                &format!(
                    "<<game-state-{}-new-{oracle}>>",
                    side_name(trace, Side::Right)
                ),
                &format!("left ({})", side_name(trace, Side::Left)),
                &format!("right ({})", side_name(trace, Side::Right)),
            );
        }
    }

    if !is_initial_state_claim {
        // When the relevant oracle is known, hide other oracles' arguments/returns/aborts, since
        // they're irrelevant noise for the claim actually being investigated.
        let oracle_filter = trace.oracle_name.as_deref();
        let oracle_matches = |name: &str| oracle_filter.map_or(true, |o| o == name);

        render_bucket(
            &mut out,
            model,
            &labels,
            &ctors,
            "== Oracle arguments ==",
            |cat| matches!(cat, Category::OracleArg { oracle, .. } if oracle_matches(oracle)),
        );
        // `RawReturn` bundles the oracle's return value together with the *entire* resulting
        // game state, which is already shown in full in the "new game state" section above; only
        // the return value itself is useful here.
        render_bucket(
            &mut out,
            model,
            &labels,
            &ctors,
            "== Return values ==",
            |cat| matches!(cat, Category::ReturnValue(_, oracle) if oracle_matches(oracle)),
        );
        render_bucket(
            &mut out,
            model,
            &labels,
            &ctors,
            "== Abort flags ==",
            |cat| matches!(cat, Category::IsAbort(_, oracle) if oracle_matches(oracle)),
        );
    }

    render_bucket(
        &mut out,
        model,
        &labels,
        &ctors,
        "== Theorem constants ==",
        |cat| matches!(cat, Category::TheoremConsts),
    );
    render_function_bucket(&mut out, model, &labels, &ctors);
    render_bucket(
        &mut out,
        model,
        &labels,
        &ctors,
        "== Sampled randomness ==",
        |cat| matches!(cat, Category::RandVal(..) | Category::RandCtr(..)),
    );

    render_other(&mut out, model, &labels);

    if !trace.warnings.is_empty() {
        out.push_str("\n== Warnings ==\n");
        for warning in &trace.warnings {
            out.push_str(&format!("- {warning}\n"));
        }
    }

    Report { text: out }
}

fn side_name<'t>(trace: &'t Trace, side: Side) -> &'t str {
    let name = match side {
        Side::Left => trace.left_name.as_deref(),
        Side::Right => trace.right_name.as_deref(),
    };
    name.unwrap_or("")
}

fn render_header(out: &mut String, trace: &Trace) {
    out.push_str("== Model ==\n");
    out.push_str(&format!(
        "theorem:   {}\n",
        trace.theorem_name.as_deref().unwrap_or("<unknown>")
    ));
    match (&trace.left_name, &trace.right_name) {
        (Some(l), Some(r)) => out.push_str(&format!("proofstep: {l} == {r}\n")),
        _ => out.push_str("proofstep: <unknown>\n"),
    }
    let oracle_display = if trace.claim_name.as_deref() == Some(INITIAL_STATE_CLAIM_NAME) {
        "n/a (equivalence-wide claim)"
    } else {
        trace.oracle_name.as_deref().unwrap_or("<unknown>")
    };
    out.push_str(&format!("oracle:    {oracle_display}\n"));
    out.push_str(&format!(
        "claim:     {}\n",
        trace.claim_name.as_deref().unwrap_or("<unknown>")
    ));
}

/// Explains the initial-state claim: the equivalence's induction *base case*, checking that the
/// invariant actually holds on the two games' basic initial states (every package state field at
/// its type's default value) rather than just being preserved once established.
fn render_initial_state_claim_description(out: &mut String) {
    out.push_str(
        "\nThe invariant was expected to hold on the initial state of both games, but didn't.\n\
         This is the base case of the equivalence's invariant induction (`domino prove` proving \
         each oracle preserves it only shows it's inductive, not that it actually holds at the \
         start). See the initial game states below.\n",
    );
}

/// Looks up the single model entry whose label matches `category`, if any.
fn find_by_category(
    model: &SmtModel,
    labels: &EntryLabels,
    ctors: &CtorMap,
    category: &Category,
) -> Option<Pretty> {
    let (name, _) = labels
        .iter()
        .find(|(_, label)| &label.category == category)?;
    let entry = model.get_value(name)?;
    Some(value::interpret(&entry.value_expr(), ctors))
}

fn render_claim_description(
    out: &mut String,
    trace: &Trace,
    model: &SmtModel,
    ctors: &CtorMap,
    labels: &EntryLabels,
) {
    let (Some(claim), Some(oracle)) = (trace.claim_name.as_deref(), trace.oracle_name.as_deref())
    else {
        return;
    };

    match claim {
        "same-output" => {
            let left = find_by_category(
                model,
                labels,
                ctors,
                &Category::ReturnValue(Side::Left, oracle.to_string()),
            );
            let right = find_by_category(
                model,
                labels,
                ctors,
                &Category::ReturnValue(Side::Right, oracle.to_string()),
            );
            out.push_str(&format!(
                "\n`{oracle}` was expected to return the same value on both sides, but didn't:\n"
            ));
            out.push_str(&format!(
                "  left  ({}): {}\n",
                side_name(trace, Side::Left),
                left.map(|v| v.to_string())
                    .unwrap_or_else(|| "<not present in model>".to_string())
            ));
            out.push_str(&format!(
                "  right ({}): {}\n",
                side_name(trace, Side::Right),
                right
                    .map(|v| v.to_string())
                    .unwrap_or_else(|| "<not present in model>".to_string())
            ));
        }
        "equal-aborts" => {
            let left = find_by_category(
                model,
                labels,
                ctors,
                &Category::IsAbort(Side::Left, oracle.to_string()),
            );
            let right = find_by_category(
                model,
                labels,
                ctors,
                &Category::IsAbort(Side::Right, oracle.to_string()),
            );
            out.push_str(&format!(
                "\n`{oracle}` was expected to either abort on both sides or neither, but only one did:\n"
            ));
            out.push_str(&format!(
                "  left  ({}) aborted: {}\n",
                side_name(trace, Side::Left),
                left.map(|v| v.to_string())
                    .unwrap_or_else(|| "<not present in model>".to_string())
            ));
            out.push_str(&format!(
                "  right ({}) aborted: {}\n",
                side_name(trace, Side::Right),
                right
                    .map(|v| v.to_string())
                    .unwrap_or_else(|| "<not present in model>".to_string())
            ));
        }
        "no-abort" => {
            out.push_str(&format!(
                "\n`{oracle}` was expected not to abort, but it did.\n"
            ));
        }
        _ => {}
    }
}

/// Renders a package-grouped, indented dump of a game-state entry (`name`) for both sides,
/// side by side in two columns. Fields are paired up between the two sides (see
/// [`Pretty::render_pair_lines`]) so that a diverging field (e.g. a `Map` override present on
/// only one side) doesn't throw off the alignment of everything that follows it.
fn render_state_columns(
    out: &mut String,
    model: &SmtModel,
    ctors: &CtorMap,
    left_name: &str,
    right_name: &str,
    left_header: &str,
    right_header: &str,
) {
    let left_value = state_value(model, ctors, left_name);
    let right_value = state_value(model, ctors, right_name);
    let pairs = Pretty::render_pair_lines(&left_value, &right_value, 0);
    let (left_lines, right_lines): (Vec<String>, Vec<String>) = pairs.into_iter().unzip();
    out.push_str(&side_by_side(
        &left_lines,
        &right_lines,
        left_header,
        right_header,
    ));
}

fn state_value(model: &SmtModel, ctors: &CtorMap, name: &str) -> Pretty {
    match model.get_value(name) {
        Some(entry) => value::interpret(&entry.value_expr(), ctors),
        None => Pretty::Unknown("<not present in model>".to_string()),
    }
}

/// Lays out two blocks of pre-rendered lines side by side in two padded columns. Column width is
/// capped at [`value::MAX_INLINE_WIDTH`] so one unusually long, un-splittable row doesn't blow up
/// the padding for every other, much shorter row; long lines just spill into the right column on
/// their own row instead of forcing the whole table wide.
fn side_by_side(
    left: &[String],
    right: &[String],
    left_header: &str,
    right_header: &str,
) -> String {
    let width = left
        .iter()
        .map(|line| line.chars().count())
        .chain(std::iter::once(left_header.chars().count()))
        .max()
        .unwrap_or(0)
        .min(value::MAX_INLINE_WIDTH);

    let mut out = String::new();
    out.push_str(&format!("{left_header:<width$}   {right_header}\n"));
    out.push_str(&format!(
        "{:-<width$}   {:-<rwidth$}\n",
        "",
        "",
        rwidth = right_header.chars().count().max(1)
    ));

    for i in 0..left.len().max(right.len()) {
        let l = left.get(i).map(String::as_str).unwrap_or("");
        let r = right.get(i).map(String::as_str).unwrap_or("");
        out.push_str(&format!("{l:<width$}   {r}\n"));
    }

    out
}

fn render_function_bucket(
    out: &mut String,
    model: &SmtModel,
    labels: &EntryLabels,
    ctors: &CtorMap,
) {
    let mut funcs: Vec<(String, Pretty)> = model
        .entries()
        .filter_map(|entry| {
            let label = labels.get(entry.name())?;
            matches!(label.category, Category::TheoremFunc(_)).then(|| {
                (
                    label.display.clone(),
                    value::interpret_function(entry, ctors),
                )
            })
        })
        .collect();

    if funcs.is_empty() {
        return;
    }

    funcs.sort_by(|a, b| a.0.cmp(&b.0));

    out.push_str("\n== Theorem functions ==\n");
    for (name, pretty) in funcs {
        if pretty.is_compound() {
            out.push_str(&format!("{name}:\n"));
            for line in pretty.render_lines(1) {
                out.push_str(&line);
                out.push('\n');
            }
        } else {
            out.push_str(&format!("{name}: {pretty}\n"));
        }
    }
}

fn render_bucket(
    out: &mut String,
    model: &SmtModel,
    labels: &EntryLabels,
    ctors: &CtorMap,
    heading: &str,
    matches_category: impl Fn(&Category) -> bool,
) {
    let mut lines = Vec::new();
    for entry in model.entries() {
        if let Some(label) = labels.get(entry.name()) {
            if matches_category(&label.category) {
                let value = value::interpret(&entry.value_expr(), ctors);
                lines.push(format!("{}: {value}", label.display));
            }
        }
    }

    if lines.is_empty() {
        return;
    }

    out.push('\n');
    out.push_str(heading);
    out.push('\n');
    lines.sort();
    for line in lines {
        out.push_str(&line);
        out.push('\n');
    }
}

fn render_other(out: &mut String, model: &SmtModel, labels: &EntryLabels) {
    let mut lines = Vec::new();
    for entry in model.entries() {
        if labels.contains_key(entry.name()) {
            continue;
        }
        if entry.name() == "<<theorem-consts>>" {
            continue;
        }
        if entry.name().starts_with("<<game-state-") {
            continue;
        }
        if !entry.args().is_empty() {
            // uninterpreted-function-style entries (e.g. `__sample-rand-*`, `<<func-*>>`) are
            // functions rather than plain values; skip them from this leftover dump.
            continue;
        }
        lines.push(entry.name().to_string());
    }

    if lines.is_empty() {
        return;
    }

    out.push_str("\n== Other model values ==\n");
    lines.sort();
    for name in lines {
        out.push_str(&format!("{name}\n"));
    }
}
