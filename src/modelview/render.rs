// SPDX-License-Identifier: MIT OR Apache-2.0

//! Turns a [`Trace`] plus the parsed [`SmtModel`] into a human-readable text report.

use std::fmt;

use crate::modelview::ctors::{self, Category, CtorMap, EntryLabels, Side};
use crate::modelview::trace::Trace;
use crate::modelview::value::{self, Pretty};
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

    if trace.matched.is_some() {
        render_claim_description(&mut out, trace, model, &ctors, &labels);

        out.push_str("\n== Left/Right old game state ==\n");
        render_named(&mut out, model, &ctors, &format!("<<game-state-{}-old>>", side_name(trace, Side::Left)), "left");
        render_named(&mut out, model, &ctors, &format!("<<game-state-{}-old>>", side_name(trace, Side::Right)), "right");

        if let Some(oracle) = &trace.oracle_name {
            out.push_str("\n== New game state (after calling the oracle) ==\n");
            render_named(
                &mut out,
                model,
                &ctors,
                &format!("<<game-state-{}-new-{oracle}>>", side_name(trace, Side::Left)),
                "left",
            );
            render_named(
                &mut out,
                model,
                &ctors,
                &format!("<<game-state-{}-new-{oracle}>>", side_name(trace, Side::Right)),
                "right",
            );
        }
    }

    render_bucket(&mut out, model, &labels, &ctors, "== Oracle arguments ==", |cat| {
        matches!(cat, Category::OracleArg { .. })
    });
    render_bucket(&mut out, model, &labels, &ctors, "== Return values ==", |cat| {
        matches!(cat, Category::RawReturn(..) | Category::ReturnValue(..))
    });
    render_bucket(&mut out, model, &labels, &ctors, "== Abort flags ==", |cat| {
        matches!(cat, Category::IsAbort(..))
    });
    render_bucket(&mut out, model, &labels, &ctors, "== Theorem constants ==", |cat| {
        matches!(cat, Category::TheoremConsts)
    });
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
    out.push_str(&format!(
        "oracle:    {}\n",
        trace.oracle_name.as_deref().unwrap_or("<unknown>")
    ));
    out.push_str(&format!(
        "claim:     {}\n",
        trace.claim_name.as_deref().unwrap_or("<unknown>")
    ));
}

/// Looks up the single model entry whose label matches `category`, if any.
fn find_by_category(
    model: &SmtModel,
    labels: &EntryLabels,
    ctors: &CtorMap,
    category: &Category,
) -> Option<Pretty> {
    let (name, _) = labels.iter().find(|(_, label)| &label.category == category)?;
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
                left.map(|v| v.to_string()).unwrap_or_else(|| "<not present in model>".to_string())
            ));
            out.push_str(&format!(
                "  right ({}): {}\n",
                side_name(trace, Side::Right),
                right.map(|v| v.to_string()).unwrap_or_else(|| "<not present in model>".to_string())
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
                left.map(|v| v.to_string()).unwrap_or_else(|| "<not present in model>".to_string())
            ));
            out.push_str(&format!(
                "  right ({}) aborted: {}\n",
                side_name(trace, Side::Right),
                right.map(|v| v.to_string()).unwrap_or_else(|| "<not present in model>".to_string())
            ));
        }
        "no-abort" => {
            out.push_str(&format!("\n`{oracle}` was expected not to abort, but it did.\n"));
        }
        _ => {}
    }
}

fn render_named(out: &mut String, model: &SmtModel, ctors: &CtorMap, name: &str, side: &str) {
    match model.get_value(name) {
        Some(entry) => {
            let value = value::interpret(&entry.value_expr(), ctors);
            out.push_str(&format!("{side} ({name}):\n  {value}\n"));
        }
        None => out.push_str(&format!("{side} ({name}): <not present in model>\n")),
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
