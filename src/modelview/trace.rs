// SPDX-License-Identifier: MIT OR Apache-2.0

//! Identifies which theorem / proof step / oracle / claim a model belongs to.

use crate::modelview::ctors::{Side, SideInfo};
use crate::project::Project;
use crate::theorem::Theorem;
use crate::util::smtmodel::SmtModel;

pub struct MatchedStep<'p> {
    pub theorem: &'p Theorem<'p>,
    pub left: SideInfo<'p>,
    pub right: SideInfo<'p>,
}

pub struct Trace<'p> {
    pub matched: Option<MatchedStep<'p>>,
    pub theorem_name: Option<String>,
    pub left_name: Option<String>,
    pub right_name: Option<String>,
    pub oracle_name: Option<String>,
    pub claim_name: Option<String>,
    pub warnings: Vec<String>,
}

impl Default for Trace<'_> {
    fn default() -> Self {
        Self {
            matched: None,
            theorem_name: None,
            left_name: None,
            right_name: None,
            oracle_name: None,
            claim_name: None,
            warnings: Vec::new(),
        }
    }
}

type Metadata = (
    Option<String>,
    Option<String>,
    Option<String>,
    Option<String>,
    Option<String>,
);

fn metadata(model: &SmtModel) -> Metadata {
    (
        model.get_value_as_string("<domino-model-info-theorem>"),
        model.get_value_as_string("<domino-model-info-game-inst-left>"),
        model.get_value_as_string("<domino-model-info-game-inst-right>"),
        model.get_value_as_string("<domino-model-info-oracle>"),
        model.get_value_as_string("<domino-model-info-claim>"),
    )
}

/// Collects candidate game instance names by looking for `<<game-state-X-old>>`-shaped free
/// constants in the model.
fn candidate_instance_names(model: &SmtModel) -> Vec<String> {
    model
        .entries()
        .filter_map(|entry| {
            entry
                .name()
                .strip_prefix("<<game-state-")?
                .strip_suffix("-old>>")
                .map(str::to_string)
        })
        .collect()
}

pub fn identify<'p, P: Project>(project: Option<&'p P>, model: &SmtModel) -> Trace<'p> {
    let mut trace = Trace::default();

    let (theorem_name, left_name, right_name, oracle_name, claim_name) = metadata(model);
    trace.oracle_name = oracle_name;
    trace.claim_name = claim_name;

    let Some(project) = project else {
        trace.theorem_name = theorem_name;
        trace.left_name = left_name;
        trace.right_name = right_name;
        if trace.theorem_name.is_some() {
            trace.warnings.push(
                "no Domino project loaded: showing raw values without resolving field names"
                    .to_string(),
            );
        }
        return trace;
    };

    if let (Some(theorem_name), Some(left_name), Some(right_name)) = (
        theorem_name.clone(),
        left_name.clone(),
        right_name.clone(),
    ) {
        trace.theorem_name = Some(theorem_name.clone());
        trace.left_name = Some(left_name.clone());
        trace.right_name = Some(right_name.clone());

        let oracle_name = trace.oracle_name.clone();

        match resolve(project, &theorem_name, &left_name, &right_name) {
            Ok(matched) => {
                check_proofstep_exists(&mut trace, matched.theorem, &left_name, &right_name);
                check_oracle_exists(&mut trace, &matched, oracle_name.as_deref());
                trace.matched = Some(matched);
            }
            Err(warning) => trace.warnings.push(warning),
        }

        return trace;
    }

    // Fallback: no (or incomplete) breadcrumb metadata. Scan the model for game-instance-name
    // shaped constants and match them against every theorem's proof steps.
    let candidates = candidate_instance_names(model);
    if candidates.is_empty() {
        trace.warnings.push(
            "could not identify the theorem/proof step: no `<domino-model-info-*>` breadcrumbs \
             and no recognizable game-state constants were found in this model"
                .to_string(),
        );
        return trace;
    }

    let mut found = None;
    for theorem_key in project.theorems() {
        let Some(theorem) = project.get_theorem(theorem_key) else {
            continue;
        };
        for hop in &theorem.game_hops {
            let left = hop.left_game_instance_name();
            let right = hop.right_game_instance_name();
            if candidates.iter().any(|c| c == left) && candidates.iter().any(|c| c == right) {
                found = Some((theorem_key.to_string(), left.to_string(), right.to_string()));
                break;
            }
        }
        if found.is_some() {
            break;
        }
    }

    match found {
        Some((theorem_name, left_name, right_name)) => {
            match resolve(project, &theorem_name, &left_name, &right_name) {
                Ok(matched) => {
                    trace.theorem_name = Some(theorem_name);
                    trace.left_name = Some(left_name);
                    trace.right_name = Some(right_name);
                    trace.matched = Some(matched);
                    trace.warnings.push(
                        "no `<domino-model-info-*>` breadcrumbs in this model (it predates that \
                         feature, or was hand-written); theorem and proof step were inferred from \
                         game-instance names. The specific oracle/claim could not be determined, \
                         so return values/arguments for all oracles are shown."
                            .to_string(),
                    );
                }
                Err(warning) => trace.warnings.push(warning),
            }
        }
        None => {
            trace.warnings.push(format!(
                "found game-instance-like names {candidates:?} in the model, but no proof step \
                 in this project has both as its left/right game instances"
            ));
        }
    }

    trace
}

fn resolve<'p, P: Project>(
    project: &'p P,
    theorem_name: &str,
    left_name: &str,
    right_name: &str,
) -> Result<MatchedStep<'p>, String> {
    let theorem = project
        .get_theorem(theorem_name)
        .ok_or_else(|| format!("theorem \"{theorem_name}\" was not found in this project"))?;

    let left_inst = theorem.find_game_instance(left_name).ok_or_else(|| {
        format!(
            "game instance \"{left_name}\" was not found in theorem \"{theorem_name}\" \
             (the project may have changed since this model was generated)"
        )
    })?;
    let right_inst = theorem.find_game_instance(right_name).ok_or_else(|| {
        format!(
            "game instance \"{right_name}\" was not found in theorem \"{theorem_name}\" \
             (the project may have changed since this model was generated)"
        )
    })?;

    Ok(MatchedStep {
        theorem,
        left: SideInfo::new(Side::Left, left_inst),
        right: SideInfo::new(Side::Right, right_inst),
    })
}

fn check_proofstep_exists(trace: &mut Trace, theorem: &Theorem, left: &str, right: &str) {
    let exists = theorem.game_hops.iter().any(|hop| {
        hop.left_game_instance_name() == left && hop.right_game_instance_name() == right
    });

    if !exists {
        trace.warnings.push(format!(
            "game instances \"{left}\" and \"{right}\" both exist in theorem \"{}\", but there is \
             no proof step directly comparing them (the project may have changed since this model \
             was generated)",
            theorem.name
        ));
    }
}

fn check_oracle_exists(trace: &mut Trace, matched: &MatchedStep, oracle_name: Option<&str>) {
    let Some(oracle_name) = oracle_name else {
        return;
    };

    let exported = matched
        .left
        .game_inst
        .game()
        .exports
        .iter()
        .any(|export| export.name() == oracle_name);

    if !exported {
        trace.warnings.push(format!(
            "oracle \"{oracle_name}\" is not exported by game instance \"{}\" (the project may \
             have changed since this model was generated)",
            matched.left.inst_name()
        ));
    }
}
