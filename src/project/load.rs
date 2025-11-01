// SPDX-License-Identifier: MIT OR Apache-2.0

use std::collections::HashMap;

use super::*;
use error::Result;

use crate::package::{Composition, Package};
use crate::parser::{composition::handle_composition, theorem::handle_theorem, SspParser};
use crate::theorem::Theorem;

pub(crate) fn games(
    files: &[(String, String)],
    pkgs: &HashMap<String, Package>,
) -> Result<HashMap<String, Composition>> {
    let mut games = HashMap::new();

    for (file_name, file_content) in files {
        let mut ast =
            SspParser::parse_composition(file_content).map_err(|err| (file_name.as_str(), err))?;

        let comp = handle_composition(file_name, file_content, ast.next().unwrap(), pkgs)?;
        let comp_name = comp.name.clone();

        games.insert(comp_name, comp);
    }

    Ok(games)
}

pub(crate) fn theorems(
    files: &[(String, String)],
    pkgs: HashMap<String, Package>,
    games: HashMap<String, Composition>,
) -> Result<HashMap<String, Theorem<'_>>> {
    let mut theorems = HashMap::new();

    for (file_name, file_content) in files {
        let parse_result =
            SspParser::parse_theorem(file_content).map_err(|err| (file_name.as_str(), err))?;

        let mut ast = parse_result;
        let theorem = handle_theorem(
            file_name,
            file_content,
            ast.next().unwrap(),
            pkgs.clone(),
            games.clone(),
        )?;
        let theorem_name = theorem.name.to_string();

        theorems.insert(theorem_name, theorem);
    }

    Ok(theorems)
}

/*
pub(crate) fn validate_assumptions(
    assumptions: &HashMap<String, Assumption>,
    games: &HashMap<String, Composition>,
) -> Result<()> {
    for (name, Assumption { left, right }) in assumptions.iter() {
        if !games.contains_key(left) {
            return Err(Error::UndefinedGame(
                left.clone(),
                format!("left in assumption {name}"),
            ));
        }

        if !games.contains_key(right) {
            return Err(Error::UndefinedGame(
                right.clone(),
                format!("right in assumption {name}"),
            ));
        }
    }

    return Ok(());
}

fn validate_game_hops(
    hops: &[GameHop],
    games: &HashMap<String, Composition>,
    assumptions: &HashMap<String, Assumption>,
) -> Result<()> {
    for (i, hop) in hops.iter().enumerate() {
        match hop {
            GameHop::Reduction(Reduction {
                left,
                right,
                assumption,
                ..
            }) => {
                if !games.contains_key(left) {
                    return Err(Error::UndefinedGame(
                        left.clone(),
                        format!("left in game hop {i} ({hop:?})"),
                    ));
                }
                if !games.contains_key(right) {
                    return Err(Error::UndefinedGame(
                        right.clone(),
                        format!("right in game hop {i} ({hop:?})"),
                    ));
                }
                if !assumptions.contains_key(assumption) {
                    return Err(Error::UndefinedAssumption(
                        assumption.clone(),
                        format!("in game hop {i} ({hop:?})"),
                    ));
                }
            }
            GameHop::Equivalence(eq) => {
                let Equivalence {
                    left,
                    right,
                    invariant_path: _,
                    trees,
                } = &eq;
                if !games.contains_key(left) {
                    return Err(Error::UndefinedGame(
                        left.clone(),
                        format!("left in game hop {i} ({hop:?})"),
                    ));
                }

                if !games.contains_key(right) {
                    return Err(Error::UndefinedGame(
                        right.clone(),
                        format!("right in game hop {i} ({hop:?})"),
                    ));
                };

                let left_game = &games[left];
                let right_game = &games[right];

                let left_sigs: HashSet<_> = HashSet::from_iter(&left_game.exports);
                let right_sigs: HashSet<_> = HashSet::from_iter(&right_game.exports);

                let left_not_right = left_sigs.difference(&right_sigs).collect_vec();
                let right_not_left = right_sigs.difference(&left_sigs).collect_vec();

                if left_sigs != right_sigs {
                    let err_msg =  match (left_not_right.is_empty(), right_not_left.is_empty()) {
                        (false, false) => format!("right game {right} exports oracles {right_not_left:?} that are not exported by left game {left} and left game exports oracles {left_not_right:?} that are not exported by right game"),
                        (false, true) => format!("left game {left} exports oracles {left_not_right:?} that are not exported by right game {right}"),
                        (true, false) => format!("right game {right} exports oracles {right_not_left:?} that are not exported by left game {left}"),
                        (true, true) => unreachable!(),
                    };

                    return Err(Error::TheoremTreeValidationError(err_msg));
                }

                let sig_names: HashSet<_> =
                    left_sigs.iter().map(|Export(_, sig)| &sig.name).collect();
                let tree_keys: HashSet<_> = HashSet::from_iter(trees.keys());

                if !tree_keys.is_subset(&sig_names) {
                    let diff = tree_keys
                        .difference(&sig_names)
                        .map(|x| *x)
                        .cloned()
                        .collect_vec();
                    return Err(Error::TheoremTreeValidationError(format!(
                        "theorem trees {diff:?} refer to unexported oracles"
                    )));
                }
            }
        }
    }

    Ok(())
}
 */
