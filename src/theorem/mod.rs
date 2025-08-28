use crate::parser::ast::Identifier;
use std::collections::{HashMap, HashSet, VecDeque};
use std::iter::zip;

use crate::{
    expressions::Expression,
    gamehops::GameHop,
    proof::{GameInstance, Proof},
};

#[derive(Debug, Clone)]
pub struct Theorem<'a> {
    proof: &'a Proof<'a>,
    // Specialized Instance -> reference to more general instance in the proof
    specialization: Vec<(GameInstance, &'a GameInstance)>,
    sequence: Vec<usize>,
}

impl<'a> Theorem<'a> {
    pub(crate) fn try_new(proof: &'a Proof) -> Option<Theorem<'a>> {
        let real = proof
            .instances
            .iter()
            .position(|inst| inst.name == "Real")?;
        let ideal = proof
            .instances
            .iter()
            .position(|inst| inst.name == "Ideal")?;

        let mut specialization: Vec<_> = proof
            .instances
            .iter()
            .map(|inst| (inst.clone(), inst))
            .collect();
        let mut workque = VecDeque::new();
        workque.push_back(real);
        let mut predecessors = HashMap::new();

        while !workque.is_empty() {
            let current_idx = workque.pop_front().unwrap();
            log::debug!(
                "next up: {current_idx} : {}",
                &specialization[current_idx].0.name
            );

            if game_is_compatible(&proof.instances[ideal], &specialization[current_idx].0) {
                let mut path = Vec::new();
                path.push(ideal);
                loop {
                    let cur = predecessors[path.last().unwrap()];
                    path.push(cur);
                    if cur == real {
                        break;
                    }
                }
                path.reverse();
                log::info!("found theorem {path:?}");
                return Some(Theorem {
                    proof,
                    specialization,
                    sequence: path,
                });
            } else {
                let reach = reachable_games(proof, &mut specialization, current_idx);
                for entry in reach {
                    if predecessors.contains_key(&entry) {
                        continue;
                    }
                    workque.push_back(entry);
                    predecessors.insert(entry, current_idx);
                }
            }
        }
        None
    }
}

fn specialize<'a>(
    specialization: &mut Vec<(GameInstance, &'a GameInstance)>,
    game: usize,
    generic_match: &'a GameInstance,
    generic_other: &'a GameInstance,
) -> usize {
    debug_assert!(game_is_compatible(&specialization[game].0, generic_match));

    if game_is_equivalent(&specialization[game].0, generic_match) {
        log::debug!(
            "potential gamehop with exact match {} -- {}",
            generic_match.name,
            generic_other.name
        );
        specialization
            .iter()
            .position(|(inst, _ref)| game_is_equivalent(generic_other, inst))
            .unwrap()
    } else {
        log::debug!(
            "potential gamehop with generalized match {} -- {}",
            generic_match.name,
            generic_other.name
        );
        let mut new_game = generic_other.clone();
        new_game.consts = new_game
            .consts
            .into_iter()
            .map(|(var, val)| {
                if matches!(val, Expression::Identifier(_)) {
                    let other_val = specialization[game]
                        .0
                        .consts
                        .iter()
                        .find_map(|(other_var, other_val)| {
                            if var.name == other_var.name {
                                Some(other_val)
                            } else {
                                None
                            }
                        })
                        .unwrap();

                    match other_val {
                        Expression::Identifier(_) => (var, val),
                        Expression::BooleanLiteral(_) => (var, other_val.clone()),
                        _ => {
                            unimplemented!()
                        }
                    }
                } else {
                    (var, val)
                }
            })
            .collect();

        if let Some(pos) = specialization
            .iter()
            .position(|(inst, _ref)| game_is_equivalent(&new_game, inst))
        {
            pos
        } else {
            specialization.push((new_game, generic_other));
            specialization.len() - 1
        }
    }
}

fn other_game<'a>(
    proof: &'a Proof,
    specialization: &mut Vec<(GameInstance, &'a GameInstance)>,
    game: usize,
    hop: &'a GameHop,
) -> Option<usize> {
    match hop {
        GameHop::Equivalence(eq) => {
            if game_is_compatible(
                &specialization[game].0,
                proof.find_game_instance(&eq.left_name).unwrap(),
            ) {
                return Some(specialize(
                    specialization,
                    game,
                    proof.find_game_instance(&eq.left_name).unwrap(),
                    proof.find_game_instance(&eq.right_name).unwrap(),
                ));
            }
            if game_is_compatible(
                &specialization[game].0,
                proof.find_game_instance(&eq.right_name).unwrap(),
            ) {
                return Some(specialize(
                    specialization,
                    game,
                    proof.find_game_instance(&eq.right_name).unwrap(),
                    proof.find_game_instance(&eq.left_name).unwrap(),
                ));
            }
            return None;
        }
        GameHop::Reduction(red) => {
            let left = proof
                .find_game_instance(&red.left().construction_game_instance_name().as_str())
                .unwrap();
            let right = proof
                .find_game_instance(&red.right().construction_game_instance_name().as_str())
                .unwrap();
            if game_is_compatible(&specialization[game].0, left) {
                return Some(specialize(specialization, game, left, right));
            }
            if game_is_compatible(&specialization[game].0, right) {
                return Some(specialize(specialization, game, right, left));
            }
            return None;
        }
    }
}

fn reachable_games<'a>(
    proof: &'a Proof,
    specialization: &mut Vec<(GameInstance, &'a GameInstance)>,
    game: usize,
) -> impl Iterator<Item = usize> {
    // let (left, right): (Vec<_>, Vec<_>) = proof
    //     .game_hops
    //     .iter()
    //     .map(|hop| other_game(proof, specialization, game, hop))
    //     .unzip();

    let mut specialization = specialization;
    let mut positions = Vec::new();
    for hop in &proof.game_hops {
        if let Some(position) = other_game(proof, specialization, game, hop) {
            positions.push(position);
        }
    }
    positions.into_iter()
}

fn game_is_equivalent(lhs: &GameInstance, rhs: &GameInstance) -> bool {
    game_is_compatible(lhs, rhs) && game_is_compatible(rhs, lhs)
}

fn game_is_compatible(specific: &GameInstance, general: &GameInstance) -> bool {
    if specific.game.name != general.game.name {
        return false;
    }
    if specific.types != general.types {
        println!("b");
        return false;
    }

    let specific_const_names: HashSet<_> =
        specific.consts.iter().map(|(var, val)| &var.name).collect();
    let general_const_names: HashSet<_> =
        general.consts.iter().map(|(var, val)| &var.name).collect();

    if specific_const_names != general_const_names {
        return false;
    }

    specific.consts.iter().all(|(var, val)| {
        let other_val = general
            .consts
            .iter()
            .find_map(|(other_var, other_val)| {
                if var.name == other_var.name {
                    Some(other_val)
                } else {
                    None
                }
            })
            .unwrap();
        if matches!(val, Expression::Identifier(_)) {
            return val == other_val;
        }
        if matches!(val, Expression::BooleanLiteral(_))
            || matches!(val, Expression::IntegerLiteral(_))
        {
            return val == other_val || matches!(other_val, Expression::Identifier(_));
        }
        unimplemented!()
    })
}
