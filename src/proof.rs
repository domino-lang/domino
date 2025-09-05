use itertools::Itertools;
use std::collections::{HashMap, HashSet, VecDeque};

use crate::{
    expressions::Expression,
    gamehops::GameHop,
    theorem::{GameInstance, Theorem},
};

#[derive(Debug, Clone)]
pub struct Proof<'a> {
    name: String,
    left_name: String,
    right_name: String,

    // Specialized Instance -> reference to more general instance in the theorem
    specialization: Vec<(GameInstance, String, Vec<(String, String)>)>,
    gamehops: Vec<GameHop<'a>>,
    sequence: Vec<usize>,
    hops: Vec<usize>,
}

impl<'a> Proof<'a> {
    pub(crate) fn try_new(
        instances: &Vec<GameInstance>,
        gamehops: &Vec<GameHop<'a>>,
        name: String,
        left_name: String,
        right_name: String,
    ) -> Option<Proof<'a>> {
        let real = instances.iter().position(|inst| inst.name == left_name)?;
        let ideal = instances.iter().position(|inst| inst.name == right_name)?;

        let mut specialization: Vec<_> = instances
            .iter()
            .map(|inst| (inst.clone(), inst.name().to_string(), Vec::new()))
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

            if game_is_compatible(&instances[ideal], &specialization[current_idx].0) {
                let mut path = Vec::new();
                let mut hops = Vec::new();
                path.push(ideal);
                loop {
                    let (cur, hop) = predecessors[path.last().unwrap()];
                    path.push(cur);
                    hops.push(hop);
                    if cur == real {
                        break;
                    }
                }
                path.reverse();
                hops.reverse();
                log::info!("found theorem; games: {path:?}, gamehops: {hops:?}");
                return Some(Proof {
                    name,
                    left_name,
                    right_name,
                    specialization,
                    gamehops: gamehops.clone(),
                    sequence: path,
                    hops,
                });
            } else {
                let reach = reachable_games(instances, gamehops, &mut specialization, current_idx);
                for (entry, hop) in reach {
                    if predecessors.contains_key(&entry) {
                        continue;
                    }
                    workque.push_back(entry);
                    predecessors.insert(entry, (current_idx, hop));
                }
            }
        }
        None
    }
}

impl std::fmt::Display for Proof<'_> {
    // This trait requires `fmt` with this exact signature.
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        //writeln!(f, "Theorem {}:", self.theorem.name)?;
        writeln!(f, "Real")?;
        for i in 0..self.hops.len() {
            let left = &self.specialization[self.sequence[i]];
            let right = &self.specialization[self.sequence[i + 1]];
            let hop = &self.gamehops[self.hops[i]];

            writeln!(
                f,
                "{} ({})",
                left.1,
                left.2
                    .iter()
                    .map(|(a, b)| { format!("{}={}", a, b) })
                    .join(", ")
            )?;
            writeln!(f, "    {}", hop)?;
            writeln!(
                f,
                "{} ({})",
                right.1,
                right
                    .2
                    .iter()
                    .map(|(a, b)| { format!("{}={}", a, b) })
                    .join(", ")
            )?;
        }
        writeln!(f, "Ideal")?;
        Ok(())
    }
}

fn specialize<'a>(
    specialization: &mut Vec<(GameInstance, String, Vec<(String, String)>)>,
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
            .position(|(inst, _ref, _assign)| game_is_equivalent(generic_other, inst))
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
            .position(|(inst, _ref, _assign)| game_is_equivalent(&new_game, inst))
        {
            pos
        } else {
            let assignments = assignments(&new_game, generic_other);
            specialization.push((new_game, generic_other.name().to_string(), assignments));
            specialization.len() - 1
        }
    }
}

fn other_game<'a>(
    instances: &Vec<GameInstance>,
    gamehops: &Vec<GameHop<'a>>,
    specialization: &mut Vec<(GameInstance, String, Vec<(String, String)>)>,
    game: usize,
    hop: &'a GameHop,
) -> Option<usize> {
    let left_game = instances
        .iter()
        .find(|inst| inst.name == hop.left_game_instance_name())
        .unwrap();
    let right_game = instances
        .iter()
        .find(|inst| inst.name == hop.right_game_instance_name())
        .unwrap();

    if game_is_compatible(&specialization[game].0, left_game) {
        return Some(specialize(specialization, game, left_game, right_game));
    }
    if game_is_compatible(&specialization[game].0, right_game) {
        return Some(specialize(specialization, game, right_game, left_game));
    }
    None
}

fn reachable_games(
    instances: &Vec<GameInstance>,
    gamehops: &Vec<GameHop>,
    specialization: &mut Vec<(GameInstance, String, Vec<(String, String)>)>,
    game: usize,
) -> impl Iterator<Item = (usize, usize)> {
    // let (left, right): (Vec<_>, Vec<_>) = theorem
    //     .game_hops
    //     .iter()
    //     .map(|hop| other_game(theorem, specialization, game, hop))
    //     .unzip();

    let specialization = specialization;
    let mut positions = Vec::new();
    for (idx, hop) in gamehops.iter().enumerate() {
        if let Some(position) = other_game(instances, gamehops, specialization, game, hop) {
            positions.push((position, idx));
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

    let specific_const_names: HashSet<_> = specific
        .consts
        .iter()
        .map(|(var, _val)| &var.name)
        .collect();
    let general_const_names: HashSet<_> =
        general.consts.iter().map(|(var, _val)| &var.name).collect();

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

fn assignments(game: &GameInstance, reference: &GameInstance) -> Vec<(String, String)> {
    game.consts
        .iter()
        .filter_map(|(var, val)| {
            let other_val = reference
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

            if let Expression::Identifier(ident) = other_val {
                if let Expression::BooleanLiteral(lit) = val {
                    return Some((ident.ident(), lit.clone()));
                }
            }
            None
        })
        .collect()
}
