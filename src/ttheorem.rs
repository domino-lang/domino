use itertools::Itertools;
use std::collections::{HashMap, HashSet, VecDeque};

use crate::{
    expressions::Expression,
    gamehops::GameHop,
    theorem::{GameInstance, Theorem},
};

#[derive(Debug, Clone)]
pub struct TTheorem<'a> {
    theorem: &'a Theorem<'a>,
    // Specialized Instance -> reference to more general instance in the theorem
    specialization: Vec<(GameInstance, &'a GameInstance)>,
    sequence: Vec<usize>,
    hops: Vec<usize>,
}

impl<'a> TTheorem<'a> {
    pub(crate) fn try_new(theorem: &'a Theorem) -> Option<TTheorem<'a>> {
        let real = theorem
            .instances
            .iter()
            .position(|inst| inst.name == "Real")?;
        let ideal = theorem
            .instances
            .iter()
            .position(|inst| inst.name == "Ideal")?;

        let mut specialization: Vec<_> = theorem
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

            if game_is_compatible(&theorem.instances[ideal], &specialization[current_idx].0) {
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
                return Some(TTheorem {
                    theorem,
                    specialization,
                    sequence: path,
                    hops,
                });
            } else {
                let reach = reachable_games(theorem, &mut specialization, current_idx);
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

    fn assignments(
        &'a self,
        game: &'a GameInstance,
        hop: &'a GameHop,
    ) -> impl Iterator<Item = (String, String)> + 'a {
        let left = self
            .theorem
            .find_game_instance(hop.left_game_instance_name())
            .unwrap();
        let right = self
            .theorem
            .find_game_instance(hop.right_game_instance_name())
            .unwrap();

        let reference = if game_is_compatible(game, left) {
            left
        } else {
            right
        };

        game.consts.iter().filter_map(|(var, val)| {
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
    }
}

impl std::fmt::Display for TTheorem<'_> {
    // This trait requires `fmt` with this exact signature.
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        writeln!(f, "Theorem {}:", self.theorem.name)?;
        writeln!(f, "Real")?;
        for i in 0..self.hops.len() {
            let left = &self.specialization[self.sequence[i]];
            let right = &self.specialization[self.sequence[i + 1]];
            let hop = &self.theorem.game_hops[self.hops[i]];

            writeln!(
                f,
                "{} ({})",
                left.1.name,
                self.assignments(&left.0, hop)
                    .map(|(a, b)| { format!("{}={}", a, b) })
                    .join(", ")
            )?;
            writeln!(f, "    {}", hop)?;
            writeln!(
                f,
                "{} ({})",
                right.1.name,
                self.assignments(&right.0, hop)
                    .map(|(a, b)| { format!("{}={}", a, b) })
                    .join(", ")
            )?;
        }
        writeln!(f, "Ideal")?;
        Ok(())
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
    theorem: &'a Theorem,
    specialization: &mut Vec<(GameInstance, &'a GameInstance)>,
    game: usize,
    hop: &'a GameHop,
) -> Option<usize> {
    let left_game = theorem
        .find_game_instance(hop.left_game_instance_name())
        .unwrap();
    let right_game = theorem
        .find_game_instance(hop.right_game_instance_name())
        .unwrap();

    if game_is_compatible(&specialization[game].0, left_game) {
        return Some(specialize(specialization, game, left_game, right_game));
    }
    if game_is_compatible(&specialization[game].0, right_game) {
        return Some(specialize(specialization, game, right_game, left_game));
    }
    None
}

fn reachable_games<'a>(
    theorem: &'a Theorem,
    specialization: &mut Vec<(GameInstance, &'a GameInstance)>,
    game: usize,
) -> impl Iterator<Item = (usize, usize)> {
    // let (left, right): (Vec<_>, Vec<_>) = theorem
    //     .game_hops
    //     .iter()
    //     .map(|hop| other_game(theorem, specialization, game, hop))
    //     .unzip();

    let specialization = specialization;
    let mut positions = Vec::new();
    for (idx, hop) in theorem.game_hops.iter().enumerate() {
        if let Some(position) = other_game(theorem, specialization, game, hop) {
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
