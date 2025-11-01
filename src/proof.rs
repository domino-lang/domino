// SPDX-License-Identifier: MIT OR Apache-2.0

use std::collections::{HashMap, HashSet, VecDeque};

use crate::{expressions::Expression, gamehops::GameHop, theorem::GameInstance};

#[derive(Debug, Clone)]
pub struct Proof<'a> {
    pub name: String,
    pub left_name: String,
    pub right_name: String,

    // Specialized Instance -> reference to more general instance in the theorem
    specialization: Vec<Specialization>,
    gamehops: Vec<GameHop<'a>>,
    sequence: Vec<usize>,
    hops: Vec<usize>,
}

/// A value assigned to a constant, already encoded as a string.
#[derive(Debug, Clone)]
struct ConstAssignment {
    name: String,
    assigned_value: String,
}

/// GameInstances often refer to families of game instances, because they are parameterized.
/// This type is a specific specialization of generic game instances that matches a game instance
/// on the indistinguishability proof path.
#[derive(Debug, Clone)]
struct Specialization {
    /// The specialized game instance. Has the constant overwritten, but still has the original
    /// name
    game_instance: GameInstance,

    /// The constants that were overwritten, in a somehwat ready-to-print form
    const_assignments: Vec<ConstAssignment>,
}

impl Specialization {
    fn name(&self) -> &str {
        &self.game_instance.name
    }
}

impl<'a> Proof<'a> {
    /// Tries to find a swquence of game hops that proves that the game instance with name
    /// `left_name` is indistinguishable from the game instance with name `right_name`
    pub(crate) fn try_new(
        instances: &[GameInstance],
        gamehops: &[GameHop<'a>],
        name: String,
        left_name: String,
        right_name: String,
    ) -> Option<Proof<'a>> {
        // get the game instances by name
        let left = instances.iter().position(|inst| inst.name == left_name)?;
        let right = instances.iter().position(|inst| inst.name == right_name)?;

        // prepare the specialization vector. Initially contains just the game istances as defined
        // in the theorem.
        let mut specialization: Vec<_> = instances
            .iter()
            .map(|inst| Specialization {
                game_instance: inst.clone(),
                const_assignments: Vec::new(),
            })
            .collect();

        // preppare the work queue with the start value.
        let mut workque = VecDeque::new();
        workque.push_back(left);

        // A table of backlinks: specialization index -> (specialization index, game hop index)
        let mut predecessors = HashMap::new();

        while !workque.is_empty() {
            let current_inst_idx = workque.pop_front().unwrap();
            log::debug!(
                "next up: {current_inst_idx} : {}",
                &specialization[current_inst_idx].game_instance.name
            );

            // Check whether we are done. This is the case if the current specialized game instance
            // matches the target (the right instance).
            if game_is_compatible(
                &instances[right],
                &specialization[current_inst_idx].game_instance,
            ) {
                // If we are done, build the proof path from the backlinks.
                let mut path = Vec::new();
                let mut hops = Vec::new();
                path.push(right);
                loop {
                    let (cur, hop) = predecessors[path.last().unwrap()];

                    path.push(cur);
                    hops.push(hop);

                    if cur == left {
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
                    gamehops: gamehops.to_vec(),
                    sequence: path,
                    hops,
                });
            } else {
                let reach =
                    reachable_games(instances, gamehops, &mut specialization, current_inst_idx);

                // next_inst_idx: offset into specializations, i.e. designating a Game Instance
                // hop_idx: offset into gamehops
                for (next_inst_idx, hop_idx) in reach {
                    if predecessors.contains_key(&next_inst_idx) {
                        continue;
                    }
                    workque.push_back(next_inst_idx);
                    predecessors.insert(next_inst_idx, (current_inst_idx, hop_idx));
                }
            }
        }
        None
    }
}

/// Specialize a game instance that matches generic_match to one that matches generic_other. Use
/// the assignments of the current specialization.
fn specialize<'a>(
    specializations: &mut Vec<Specialization>,
    spec_game_inst_idx: usize,
    generic_match: &'a GameInstance,
    generic_other: &'a GameInstance,
) -> usize {
    debug_assert!(game_is_compatible(
        &specializations[spec_game_inst_idx].game_instance,
        generic_match
    ));

    if game_is_equivalent(
        &specializations[spec_game_inst_idx].game_instance,
        generic_match,
    ) {
        // If the game instance at the provided index matches exactly, find and
        // return the index to the other one.

        log::debug!(
            "potential gamehop with exact match {} -- {}",
            generic_match.name,
            generic_other.name
        );

        specializations
            .iter()
            .position(|specialization| {
                game_is_equivalent(generic_other, &specialization.game_instance)
            })
            .unwrap()
    } else {
        // Create a specialization based on the other side of the game hop and the constant
        // assignments of the current specialization (i.e. spec_game_inst_idx)

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
                // Find all constants that the other side of the game hop has set to identifiers
                if let Expression::Identifier(_) = val {
                    // find the values that our current specialization assigns to it
                    let other_val = specializations[spec_game_inst_idx]
                        .game_instance
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

                    // if it is a literal, copy it over, otherwise keep the identifier
                    match other_val {
                        Expression::Identifier(_) => (var, val),
                        Expression::BooleanLiteral(_) => (var, other_val.clone()),
                        Expression::IntegerLiteral(_) => (var, other_val.clone()),
                        _ => {
                            unimplemented!()
                        }
                    }
                } else {
                    (var, val)
                }
            })
            .collect();

        // Check whether we already have this specialization. Otherwise push it and return the
        // index.
        specializations
            .iter()
            .position(|specialization| game_is_equivalent(&new_game, &specialization.game_instance))
            .unwrap_or_else(|| {
                let idx = specializations.len();
                let const_assignments = assignments(&new_game, generic_other);
                let specialization = Specialization {
                    game_instance: new_game,
                    const_assignments,
                };

                specializations.push(specialization);
                idx
            })
    }
}

/// Takes a game (by index into the specialization vector) and a game hop and tries to find the
/// specialized game that is the other side of the game hop.
///
/// If the game matches neither side of the game hop, it returns None.
/// If it does, the index into the specialization vector is returned.
/// If the vector does not yet contain the specialization, it is created.
fn other_game(
    instances: &[GameInstance],
    specialization: &mut Vec<Specialization>,
    game: usize,
    hop: &GameHop,
) -> Option<usize> {
    let left_game = instances
        .iter()
        .find(|inst| inst.name == hop.left_game_instance_name())
        .unwrap();
    let right_game = instances
        .iter()
        .find(|inst| inst.name == hop.right_game_instance_name())
        .unwrap();

    if game_is_compatible(&specialization[game].game_instance, left_game) {
        return Some(specialize(specialization, game, left_game, right_game));
    }
    if game_is_compatible(&specialization[game].game_instance, right_game) {
        return Some(specialize(specialization, game, right_game, left_game));
    }
    None
}

/// Returns a vector of index pairs that point to specialized game instances that can be reached
/// with a single game hop, as well as that game hop's index.
fn reachable_games(
    instances: &[GameInstance],
    gamehops: &[GameHop],
    specialization: &mut Vec<Specialization>,
    game: usize,
) -> Vec<(usize, usize)> {
    let mut positions = Vec::new();
    for (idx, hop) in gamehops.iter().enumerate() {
        if let Some(position) = other_game(instances, specialization, game, hop) {
            positions.push((position, idx));
        }
    }
    positions
}

fn game_is_equivalent(lhs: &GameInstance, rhs: &GameInstance) -> bool {
    game_is_compatible(lhs, rhs) && game_is_compatible(rhs, lhs)
}

/// Check that the left game instance is a more specialized version of the right game instance.
fn game_is_compatible(specific: &GameInstance, general: &GameInstance) -> bool {
    if specific.game.name != general.game.name {
        return false;
    }

    // TODO: verify this does the right thing with param types!
    if specific.types != general.types {
        return false;
    }

    // Collect the names of specific and generic constant parameters. This should always be the
    // same. Check this using an assert to find bugs
    let specific_const_names: HashSet<_> = specific
        .consts
        .iter()
        .map(|(var, _val)| &var.name)
        .collect();
    let general_const_names: HashSet<_> =
        general.consts.iter().map(|(var, _val)| &var.name).collect();
    debug_assert_eq!(specific_const_names, general_const_names);

    // Check for all constant assignments that
    //
    // 1. if the specific game uses an identifier, then the general one uses the same
    // 2. if the specific game uses a concrete value (i.e. int or bool literal), then the general
    //    either uses the same value or an identifier.
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

/// Extract the assignments where the the game is more specific than the reference.
fn assignments(game: &GameInstance, reference: &GameInstance) -> Vec<ConstAssignment> {
    game.consts
        .iter()
        .filter_map(|(var, val)| {
            // find the assigned value in the reference
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

            // if the referenced is an identifier, write down the value assigned in game
            if let Expression::Identifier(ident) = other_val {
                if let Expression::BooleanLiteral(lit) = val {
                    return Some(ConstAssignment {
                        name: ident.ident(),
                        assigned_value: lit.clone(),
                    });
                }
                if let Expression::IntegerLiteral(lit) = val {
                    return Some(ConstAssignment {
                        name: ident.ident(),
                        assigned_value: lit.to_string(),
                    });
                }
            }
            None
        })
        .collect()
}

impl std::fmt::Display for ConstAssignment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}={}", self.name, self.assigned_value)
    }
}

/// A utility type that implements Display if T implements Display and prints the elements of the
/// slice with a ", " delimiter
struct CommaSeperated<'a, T>(&'a [T]);

impl<'a, T: std::fmt::Display> std::fmt::Display for CommaSeperated<'a, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut sep = "";

        for elem in self.0 {
            write!(f, "{sep}{elem}")?;
            sep = ", ";
        }

        Ok(())
    }
}

impl std::fmt::Display for Specialization {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let name = self.name();
        let assignments = CommaSeperated(&self.const_assignments);

        write!(f, "{name} ({assignments})",)
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

            writeln!(f, "{left}")?;
            writeln!(f, "    {hop}")?;
            writeln!(f, "{right}")?;
        }
        writeln!(f, "Ideal")?;
        Ok(())
    }
}
