use itertools::Itertools;
use std::collections::hash_map::DefaultHasher;
use std::collections::HashSet;
use std::hash::{Hash, Hasher};
use std::iter::FromIterator;

use crate::{
    package::{Edge, PackageInstance},
    project::error::{Error, Result},
    proof::{Proof, Reduction},
    util::resolver::{Named, Resolver, SliceResolver},
};

/*
approach:

1. find the diff of left/right games and assumptions, recoding the path of signatures
2. for both left and right:
2.1. in the game, walk the path given by these signatures
2.2. check that the subgame starting by that root is identical


22-09-21 conceptualization
1. find diffs
2. check that diffs are the same package and params
    -> actually it might make sense to make this a separate function
3. in the game hop games, walk back the paths (diff->roots) from the assumption
4. use these as roots to a new composition (both left and right) and generate that (take care of exports)
5. compare to assumption

- a lot of this is comparing parts of the composition. Maybe we should add that as a function on the composition.
- what makes these comparisons tricky is that they don't need to be equal, they just need to be at least as strict as the assumption. It's okay if it offers less oracles to the adversary.
  -> this only concerns the exports


impl Composition {
    fn
}
 */

fn same_package(left: &PackageInstance, right: &PackageInstance) -> bool {
    left.pkg == right.pkg
}

pub fn verify(red: &Reduction, proof: &Proof) -> Result<()> {
    let left_mapping = red.left();
    let right_mapping = red.right();
    let assumption_name = red.assumption_name();

    // resolve game instances
    let game_instance_resolver = SliceResolver(proof.instances());

    let left = left_mapping.as_game_inst_name();
    let left = game_instance_resolver
        .resolve(left)
        .ok_or(Error::ProofCheck(format!(
            "could not find game instance {left:?}"
        )))?;
    let right = right_mapping.as_game_inst_name();
    let right = game_instance_resolver
        .resolve(right)
        .ok_or(Error::ProofCheck(format!(
            "could not find game instance {right:?}"
        )))?;

    let assumption_resolver = SliceResolver(proof.assumptions());
    let assumption = assumption_resolver
        .resolve(assumption_name)
        .ok_or(Error::ProofCheck(format!(
            "could not find assumption {assumption_name:?}"
        )))?;

    let assumption_left = &assumption.left_name;
    let assumption_left = game_instance_resolver
        .resolve(&assumption.left_name)
        .ok_or(Error::ProofCheck(format!(
            "could not find game instance {assumption_left:?}"
        )))?;

    let assumption_right = &assumption.right_name;
    let assumption_right = game_instance_resolver
        .resolve(&assumption.right_name)
        .ok_or(Error::ProofCheck(format!(
            "could not find game instance {assumption_right:?}"
        )))?;

    let leftmap = left_mapping.pkg_maps();
    let rightmap = right_mapping.pkg_maps();

    // PackageInstances are only mentioned once
    if !(leftmap.iter().map(|(from, _to)| from).all_unique()) {
        return Err(Error::ProofCheck(format!("leftmap has duplicate from")));
    }
    if !(leftmap.iter().map(|(_from, to)| to).all_unique()) {
        return Err(Error::ProofCheck(format!("leftmap has duplicate to")));
    }
    if !(rightmap.iter().map(|(from, _to)| from).all_unique()) {
        return Err(Error::ProofCheck(format!("rightmap has duplicate from")));
    }
    if !(rightmap.iter().map(|(_from, to)| to).all_unique()) {
        return Err(Error::ProofCheck(format!("rightmap has duplicate to")));
    }

    // TODO check that all names are well-defined (or has that already happened?)

    let right_package_resolver = SliceResolver(&right.game().pkgs);
    let left_package_resolver = SliceResolver(&left.game().pkgs);
    let assumption_right_package_resolver = SliceResolver(&assumption_right.game().pkgs);
    let assumption_left_package_resolver = SliceResolver(&assumption_left.game().pkgs);

    // Mapping may only occure with the same package type
    let mismatches_left: Vec<_> = leftmap
        .iter()
        .map(|(from, to)| {
            let assumption_left_pkg_inst =
                assumption_left_package_resolver
                    .resolve(from)
                    .ok_or(Error::ProofCheck(format!(
                        "error resolving package {from} in left game {}",
                        assumption_left.name()
                    )))?;

            let left_pkg_inst =
                left_package_resolver
                    .resolve(to)
                    .ok_or(Error::ProofCheck(format!(
                        "error resolving package {to} in left assumption game {}",
                        left.name()
                    )))?;

            Ok((left_pkg_inst, assumption_left_pkg_inst))
        })
        .filter(|to| match to {
            Ok((from, to)) => !same_package(from, to),
            Err(_) => true,
        })
        .map(|res| {
            res.map(|(from, to)| {
                format!(
                    "{} and {} have different types",
                    from.as_name(),
                    to.as_name()
                )
            })
        })
        .collect::<Result<_>>()?;

    if !mismatches_left.is_empty() {
        return Err(Error::ProofCheck(format!(
            "leftmap has incompatible package instances: {}",
            mismatches_left.join(", ")
        )));
    }

    let mismatches_right: Vec<_> = rightmap
        .iter()
        .map(|(from, to)| {
            let assumption_right_pkg_inst =
                assumption_right_package_resolver
                    .resolve(from)
                    .ok_or(Error::ProofCheck(format!(
                        "error resolving package {from} in right game {}",
                        assumption_right.name()
                    )))?;

            let right_pkg_inst =
                right_package_resolver
                    .resolve(to)
                    .ok_or(Error::ProofCheck(format!(
                        "error resolving package {to} in right assumption game {}",
                        right.name()
                    )))?;

            Ok((right_pkg_inst, assumption_right_pkg_inst))
        })
        .filter(|to| match to {
            Ok((from, to)) => !same_package(from, to),
            Err(_) => true,
        })
        .map(|res| {
            res.map(|(from, to)| {
                format!(
                    "{} and {} have different types",
                    from.as_name(),
                    to.as_name()
                )
            })
        })
        .collect::<Result<_>>()?;

    if !mismatches_right.is_empty() {
        return Err(Error::ProofCheck(format!(
            "rightmap has incompatible package instances: {}",
            mismatches_right.join(", ")
        )));
    }

    // Every PackageInstance in the assumptions is mapped
    if assumption_left.game().pkgs.len() != leftmap.len() {
        return Err(Error::ProofCheck(format!(
            "Some package instances in left assumption are not mapped: {} != {:?}",
            assumption_left.game().pkgs.len(),
            leftmap
        )));
    }
    if assumption_right.game().pkgs.len() != rightmap.len() {
        return Err(Error::ProofCheck(format!(
            "Some package instances in right assumption are not mapped"
        )));
    }

    // Every PackageInstance in the game, which is mapped
    // only calls other mapped package instances
    for Edge(from, to, _sig) in &left.game().edges {
        let from = &left.game().pkgs[*from].name;
        let from_is_mapped = leftmap
            .iter()
            .find(|(_, game_inst_name)| game_inst_name == from)
            .is_some();

        let to = &left.game().pkgs[*to].name;
        let to_is_mapped = leftmap
            .iter()
            .find(|(_, game_inst_name)| game_inst_name == to)
            .is_some();

        if from_is_mapped && !to_is_mapped {
            return Err(Error::ProofCheck(format!(
                "Left Game: Mapped package {from} calls unmappedpackage {to}",
            )));
        }
    }
    for Edge(from, to, _sig) in &right.game().edges {
        let from = &right.game().pkgs[*from].name;
        let from_is_mapped = rightmap
            .iter()
            .find(|(_, game_inst_name)| game_inst_name == from)
            .is_some();

        let to = &right.game().pkgs[*to].name;
        let to_is_mapped = rightmap
            .iter()
            .find(|(_, game_inst_name)| game_inst_name == to)
            .is_some();

        if from_is_mapped && !to_is_mapped {
            return Err(Error::ProofCheck(format!(
                "Right Game: Mapped package {from} calls unmappedpackage {to}",
            )));
        }
    }

    // The PackageInstances in the games which are *not* mapped need to be identical
    let unmapped_left: HashSet<_> =
        HashSet::from_iter(left.game().pkgs.iter().filter(|pkg_inst| {
            leftmap
                .iter()
                .find(|(_, game_inst_name)| game_inst_name == &pkg_inst.name)
                .is_none()
        }));
    let unmapped_right = HashSet::from_iter(right.game().pkgs.iter().filter(|pkg_inst| {
        rightmap
            .iter()
            .find(|(_, game_inst_name)| game_inst_name == &pkg_inst.name)
            .is_none()
    }));

    if unmapped_left != unmapped_right {
        let mut left_summary = unmapped_left
            .iter()
            .map(|pkg_inst| {
                let mut hasher = DefaultHasher::new();
                pkg_inst.hash(&mut hasher);
                (pkg_inst.as_name(), hasher.finish())
            })
            .collect::<Vec<_>>();

        let mut right_summary = unmapped_right
            .iter()
            .map(|pkg_inst| {
                let mut hasher = DefaultHasher::new();
                pkg_inst.hash(&mut hasher);
                (pkg_inst.as_name(), hasher.finish())
            })
            .collect::<Vec<_>>();

        left_summary.sort();
        right_summary.sort();

        let example_left: &PackageInstance = unmapped_left
            .iter()
            .filter(|inst| inst.as_name() == "xor")
            .take(1)
            .collect::<Vec<_>>()[0];

        let example_right: &PackageInstance = unmapped_right
            .iter()
            .filter(|inst| inst.as_name() == "xor")
            .take(1)
            .collect::<Vec<_>>()[0];

        return Err(Error::ProofCheck(format!(
            "unmapped package instances not equal: \n{:#?} and \n{:#?}.\nexample: \n {:#?}\n {:#?}",
            left_summary, right_summary, example_left, example_right
        )));
    }

    Ok(())
}
