// SPDX-License-Identifier: MIT OR Apache-2.0

/*
use super::{
    assumption::ResolvedAssumption,
    equivalence::{Equivalence, ResolvedEquivalence},
    error::{Error, Result},
    reduction::{Reduction, ResolvedReduction},
    Assumption, Project,
};
 */
/*

impl Project {
    // i is passed for error reporting only
    pub fn resolve_reduction(&self, reduction: &Reduction, i: usize) -> Result<ResolvedReduction> {
        let left = self
            .get_game(&reduction.left)
            .ok_or(Error::UndefinedGame(
                reduction.left.clone(),
                format!("in left of reduction {i}"),
            ))?
            .clone();

        let right = self
            .get_game(&reduction.right)
            .ok_or(Error::UndefinedGame(
                reduction.right.clone(),
                format!("in right of reduction {i}"),
            ))?
            .clone();

        let assumption =
            self.get_assumption(&reduction.assumption)
                .ok_or(Error::UndefinedAssumption(
                    reduction.assumption.clone(),
                    format!("in reduction {i}"),
                ))?;

        let assumption = self.resolve_assumption(assumption)?;

        let assumption_name = reduction.assumption.clone();

        let leftmap: Result<Vec<_>> = reduction
            .leftmap
            .iter()
            .map(|(from, to)| {
                let gameindex = left.pkgs.iter().position(|pkg| &pkg.name == from).ok_or(
                    Error::UndefinedMapping(from.clone(), format!("in reduction {i}, left game")),
                )?;
                let assumptionindex = assumption
                    .left
                    .pkgs
                    .iter()
                    .position(|pkg| &pkg.name == to)
                    .ok_or(Error::UndefinedMapping(
                        to.clone(),
                        format!("in reduction {i}, left assumption"),
                    ))?;
                Ok((gameindex, assumptionindex))
            })
            .collect();
        let leftmap = leftmap?;

        let rightmap: Result<Vec<_>> = reduction
            .rightmap
            .iter()
            .map(|(from, to)| {
                let gameindex = right.pkgs.iter().position(|pkg| &pkg.name == from).ok_or(
                    Error::UndefinedMapping(from.clone(), format!("in reduction {i}, right game")),
                )?;
                let assumptionindex = assumption
                    .right
                    .pkgs
                    .iter()
                    .position(|pkg| &pkg.name == to)
                    .ok_or(Error::UndefinedMapping(
                        to.clone(),
                        format!("in reduction {i}, right assumption"),
                    ))?;
                Ok((gameindex, assumptionindex))
            })
            .collect();
        let rightmap = rightmap?;

        Ok(ResolvedReduction {
            left,
            right,
            assumption,
            assumption_name,
            leftmap,
            rightmap,
        })
    }

    pub fn resolve_equivalence(&self, eq: &Equivalence) -> Result<ResolvedEquivalence> {
        let Equivalence {
            left,
            right,
            invariant_path,
            trees,
            ..
        } = eq;
        let trees = trees.clone();

        let left_err = Error::UndefinedGame(
            left.to_string(),
            format!("in resolving the equivalence between {left} and {right}"),
        );
        let right_err = Error::UndefinedGame(
            right.to_string(),
            format!("in resolving the equivalence between {left} and {right}"),
        );

        let left_game = self.get_game(left).ok_or(left_err)?.clone();
        let right_game = self.get_game(right).ok_or(right_err)?.clone();

        let inv_path = self.get_invariant_path(invariant_path);
        let invariant = std::fs::read_to_string(inv_path)?;

        let left_decl_smt_file = self.get_game_smt_file(left)?;
        let right_decl_smt_file = self.get_game_smt_file(right)?;
        let base_decl_smt_file = self.get_base_decl_smt_file(left, right)?;
        let const_decl_smt_file = self.get_const_decl_smt_file(left, right)?;
        let epilogue_smt_file = self.get_epilogue_smt_file(left, right)?;
        let joined_smt_file = self.get_joined_smt_file(left, right)?;

        Ok(ResolvedEquivalence {
            left: left_game,
            right: right_game,
            invariant,
            trees,

            left_decl_smt_file,
            right_decl_smt_file,
            base_decl_smt_file,
            const_decl_smt_file,
            epilogue_smt_file,
            joined_smt_file,
        })
    }

    pub fn resolve_assumption(&self, ass: &Assumption) -> Result<ResolvedAssumption> {
        let Assumption { left, right, .. } = ass;
        let left_err = Error::UndefinedGame(
            left.to_string(),
            format!("in resolving the assumption of {left} and {right}"),
        );
        let right_err = Error::UndefinedGame(
            right.to_string(),
            format!("in resolving the assumption of {left} and {right}"),
        );

        let left = self.get_game(left).ok_or(left_err)?.clone();
        let right = self.get_game(right).ok_or(right_err)?.clone();

        Ok(ResolvedAssumption { left, right })
    }
}

*/
