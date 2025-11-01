// SPDX-License-Identifier: MIT OR Apache-2.0

use miette::Diagnostic;
use thiserror::Error;

use crate::parser::reduction::ReductionMapping;

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

#[derive(Debug, Clone)]
pub struct Assumption {
    pub name: String,
    pub left_name: String,
    pub right_name: String,
}

#[derive(Debug, Clone)]
pub struct Reduction<'a> {
    left: ReductionMapping<'a>,
    right: ReductionMapping<'a>,

    assumption_name: String,
}

impl<'a> Reduction<'a> {
    pub(crate) fn new(
        left: ReductionMapping<'a>,
        right: ReductionMapping<'a>,
        assumption_name: String,
    ) -> Self {
        Self {
            left,
            right,
            assumption_name,
        }
    }

    pub(crate) fn left(&self) -> &ReductionMapping<'a> {
        &self.left
    }

    pub(crate) fn right(&self) -> &ReductionMapping<'a> {
        &self.right
    }

    pub(crate) fn assumption_name(&self) -> &str {
        &self.assumption_name
    }
}

#[derive(Debug, Error, Diagnostic)]
pub enum ReductionError {}
