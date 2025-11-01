// SPDX-License-Identifier: MIT OR Apache-2.0

/*
 *
 * old:
 * We want to abstract over
 * - system state variables (__self_state, __global_state)
 * - package state vars
 * - package params
 * - local variables
 *
 *
 * It must be possible to use a variables without having to specify it's sort.
 * This means the type/sort must be part of the "spec", not the regular value.
 *
 * We also want to be able to get the name of a variable, as a string.
 *
 *   Problem: not all variables have names -- e.g. pkg state vars only exist inside the package state
 *   and we use accessors to get to them.
 *
 *      Solution 1: Skip cases like this and concentrate on locals and system state vars
 *
 *          Feels half-assed, but also does solve the only real issues of scope pollution and
 *          getting the variable names as strings
 *
 *      Solution 2: Solve these problems in a subtrait and keep the main trait more general
 *
 *          I guess this is more "clean", but begs the question of why to formalize it this way.
 *          Do we really need to? If not, Solution 1 seems better
 *
 *      Solution 3: Change how package state and param variables are accessed and just bind them
 *                  into the local state, so they all are variables on SMT-level, too
 *
 *          This seems to require a lot of changes with little benefit.
 *
 *
 *   Conclusion: I think I'll go with Solition 1 for now. If we find the need to also have a pattern for
 *               package state and params, we can add that as a separate trait, and maybe make the
 *               VariablePattern a subtrait of that.
 *
 * new:
 * We want to abstract over SMT-level variables, i.e.
 * - system state variables (__self_state, __global_state)
 * - local variables
 *
 */

use crate::{
    types::Type,
    writers::smt::{exprs::SmtExpr, sorts::Sort},
};

use super::{
    DatastructurePattern, GameStatePattern as GameStateDataStructurePattern, PackageStatePattern,
};

pub trait VariablePattern {
    type SpecInfo;

    fn name(&self) -> String;
    fn sort(&self, spec: &Self::SpecInfo) -> Sort;

    fn name_sort_tuple(&self, spec: &Self::SpecInfo) -> (String, SmtExpr) {
        (self.name(), self.sort(spec).into())
    }
}

macro_rules! impl_VariablePatternIntoSmtExpr {
    ($lifetime:lifetime, $type:ty) => {
        impl<$lifetime> From<$type> for $crate::writers::smt::exprs::SmtExpr {
            fn from(value: $type) -> Self {
                <$type as $crate::writers::smt::patterns::variables::VariablePattern>::name(&value)
                    .into()
            }
        }
    };
    ($pattern:ident) => {
        impl From<$type> for $crate::writers::smt::exprs::SmtExpr {
            fn from(value: $type) -> Self {
                <$type as $crate::writers::smt::patterns::VariablePattern>::name(&value).into()
            }
        }
    };
}

impl_VariablePatternIntoSmtExpr!('a, &'a SelfStatePattern);
impl_VariablePatternIntoSmtExpr!('a, &'a GameStatePattern);
impl_VariablePatternIntoSmtExpr!('a, LocalVariablePattern<'a>);

pub struct SelfStatePattern;

impl<'a> VariablePattern for &'a SelfStatePattern {
    type SpecInfo = PackageStatePattern<'a>;

    fn name(&self) -> String {
        "<pkg-state>".to_string()
    }

    fn sort(&self, spec_info: &Self::SpecInfo) -> Sort {
        spec_info.sort(vec![])
    }
}

pub struct GameStatePattern;

impl<'a> VariablePattern for &'a GameStatePattern {
    type SpecInfo = GameStateDataStructurePattern<'a>;

    fn name(&self) -> String {
        "<game-state>".to_string()
    }

    fn sort(&self, spec_info: &Self::SpecInfo) -> Sort {
        spec_info.sort(vec![])
    }
}

pub struct LocalVariablePattern<'a>(&'a str);

impl VariablePattern for LocalVariablePattern<'_> {
    type SpecInfo = Type;

    fn name(&self) -> String {
        self.0.to_string()
    }

    fn sort(&self, spec: &Self::SpecInfo) -> Sort {
        spec.clone().into()
    }
}
