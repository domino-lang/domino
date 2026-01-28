// SPDX-License-Identifier: MIT OR Apache-2.0

use std::fmt;

use conjecture::Conjecture;
use equivalence::Equivalence;
use hybrid::Hybrid;
use reduction::Reduction;

use crate::parser::ast::Identifier;

pub mod conjecture;
pub mod equivalence;
pub mod hybrid;
pub mod reduction;
//
// TODO: add a HybridArgument variant
#[derive(Debug, Clone)]
pub enum GameHop<'a> {
    Conjecture(Conjecture<'a>),
    Reduction(Reduction<'a>),
    Equivalence(Equivalence),
    Hybrid(Hybrid<'a>),
}

impl<'a> GameHop<'a> {
    /// Returns `true` if the game hop is [`Reduction`].
    ///
    /// [`Reduction`]: GameHop::Reduction
    #[must_use]
    pub fn is_reduction(&self) -> bool {
        matches!(self, Self::Reduction(..))
    }

    /// Returns `true` if the game hop is [`Equivalence`].
    ///
    /// [`Equivalence`]: GameHop::Equivalence
    #[must_use]
    pub fn is_equivalence(&self) -> bool {
        matches!(self, Self::Equivalence(..))
    }

    pub fn as_reduction(&self) -> Option<&Reduction<'a>> {
        if let Self::Reduction(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn as_equivalence(&self) -> Option<&Equivalence> {
        if let Self::Equivalence(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn left_game_instance_name(&self) -> &str {
        match self {
            GameHop::Conjecture(conjecture) => conjecture.left_name().as_str(),
            GameHop::Reduction(reduction) => {
                reduction.left().construction_game_instance_name().as_str()
            }
            GameHop::Equivalence(equivalence) => equivalence.left_name(),
            GameHop::Hybrid(hybrid) => hybrid.hybrid_name().as_str(),
        }
    }

    pub fn right_game_instance_name(&self) -> &str {
        match self {
            GameHop::Conjecture(conjecture) => conjecture.right_name().as_str(),
            GameHop::Reduction(reduction) => {
                reduction.right().construction_game_instance_name().as_str()
            }
            GameHop::Equivalence(equivalence) => equivalence.right_name(),
            GameHop::Hybrid(hybrid) => hybrid.hybrid_name().as_str(),
        }
    }
}

impl<'a> fmt::Display for GameHop<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            GameHop::Conjecture(conj) => {
                let left_name = conj.left_name().as_str();
                let right_name = conj.right_name().as_str();
                write!(f, "{left_name} == {right_name}")?;
                Ok(())
            }
            GameHop::Equivalence(eq) => {
                let left_name = eq.left_name();
                let right_name = eq.right_name();
                write!(f, "{left_name} == {right_name}")?;
                Ok(())
            }
            GameHop::Reduction(red) => {
                let left_name = red.left().construction_game_instance_name().as_str();
                let right_name = red.right().construction_game_instance_name().as_str();
                let assumption = red.assumption_name();
                write!(f, "{left_name} ~= {right_name} ({assumption})")?;
                Ok(())
            }
            GameHop::Hybrid(hybrid) => {
                // let hybrid_name = hybrid.hybrid_name().as_str();
                // write!(f, "hybrid: {hybrid_name}")?;
                let left_name = hybrid.equivalence().left_name();
                let right_name = hybrid.equivalence().right_name();
                write!(f, "{left_name} == {right_name}")?;
                Ok(())
            }
        }
    }
}
