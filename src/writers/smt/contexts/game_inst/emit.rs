// SPDX-License-Identifier: MIT OR Apache-2.0

use std::collections::HashSet;

use itertools::Itertools;

use crate::{
    transforms::samplify::SampleInfo,
    writers::smt::{
        contexts::GameInstanceContext,
        exprs::SmtExpr,
        patterns::{DatastructurePattern, GameStateSelector},
    },
};

impl<'a> GameInstanceContext<'a> {
    pub(crate) fn smt_access_gamestate_pkgstate<S: Into<SmtExpr>>(
        &self,
        state: S,
        pkg_inst_name: &str,
    ) -> Option<SmtExpr> {
        let pkg_ctx = self.pkg_inst_ctx_by_name(pkg_inst_name)?;

        let declare_info = self.game_state_declare_info();
        let spec = self
            .datastructure_game_state_pattern()
            .datastructure_spec(&declare_info);
        let selector = GameStateSelector::PackageInstance {
            pkg_inst_name,
            sort: pkg_ctx.pkg_state_pattern().sort(vec![]),
        };

        self.datastructure_game_state_pattern()
            .access(&spec, &selector, state)
    }

    pub(crate) fn smt_access_gamestate_rand<S: Into<SmtExpr>>(
        &self,
        state: S,
        sample_id: usize,
    ) -> Option<SmtExpr> {
        let declare_info = self.game_state_declare_info();
        let spec = self
            .datastructure_game_state_pattern()
            .datastructure_spec(&declare_info);
        let selector = GameStateSelector::Randomness {
            sample_pos: Box::new(self.sample_info.positions[sample_id].clone()),
        };

        self.datastructure_game_state_pattern()
            .access(&spec, &selector, state)
    }

    pub(crate) fn smt_update_gamestate_pkgstate<S, V>(
        &self,
        gamestate: S,
        target_name: &str,
        new_pkgstate: V,
    ) -> Option<SmtExpr>
    where
        S: Clone + Into<SmtExpr>,
        V: Clone + Into<SmtExpr>,
    {
        let pkg_ctx = self.pkg_inst_ctx_by_name(target_name).unwrap();

        let declare_info = self.game_state_declare_info();
        let spec = self
            .datastructure_game_state_pattern()
            .datastructure_spec(&declare_info);
        let pkgstate_selector = GameStateSelector::PackageInstance {
            pkg_inst_name: target_name,
            sort: pkg_ctx.pkg_state_pattern().sort(vec![]),
        };

        self.datastructure_game_state_pattern().update(
            &spec,
            &pkgstate_selector,
            gamestate,
            new_pkgstate,
        )
    }

    pub(crate) fn smt_update_gamestate_rand<S, V>(
        &self,
        state: S,
        sample_info: &SampleInfo,
        sample_id: usize,
        new_value: V,
    ) -> Option<SmtExpr>
    where
        S: Clone + Into<SmtExpr>,
        V: Clone + Into<SmtExpr>,
    {
        let declare_info = self.game_state_declare_info();
        let spec = self
            .datastructure_game_state_pattern()
            .datastructure_spec(&declare_info);
        let selector = GameStateSelector::Randomness {
            sample_pos: Box::new(sample_info.positions[sample_id].clone()),
        };

        self.datastructure_game_state_pattern()
            .update(&spec, &selector, state, new_value)
    }

    pub(crate) fn smt_increment_gamestate_rand<S>(
        &self,
        state: S,
        sample_info: &SampleInfo,
        target_sample_id: usize,
    ) -> Option<SmtExpr>
    where
        S: Clone + Into<SmtExpr>,
    {
        let old_value = self.smt_access_gamestate_rand(state.clone(), target_sample_id)?;
        let new_value = ("+", 1, old_value);
        self.smt_update_gamestate_rand(state, sample_info, target_sample_id, new_value)
    }

    pub(crate) fn smt_composition_randomness(&mut self) -> impl Iterator<Item = SmtExpr> {
        let game_inst = self.game_inst();

        // ensure the sorts are unique so they all just exist once
        let smt_sorts: HashSet<SmtExpr> = self
            .sample_info
            .tys
            .iter()
            .map(|ty| ty.clone().into())
            .collect();

        // turn them to function declarations
        smt_sorts
            .into_iter()
            .map(|smt_sort| {
                (
                    "declare-fun",
                    format!(
                        "__sample-rand-{game_inst_name}-{smt_sort}",
                        game_inst_name = game_inst.name
                    ),
                    (
                        SmtExpr::Atom("SampleId".into()),
                        SmtExpr::Atom("Int".into()),
                    ),
                    smt_sort,
                )
                    .into()
            })
            .sorted()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::fmt::Write;
    use std::string::FromUtf8Error;
    use thiserror::Error;

    use crate::{expressions::Expression, writers::smt::exprs::SmtLet};

    #[derive(Error, Debug)]
    enum TestError {
        #[error("Error parsing the utf8: {0}")]
        Utf8DecodeError(#[from] FromUtf8Error),
        #[error("Error Writing: {0}")]
        WriteError(#[from] std::io::Error),
    }

    type TestResult = std::result::Result<(), TestError>;

    #[test]
    fn test_smtlet() -> TestResult {
        let l = SmtLet {
            bindings: vec![("x".into(), (&Expression::integer(42)).into())],
            body: SmtExpr::Atom(String::from("x")),
        };

        let out: SmtExpr = l.into();
        let mut str = String::new();

        write!(&mut str, "{out}").unwrap();

        assert_eq!(str, "(let ((x 42))\n     x)\n");

        Ok(())
    }
}
