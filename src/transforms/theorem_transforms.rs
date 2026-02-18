// SPDX-License-Identifier: MIT OR Apache-2.0

use std::{collections::HashSet, convert::Infallible};

use crate::{theorem::GameInstance, transforms::splitinvoke, types::Type};

use super::{
    resolveoracles::{self, ResolutionError},
    returnify, samplify, tableinitialize, treeify, type_extract, unwrapify, GameTransform,
    Transformation,
};

pub struct EquivalenceTransform;

impl super::TheoremTransform for EquivalenceTransform {
    type Err = Infallible;

    type Aux = Vec<(String, (HashSet<Type>, samplify::SampleInfo))>;

    fn transform_theorem<'a>(
        &self,
        theorem: &'a crate::theorem::Theorem<'a>,
    ) -> Result<(crate::theorem::Theorem<'a>, Self::Aux), Self::Err> {
        let results = theorem.instances.iter().map(transform_game_inst);
        let (instances, auxs) = itertools::process_results(results, |res| res.unzip())?;
        let theorem = theorem.with_new_instances(instances);

        Ok((theorem, auxs))
    }
}

fn transform_game_inst(
    game_inst: &GameInstance,
) -> Result<
    (
        GameInstance,
        (String, (HashSet<Type>, samplify::SampleInfo)),
    ),
    Infallible,
> {
    let comp = game_inst.game();

    let (comp, types) = type_extract::Transformation(comp)
        .transform()
        .expect("type extraction transformation failed unexpectedly");
    /*
     * Note: we currently do samplify early so a `if foo { stuff }
     * else { other stuff } ... x <- Integer` gets the same sample
     * counter for the x sampling after returnify (instead of
     * different ones depending on which branch was taken)
     */
    let (comp, _) = splitinvoke::Transformation(&comp)
        .transform()
        .expect("splitinvoke failed unexpectedly");
    let (comp, samplinginfo) = samplify::Transformation(&comp)
        .transform()
        .expect("samplify transformation failed unexpectedly");
    let (comp, _) = unwrapify::Transformation(&comp)
        .transform()
        .expect("unwrapify transformation failed unexpectedly");
    let (comp, _) = resolveoracles::Transformation(&comp)
        .transform()
        .unwrap_or_else(|ResolutionError(failed_oracle_stmts)| {
            panic!("error resolving oracles: {failed_oracle_stmts:?}")
        });
    let (comp, _) = returnify::TransformNg
        .transform_game(&comp)
        .expect("returnify transformation failed unexpectedly");
    let (comp, _) = treeify::Transformation(&comp)
        .transform()
        .expect("treeify transformation failed unexpectedly");
    let (comp, _) = tableinitialize::Transformation(&comp)
        .transform()
        .expect("tableinitialize transformation failed unexpectedly");

    Ok((
        game_inst.with_other_game(comp),
        (game_inst.name().to_string(), (types, samplinginfo)),
    ))
}
