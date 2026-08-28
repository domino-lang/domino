// SPDX-License-Identifier: MIT OR Apache-2.0

use std::collections::HashSet;

use miette::Diagnostic;
use thiserror::Error;

use crate::{theorem::GameInstance, types::Type};

use super::{
    deconstructinvoke, loopunroll,
    resolveoracles::{self, ResolutionError},
    returnify, sample_max_counter_extractor, samplify, tableinitialize, treeify, type_extract,
    unwrapify, GameTransform, Transformation,
};

pub struct EquivalenceTransform;

/// A failure raised while running the equivalence transform pipeline over a
/// game instance.
#[derive(Debug, Error, Diagnostic)]
pub enum EquivalenceTransformError {
    /// A sampling position is reachable through a loop `loopunroll` could not
    /// unroll. This is the only pipeline failure a parser-accepted project can
    /// still trigger; everything else the pipeline could hit is ruled out by
    /// an earlier stage and panics via `unreachable!`.
    #[error(transparent)]
    #[diagnostic(transparent)]
    UnboundedLoop(#[from] sample_max_counter_extractor::UnboundedLoopError),
}

// Bundles the per-game-instance data produced by the transform pipeline
#[derive(Clone, Debug)]
pub struct GameInstAux {
    pub types: HashSet<Type>,
    pub sample_info: samplify::SampleInfo,
    pub max_offsets: sample_max_counter_extractor::MaxOffsets,
}

impl super::TheoremTransform for EquivalenceTransform {
    type Err = EquivalenceTransformError;

    type Aux = Vec<(String, GameInstAux)>;

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
) -> Result<(GameInstance, (String, GameInstAux)), EquivalenceTransformError> {
    let comp = game_inst.game();

    let (comp, types) = type_extract::Transformation(comp)
        .transform()
        .expect("type extraction transformation failed unexpectedly");
    /*
     * Note 1: we currently do samplify and sample_max_counter_extractor before
     * treeify so a `if foo { stuff } else { other stuff } ... x <- Integer`
     * gets the same sample counter for the x sampling after returnify (instead
     * of different ones depending on which branch was taken)
     * Note 2: samplify only compiles sampling points and assigns identifiers
     * to them. The maximum possible counter/offset each sampling point can
     * be sampled from is computed afterwards by `sample_max_counter_extractor`,
     * which needs to run after loop unrolling (so samples inside bounded
     * loops are counted once per unrolled iteration) and after oracle
     * resolution (to follow resolved oracle invocations). samplify itself
     * has to stay before loop unrolling because it is also used by the latex
     * export, which must not unroll loops.
     */
    let (comp, _) = deconstructinvoke::Transformation(&comp)
        .transform()
        .expect("splitinvoke failed unexpectedly");
    let (comp, _) = unwrapify::Transformation(&comp)
        .transform()
        .expect("unwrapify transformation failed unexpectedly");
    let (comp, _) = resolveoracles::Transformation(&comp)
        .transform()
        .unwrap_or_else(|ResolutionError(failed_oracle_stmts)| {
            // The game parser rejects imported-but-unwired oracles
            // (`missing_edge`) and invocations of unknown oracles
            // (`no_such_oracle`), so resolution cannot fail on a parsed game.
            unreachable!("resolveoracles should have caught this: {failed_oracle_stmts:?}")
        });
    let (comp, sample_info) = samplify::Transformation(&comp)
        .transform()
        .expect("samplify transformation failed unexpectedly");
    let (comp, _) = loopunroll::Transformation(&comp)
        .transform()
        .expect("unroll transformation failed unexpectedly");
    let (comp, max_offsets) =
        sample_max_counter_extractor::Transformation(&comp, &sample_info.positions).transform()?;
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
        (
            game_inst.name().to_string(),
            GameInstAux {
                types,
                sample_info,
                max_offsets,
            },
        ),
    ))
}
