// SPDX-License-Identifier: MIT OR Apache-2.0

//! Computes, for every exported oracle, the maximum (over-approximated)
//! counter/offset each sampling position reachable from that export can be
//! sampled at.
//!
//! This is the former second stage of `samplify`. It has been split out
//! because it needs to run after `loopunroll`, so that a sample inside a
//! bounded loop is counted once per unrolled iteration: loop bodies keep the
//! `sample_id` assigned by `samplify` when they get unrolled, so several
//! statements can share the same id by the time this transform sees them.
//! `samplify` itself has to keep running before loop unrolling, since it is
//! also used by the latex export, which must not unroll loops. It must also
//! run after `resolveoracles`, so oracle invocations carry a resolved `edge`
//! to follow, and before `treeify`, which discards the sequential structure
//! this traversal relies on.
//!
//! Given that ordering, most of the ways this traversal could go wrong are
//! already ruled out by an earlier stage and show up here as `unreachable!`:
//!
//! * a `sample_id` of `None` — `samplify` assigns one to every sample;
//! * an unresolved oracle invocation — `resolveoracles` fails the whole
//!   pipeline before we get here if it cannot resolve one;
//! * an oracle named by an edge/export that the destination package does not
//!   define — the parser validates every edge and export signature against
//!   the destination package's oracle list;
//! * a loop with literal integer bounds — `loopunroll` unrolls exactly those.
//!
//! The one failure a well-formed project can actually trigger is a sampling
//! position reachable through a loop whose bounds are *not* literal integers:
//! `loopunroll` leaves it in place and we have no static bound on how often
//! the position runs. That is reported as [`UnboundedLoopError`].

use std::collections::HashMap;

use miette::{Diagnostic, NamedSource, SourceSpan};
use thiserror::Error;

use crate::expressions::ExpressionKind;
use crate::package::{Composition, Export, PackageInstance};
use crate::statement::{Assignment, AssignmentRhs, CodeBlock, Statement};

use super::samplify::Position;

pub struct Transformation<'a>(pub &'a Composition, pub &'a [Position]);

pub type MaxOffsets = HashMap<Export, HashMap<Position, usize>>;

/// A sampling position is reachable through a loop whose bounds are not
/// literal integers, so `loopunroll` could not unroll it and we cannot bound
/// how many times the position is sampled.
#[derive(Debug, Error, Diagnostic)]
#[error(
    "cannot bound the sample counter: oracle `{oracle_name}` samples inside a \
     loop that `loopunroll` could not unroll"
)]
#[diagnostic(
    code(domino::sample_max_counter::unbounded_loop),
    help(
        "randomness mapping needs a static bound on how often each sampling \
         position runs. Give this loop literal integer bounds, or move the \
         sampling out of the loop."
    )
)]
pub struct UnboundedLoopError {
    #[source_code]
    src: NamedSource<String>,

    #[label("this loop has non-literal bounds but a sample is reachable through it")]
    at: SourceSpan,

    oracle_name: String,
}

impl super::Transformation for Transformation<'_> {
    type Err = UnboundedLoopError;
    type Aux = MaxOffsets;

    fn transform(&self) -> Result<(Composition, MaxOffsets), UnboundedLoopError> {
        let extractor = MaxOffsetExtractor { pkgs: &self.0.pkgs };
        let max_offset = extractor.composition_offsets(&self.0.exports, self.1)?;

        Ok((self.0.clone(), max_offset))
    }
}

type OffsetMap = HashMap<usize, usize>;

fn add_offsets(target: &mut OffsetMap, source: &OffsetMap) {
    for (pos, offset) in source {
        *target.entry(*pos).or_insert(0) += offset;
    }
}

// Takes union of the given maps and for elements that exist in both maps
// compute the maximum offset.
fn max_offsets(left: &OffsetMap, right: &OffsetMap) -> OffsetMap {
    let mut result = left.to_owned();

    for (pos, offset) in right {
        result
            .entry(*pos)
            .and_modify(|existing| *existing = (*existing).max(*offset))
            .or_insert(*offset);
    }

    result
}

/// Walks the control flow reachable from each export, following resolved
/// oracle invocations across package instances, and records for every
/// `sample_id` the largest number of times it can be reached.
///
/// `statement_offsets` and `codeblock_offsets` are mutually recursive and all
/// three traversal methods need the game's package instances, so the `pkgs`
/// slice lives on `self` instead of being threaded through every call.
struct MaxOffsetExtractor<'a> {
    pkgs: &'a [PackageInstance],
}

/// Where in the source the traversal currently is. Carried only so that a
/// loop with non-literal bounds can point at itself in [`UnboundedLoopError`].
#[derive(Clone, Copy)]
struct Location<'a> {
    pkg: &'a PackageInstance,
    oracle_name: &'a str,
}

impl<'a> MaxOffsetExtractor<'a> {
    /// Converts the sample-id-indexed offsets computed per export into a map
    /// keyed directly by sampling `Position`, so callers don't need to thread
    /// `samplify`'s `positions` vector through just to resolve the index.
    fn composition_offsets(
        &self,
        exports: &[Export],
        positions: &[Position],
    ) -> Result<MaxOffsets, UnboundedLoopError> {
        exports
            .iter()
            .map(|export| {
                let offsets = self.oracle_offsets(export.to(), &export.sig().name)?;
                let by_position = offsets
                    .into_iter()
                    .map(|(sample_id, max_offset)| (positions[sample_id].clone(), max_offset))
                    .collect();
                Ok((export.clone(), by_position))
            })
            .collect()
    }

    /// Offsets accumulated over the body of `oracle_name` in package instance
    /// `pkg_idx`.
    ///
    /// The parser resolves every edge and export signature against the
    /// destination package's oracle list, and `resolveoracles` fails the
    /// pipeline if it cannot resolve an invocation, so the lookup below always
    /// finds a match by the time this transform runs.
    fn oracle_offsets(
        &self,
        pkg_idx: usize,
        oracle_name: &str,
    ) -> Result<OffsetMap, UnboundedLoopError> {
        let pkg = &self.pkgs[pkg_idx];
        let oracle = pkg
            .pkg
            .oracles
            .iter()
            .find(|oracle| oracle.sig.name == oracle_name)
            .unwrap_or_else(|| {
                unreachable!(
                    "edge/export resolution guarantees oracle `{oracle_name}` \
                     exists in package instance `{}`",
                    pkg.name
                )
            });

        self.codeblock_offsets(
            &oracle.code,
            Location {
                pkg,
                oracle_name: &oracle.sig.name,
            },
        )
    }

    fn codeblock_offsets(
        &self,
        code: &CodeBlock,
        loc: Location<'a>,
    ) -> Result<OffsetMap, UnboundedLoopError> {
        let mut result = OffsetMap::new();

        for stmt in &code.0 {
            add_offsets(&mut result, &self.statement_offsets(stmt, loc)?);
        }

        Ok(result)
    }

    fn statement_offsets(
        &self,
        stmt: &Statement,
        loc: Location<'a>,
    ) -> Result<OffsetMap, UnboundedLoopError> {
        Ok(match stmt {
            Statement::Assignment(
                Assignment {
                    rhs:
                        AssignmentRhs::Sample {
                            sample_id: Some(sample_id),
                            ..
                        },
                    ..
                },
                _,
            ) => OffsetMap::from([(*sample_id, 1)]),
            Statement::Assignment(
                Assignment {
                    rhs:
                        AssignmentRhs::Sample {
                            sample_id: None, ..
                        },
                    ..
                },
                _,
            ) => {
                unreachable!("samplify should have assigned a sample_id to every sample statement")
            }
            Statement::Assignment(
                Assignment {
                    rhs:
                        AssignmentRhs::Invoke {
                            oracle_name, edge, ..
                        },
                    ..
                },
                _,
            ) => {
                let edge = edge.as_ref().unwrap_or_else(|| {
                    unreachable!(
                        "resolveoracles should have resolved (or failed the pipeline on) the \
                         invocation of `{oracle_name}` before this transform runs"
                    )
                });
                self.oracle_offsets(edge.to(), &edge.sig().name)?
            }
            Statement::InvokeOracle(invoke) => {
                let edge = invoke.edge.as_ref().unwrap_or_else(|| {
                    unreachable!(
                        "resolveoracles should have resolved (or failed the pipeline on) the \
                         invocation of `{}` before this transform runs",
                        invoke.oracle_name
                    )
                });
                self.oracle_offsets(edge.to(), &edge.sig().name)?
            }
            Statement::IfThenElse(ite) if ite.else_block.0.is_empty() => {
                self.codeblock_offsets(&ite.then_block, loc)?
            }
            Statement::IfThenElse(ite) => max_offsets(
                &self.codeblock_offsets(&ite.then_block, loc)?,
                &self.codeblock_offsets(&ite.else_block, loc)?,
            ),
            Statement::For(_, lower, upper, _, span) => {
                if !matches!(
                    (lower.kind(), upper.kind()),
                    (
                        ExpressionKind::IntegerLiteral(_),
                        ExpressionKind::IntegerLiteral(_)
                    )
                ) {
                    return Err(UnboundedLoopError {
                        src: NamedSource::new(
                            loc.pkg.pkg.file_name.clone(),
                            loc.pkg.pkg.file_contents.clone(),
                        ),
                        at: *span,
                        oracle_name: loc.oracle_name.to_string(),
                    });
                }

                unreachable!(
                    "loopunroll should have unrolled this loop with literal integer bounds \
                     before this transform runs"
                )
            }
            Statement::Abort(_) | Statement::Return(_, _) | Statement::Assignment(_, _) => {
                OffsetMap::new()
            }
        })
    }
}

#[cfg(test)]
mod test {
    use std::collections::HashMap;

    use crate::{
        package::Composition,
        parser::tests::{games, packages},
        transforms::{loopunroll, resolveoracles, samplify, Transformation as _},
    };

    // Parses the given single-package game and runs the pipeline prefix shared
    // by the tests below: `resolveoracles -> samplify`. Loop
    // unrolling is left to the caller so that the tests exercising the
    // "loopunroll should have unrolled ..." path can skip it.
    fn resolve_and_samplify(
        pkg_name: &str,
        pkg_code: &str,
        game_name: &str,
        game_code: &str,
    ) -> (Composition, Vec<samplify::Position>) {
        let (parsed_name, pkg) = packages::parse(pkg_code, &format!("{pkg_name}.pkg.ssp"));
        let pkg_map = HashMap::from([(parsed_name, pkg)]);
        let comp = games::parse(game_code, &format!("{game_name}.comp.ssp"), &pkg_map);

        let (comp, _) = resolveoracles::Transformation(&comp).transform().unwrap();
        let (comp, sample_info) = samplify::Transformation(&comp).transform().unwrap();

        (comp, sample_info.positions)
    }

    #[test]
    fn counts_one_sample_per_unrolled_loop_iteration() {
        let pkg_code = r#"package SumSampler {
    params {
        n: Integer,
    }

    state {
        T: Table(Integer, Bits(n)),
    }

    oracle Fill() {
        for i: 0 <= i < 3 {
            r <-$ Bits(n);
            T[i] <- Some(r);
        }
    }
}
"#;
        let game_code = r#"composition SumSamplerGame {
    const n: Integer;

    instance pkg = SumSampler {
        params {
            n: n,
        }
    }

    compose {
        adversary: {
            Fill: pkg,
        }
    }
}
"#;
        let (comp, positions) =
            resolve_and_samplify("SumSampler", pkg_code, "SumSamplerGame", game_code);
        let (comp, _) = loopunroll::Transformation(&comp).transform().unwrap();

        // Before this transform moved out of samplify and started running
        // after loopunroll, this would have panicked here on the (still
        // present) `for` loop.
        let (_, max_offsets) = super::Transformation(&comp, &positions)
            .transform()
            .unwrap();

        let export = comp.exports.iter().find(|e| e.name() == "Fill").unwrap();
        let offsets = max_offsets.get(export).unwrap();

        assert_eq!(offsets.len(), 1);
        assert_eq!(*offsets.values().next().unwrap(), 3);
    }

    #[test]
    fn errors_on_sample_inside_loop_with_non_literal_bounds() {
        let pkg_code = r#"package UnboundedSampler {
    oracle Loopy(n: Integer) -> Bits(256) {
        r <-$ Bits(256);
        for i: 0 <= i < n {
            r <-$ Bits(256);
        }
        return r;
    }
}
"#;
        let game_code = r#"composition UnboundedGame {
    instance pkg = UnboundedSampler {}

    compose {
        adversary: {
            Loopy: pkg,
        }
    }
}
"#;
        let (comp, positions) =
            resolve_and_samplify("UnboundedSampler", pkg_code, "UnboundedGame", game_code);
        // loopunroll runs but cannot unroll `0 <= i < n`, so the `for` reaches
        // this transform.
        let (comp, _) = loopunroll::Transformation(&comp).transform().unwrap();

        let err = super::Transformation(&comp, &positions)
            .transform()
            .unwrap_err();

        assert_eq!(err.oracle_name, "Loopy");
        assert!(
            miette::Diagnostic::help(&err)
                .unwrap()
                .to_string()
                .contains("literal integer bounds"),
            "expected the diagnostic to suggest literal bounds",
        );
    }

    #[test]
    #[should_panic(
        expected = "loopunroll should have unrolled this loop with literal integer bounds"
    )]
    fn panics_when_a_bounded_loop_was_not_unrolled() {
        let pkg_code = r#"package BoundedSampler {
    oracle Fill() {
        for i: 0 <= i < 3 {
            r <-$ Bits(256);
        }
    }
}
"#;
        let game_code = r#"composition BoundedGame {
    instance pkg = BoundedSampler {}

    compose {
        adversary: {
            Fill: pkg,
        }
    }
}
"#;
        // Deliberately skip loopunroll: a literal-bounds `for` reaching this
        // transform is a loopunroll bug, not a user error.
        let (comp, positions) =
            resolve_and_samplify("BoundedSampler", pkg_code, "BoundedGame", game_code);

        let _ = super::Transformation(&comp, &positions).transform();
    }

    #[test]
    #[should_panic(expected = "resolveoracles should have resolved")]
    fn panics_on_unresolved_oracle_invocation() {
        let pkg_code = r#"package Caller {
    import oracles {
        Inner(),
    }

    oracle Outer() {
        r <-$ Bits(256);
        invoke Inner();
    }

    oracle Inner() {
        s <-$ Bits(256);
    }
}
"#;
        let game_code = r#"composition CallerGame {
    instance pkg = Caller {}

    compose {
        adversary: {
            Outer: pkg,
        }
        pkg: {
            Inner: pkg,
        }
    }
}
"#;
        let (parsed_name, pkg) = packages::parse(pkg_code, "Caller.pkg.ssp");
        let pkg_map = HashMap::from([(parsed_name, pkg)]);
        let comp = games::parse(game_code, "CallerGame.comp.ssp", &pkg_map);

        // Deliberately skip resolveoracles: the `invoke Inner()` keeps
        // `edge: None`.
        let (comp, sample_info) = samplify::Transformation(&comp).transform().unwrap();

        let _ = super::Transformation(&comp, &sample_info.positions).transform();
    }

    #[test]
    #[should_panic(expected = "samplify should have assigned a sample_id")]
    fn panics_on_sample_without_id() {
        let pkg_code = r#"package RawSampler {
    oracle Draw() -> Bits(256) {
        r <-$ Bits(256);
        return r;
    }
}
"#;
        let game_code = r#"composition RawSamplerGame {
    instance pkg = RawSampler {}

    compose {
        adversary: {
            Draw: pkg,
        }
    }
}
"#;
        let (parsed_name, pkg) = packages::parse(pkg_code, "RawSampler.pkg.ssp");
        let pkg_map = HashMap::from([(parsed_name, pkg)]);
        let comp = games::parse(game_code, "RawSamplerGame.comp.ssp", &pkg_map);

        // Deliberately skip samplify: the sample statement keeps `sample_id: None`.
        let (comp, _) = resolveoracles::Transformation(&comp).transform().unwrap();

        let _ = super::Transformation(&comp, &[]).transform();
    }

    // Happy path exercising every guard at once: `samplify` assigns the ids,
    // `resolveoracles` resolves the cross-package `invoke`, the edge points at
    // an oracle that exists, and `loopunroll` unrolls the bounded loop. If any
    // of the four `unreachable!` arms were reachable through the normal
    // pipeline, this would panic instead of producing offsets.
    #[test]
    fn resolves_cross_package_invocation_through_an_unrolled_loop() {
        let inner_code = r#"package Inner {
    oracle Draw() -> Bits(256) {
        s <-$ Bits(256);
        return s;
    }
}
"#;
        let outer_code = r#"package Outer {
    import oracles {
        Draw() -> Bits(256),
    }

    oracle Run() {
        r <-$ Bits(256);
        for i: 0 <= i < 2 {
            r <-$ Bits(256);
            x <- invoke Draw();
        }
    }
}
"#;
        let game_code = r#"composition CrossGame {
    instance inner = Inner {}
    instance outer = Outer {}

    compose {
        adversary: {
            Run: outer,
        }
        outer: {
            Draw: inner,
        }
    }
}
"#;
        let (inner_name, inner) = packages::parse(inner_code, "Inner.pkg.ssp");
        let (outer_name, outer) = packages::parse(outer_code, "Outer.pkg.ssp");
        let pkg_map = HashMap::from([(inner_name, inner), (outer_name, outer)]);
        let comp = games::parse(game_code, "CrossGame.comp.ssp", &pkg_map);

        let (comp, _) = resolveoracles::Transformation(&comp).transform().unwrap();
        let (comp, sample_info) = samplify::Transformation(&comp).transform().unwrap();
        let (comp, _) = loopunroll::Transformation(&comp).transform().unwrap();

        let (_, max_offsets) = super::Transformation(&comp, &sample_info.positions)
            .transform()
            .unwrap();

        let export = comp.exports.iter().find(|e| e.name() == "Run").unwrap();
        let offsets = max_offsets.get(export).unwrap();

        // The pre-loop `r` sample runs once; the in-loop `r` sample and the
        // `s` sample inside `Draw` each run once per unrolled iteration.
        let mut counts: Vec<usize> = offsets.values().copied().collect();
        counts.sort_unstable();
        assert_eq!(counts, vec![1, 2, 2]);
    }
}
