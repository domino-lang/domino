// SPDX-License-Identifier: MIT OR Apache-2.0

use std::collections::{HashMap, HashSet};
use std::ops::Range;

use itertools::Itertools as _;
use pest::iterators::Pair;

use crate::{
    expressions::{Expression, ExpressionKind},
    gamehops::{
        reduction::{Assumption, Reduction},
        GameHop,
    },
    identifier::{
        game_ident::{GameConstIdentifier, GameIdentifier},
        theorem_ident::TheoremIdentifier,
        Identifier,
    },
    package::{Composition, Edge, OracleSig, PackageInstance},
    packageinstance::instantiate::InstantiationContext,
    parser::error::{
        AssumptionMappingLeftGameInstanceIsNotFromAssumption,
        AssumptionMappingRightGameInstanceIsFromAssumption, InvalidGameInstanceInReductionError,
    },
    theorem::GameInstance,
};

use super::{
    ast::{Identifier as _, *},
    error::{
        AssumptionAdversaryExportsNotSufficientError, AssumptionExportsNotSufficientError,
        AssumptionMappingContainsDifferentPackagesError,
        AssumptionMappingDuplicatePackageInstanceError,
        AssumptionMappingMissesPackageInstanceError, AssumptionMappingParameterMismatchError,
        AssumptionMappingUnmappedDestinationError, AssumptionMappingWiringMismatchError,
        ReductionContainsDifferentPackagesError, ReductionCyclicContextError,
        ReductionInconsistentAssumptionBoundaryError, ReductionInvalidHybridMappingError,
        ReductionMissingExportError, ReductionPackageInstanceParameterMismatchError,
        ReductionPackageParameterCountMismatchError, ReductionSameGameInstanceError,
        UndefinedAssumptionError, UndefinedGameInstanceError, UndefinedPackageInstanceError,
    },
    theorem::{ParseTheoremContext, ParseTheoremError},
    Rule,
};

pub(crate) fn handle_reduction<'a>(
    ctx: &mut ParseTheoremContext<'a>,
    ast: Pair<'a, Rule>,
) -> Result<GameHop<'a>, ParseTheoremError> {
    let mut ast = ast.into_inner();

    let (left_name_ast, right_name_ast, body_ast) = ast
        .next_tuple()
        .expect("reduction grammar requires two game names and a reduction_spec");
    let header_span = left_name_ast.as_span().start()..right_name_ast.as_span().end();

    let reduction = handle_reduction_body(
        ctx,
        left_name_ast.as_str(),
        right_name_ast.as_str(),
        header_span,
        body_ast,
        false,
    )?;
    Ok(GameHop::Reduction(reduction))
}

// Keep the first edge, as the previous linear lookup did, even when separate
// compose blocks assign the same import more than once.
fn index_edges(game: &Composition) -> HashMap<(usize, &str), usize> {
    let mut edges = HashMap::new();
    for edge in &game.edges {
        edges.entry((edge.from(), edge.name())).or_insert(edge.to());
    }
    edges
}

struct ReductionTraversal<'a> {
    left_edges: HashMap<(usize, &'a str), usize>,
    right_edges: HashMap<(usize, &'a str), usize>,
    visited: HashMap<(usize, usize), ComparisonState>,
    #[cfg(test)]
    visit_count: usize,
    #[cfg(test)]
    visit_budget: usize,
}

impl<'a> ReductionTraversal<'a> {
    fn new(left: &'a Composition, right: &'a Composition) -> Self {
        Self {
            left_edges: index_edges(left),
            right_edges: index_edges(right),
            visited: HashMap::new(),
            #[cfg(test)]
            visit_count: 0,
            #[cfg(test)]
            visit_budget: left.pkgs.len().saturating_mul(right.pkgs.len()),
        }
    }
}

enum ComparisonState {
    Active,
    Complete,
}

enum ComparisonFrame {
    Enter((usize, usize)),
    Leave((usize, usize)),
}

fn compare_reduction(
    ctx: &ParseTheoremContext,
    reduction_span: pest::Span,
    inst_offs_left: usize,
    inst_offs_right: usize,
    left_game_inst: &GameInstance,
    right_game_inst: &GameInstance,
    mapping_left: &ReductionMapping,
    mapping_right: &ReductionMapping,
    traversal: &mut ReductionTraversal,
) -> Result<(), ParseTheoremError> {
    let game_left = left_game_inst.game();
    let game_right = right_game_inst.game();
    let mut stack = vec![ComparisonFrame::Enter((inst_offs_left, inst_offs_right))];
    while let Some(frame) = stack.pop() {
        let (inst_offs_left, inst_offs_right) = match frame {
            ComparisonFrame::Leave(pair) => {
                traversal.visited.insert(pair, ComparisonState::Complete);
                continue;
            }
            ComparisonFrame::Enter(pair) => pair,
        };
        let left_pkg_inst = &game_left.pkgs[inst_offs_left];
        let right_pkg_inst = &game_right.pkgs[inst_offs_right];
        let pair = (inst_offs_left, inst_offs_right);
        match traversal.visited.get(&pair) {
            Some(ComparisonState::Complete) => continue,
            Some(ComparisonState::Active) => {
                return Err(ReductionCyclicContextError {
                    source_code: ctx.named_source(),
                    at: (reduction_span.start()..reduction_span.end()).into(),
                    left_game_inst_name: left_game_inst.name().to_string(),
                    right_game_inst_name: right_game_inst.name().to_string(),
                    left_pkg_inst_name: left_pkg_inst.name().to_string(),
                    right_pkg_inst_name: right_pkg_inst.name().to_string(),
                }
                .into());
            }
            None => {
                traversal.visited.insert(pair, ComparisonState::Active);
            }
        }
        #[cfg(test)]
        {
            traversal.visit_count += 1;
            assert!(
                traversal.visit_count <= traversal.visit_budget,
                "context comparison exceeded its visit budget"
            );
        }

        if check_assumption_boundary(
            ctx,
            reduction_span,
            left_pkg_inst,
            right_pkg_inst,
            game_left,
            game_right,
            mapping_left,
            mapping_right,
        )? {
            traversal.visited.insert(pair, ComparisonState::Complete);
            continue;
        }
        check_context_package_equality(
            ctx,
            reduction_span,
            left_pkg_inst,
            left_game_inst,
            right_pkg_inst,
            right_game_inst,
        )?;

        // The stack is LIFO: push children in reverse declaration order so the
        // first declared import and all its descendants are checked first.
        stack.push(ComparisonFrame::Leave(pair));
        for (sig, _) in left_pkg_inst
            .pkg
            .imports
            .iter()
            .sorted_by_key(|(_, span)| span.offset())
            .rev()
        {
            let left_destination = *traversal
                .left_edges
                .get(&(inst_offs_left, sig.name.as_str()))
                .expect("composition validation supplies an edge for every left package import");

            let right_destination = *traversal
                .right_edges
                .get(&(inst_offs_right, sig.name.as_str()))
                .expect("composition validation supplies an edge for every right package import");

            stack.push(ComparisonFrame::Enter((
                left_destination,
                right_destination,
            )));
        }
    }
    Ok(())
}

fn check_assumption_boundary(
    ctx: &ParseTheoremContext,
    reduction_span: pest::Span,
    left_pkg_inst: &PackageInstance,
    right_pkg_inst: &PackageInstance,
    game_left: &Composition,
    game_right: &Composition,
    mapping_left: &ReductionMapping,
    mapping_right: &ReductionMapping,
) -> Result<bool, ParseTheoremError> {
    let left_mapping_entry = mapping_left
        .entries
        .iter()
        .find(|mapping_entry| mapping_entry.construction().as_str() == left_pkg_inst.name());

    let right_mapping_entry = mapping_right
        .entries
        .iter()
        .find(|mapping_entry| mapping_entry.construction().as_str() == right_pkg_inst.name());

    let (entry, game_1, pkg_1, game_2, pkg_2) = match (left_mapping_entry, right_mapping_entry) {
        (Some(_), Some(_)) => return Ok(true),
        (None, None) => return Ok(false),
        (Some(entry), None) => (entry, game_left, left_pkg_inst, game_right, right_pkg_inst),
        (None, Some(entry)) => (entry, game_right, right_pkg_inst, game_left, left_pkg_inst),
    };
    let span = entry.construction().as_span();
    Err(ReductionInconsistentAssumptionBoundaryError {
        source_code: ctx.named_source(),
        at_reduction: (reduction_span.start()..reduction_span.end()).into(),
        at_mapping_entry: (span.start()..span.end()).into(),
        game_name_1: game_1.name().to_string(),
        game_name_2: game_2.name().to_string(),
        pkg_inst_name_1: pkg_1.name().to_string(),
        pkg_inst_name_2: pkg_2.name().to_string(),
    }
    .into())
}

fn check_context_package_equality(
    ctx: &ParseTheoremContext,
    reduction_span: pest::Span,
    left_pkg_inst: &PackageInstance,
    left_game_inst: &GameInstance,
    right_pkg_inst: &PackageInstance,
    right_game_inst: &GameInstance,
) -> Result<(), ParseTheoremError> {
    let diff = package_instances_diff(
        ctx,
        reduction_span,
        left_pkg_inst,
        left_game_inst,
        right_pkg_inst,
        right_game_inst,
    )?;

    match diff {
        PackageInstanceDiff::DifferentPackage(left_pkg_name, right_pkg_name) => {
            return Err(ReductionContainsDifferentPackagesError {
                source_code: ctx.named_source(),
                at_reduction: (reduction_span.start()..reduction_span.end()).into(),
                left_pkg_inst_name: left_pkg_inst.name().to_string(),
                right_pkg_inst_name: right_pkg_inst.name().to_string(),

                left_pkg_name,
                right_pkg_name,
            }
            .into());
        }
        PackageInstanceDiff::DifferentParams(param_diff) => {
            return Err(ReductionPackageInstanceParameterMismatchError {
                source_code: ctx.named_source(),
                at_reduction: (reduction_span.start()..reduction_span.end()).into(),
                left_pkg_inst_name: left_pkg_inst.name().to_string(),
                right_pkg_inst_name: right_pkg_inst.name().to_string(),

                param_names: param_diff.join(", "),
            }
            .into());
        }
        PackageInstanceDiff::Same => {}
    }

    Ok(())
}

pub(super) fn handle_reduction_body<'a>(
    ctx: &mut ParseTheoremContext,
    left_name: &str,
    right_name: &str,
    header_span: Range<usize>,
    body: Pair<'a, Rule>,
    is_hybrid: bool,
) -> Result<Reduction<'a>, ParseTheoremError> {
    debug_assert_eq!(body.as_rule(), Rule::reduction_spec);

    let reduction_span = body.as_span();
    let mut ast = body.into_inner();
    let (assumptions_spec_ast, map1_ast, map2_ast) = ast
        .next_tuple()
        .expect("reduction_spec grammar requires an assumption_spec and two map_spec blocks");
    let assumptions_name_ast = assumptions_spec_ast
        .into_inner()
        .next()
        .expect("assumption_spec grammar requires an assumption name");
    let assumptions_name_span = assumptions_name_ast.as_span();
    let assumption_name = assumptions_name_ast.as_str();

    let assumption = resolve_assumption(ctx, assumption_name, assumptions_name_span)?;

    let (mapping1, parsed_name1) = handle_mapspec_assumption(ctx, map1_ast, assumption, is_hybrid)?;
    let (mapping2, parsed_name2) = handle_mapspec_assumption(ctx, map2_ast, assumption, is_hybrid)?;
    let (mapping_left, mapping_right) = align_reduction_mappings(
        ctx,
        left_name,
        right_name,
        header_span,
        mapping1,
        &parsed_name1,
        mapping2,
        &parsed_name2,
    )?;
    compare_reduction_context(
        ctx,
        reduction_span,
        left_name,
        right_name,
        &mapping_left,
        &mapping_right,
    )?;
    check_distinct_mapped_games(ctx, reduction_span, &mapping_left, &mapping_right)?;

    let reduction = Reduction::new(mapping_left, mapping_right, assumption_name.to_string());

    Ok(reduction)
}

fn resolve_assumption<'ctx>(
    ctx: &'ctx ParseTheoremContext,
    assumption_name: &str,
    assumptions_name_span: pest::Span,
) -> Result<&'ctx Assumption, ParseTheoremError> {
    ctx.assumptions
        .iter()
        .find(|assumption| assumption.name == assumption_name)
        .ok_or_else(|| UndefinedAssumptionError {
            source_code: ctx.named_source(),
            at: (assumptions_name_span.start()..assumptions_name_span.end()).into(),
            assumption_name: assumption_name.to_string(),
        })
        .map_err(Into::into)
}

fn align_reduction_mappings<'a>(
    ctx: &ParseTheoremContext,
    left_name: &str,
    right_name: &str,
    header_span: Range<usize>,
    mapping1: ReductionMapping<'a>,
    parsed_name1: &str,
    mapping2: ReductionMapping<'a>,
    parsed_name2: &str,
) -> Result<(ReductionMapping<'a>, ReductionMapping<'a>), ParseTheoremError> {
    let (left, right) = if parsed_name1 != right_name {
        ((mapping1, parsed_name1), (mapping2, parsed_name2))
    } else {
        ((mapping2, parsed_name2), (mapping1, parsed_name1))
    };
    for ((mapping, parsed_name), expected_name) in [(&left, left_name), (&right, right_name)] {
        if *parsed_name != expected_name {
            return Err(InvalidGameInstanceInReductionError::new(
                ctx.named_source(),
                mapping.construction_game_instance_name(),
                header_span,
            )
            .into());
        }
    }
    Ok((left.0, right.0))
}

fn compare_reduction_context(
    ctx: &ParseTheoremContext,
    reduction_span: pest::Span,
    left_name: &str,
    right_name: &str,
    mapping_left: &ReductionMapping,
    mapping_right: &ReductionMapping,
) -> Result<(), ParseTheoremError> {
    let left_game_inst = ctx
        .game_instance(left_name)
        .expect("validated construction mappings resolve both reduction header game names")
        .1;
    let right_game_inst = ctx
        .game_instance(right_name)
        .expect("validated construction mappings resolve both reduction header game names")
        .1;

    let left_exports = &left_game_inst.game().exports;
    let mut traversal = ReductionTraversal::new(left_game_inst.game(), right_game_inst.game());

    for left_export in left_exports {
        let right_export = right_game_inst
            .game()
            .exports
            .iter()
            .find(|right_export| left_export.name() == right_export.name())
            .ok_or_else(|| ReductionMissingExportError {
                source_code: ctx.named_source(),
                at: (reduction_span.start()..reduction_span.end()).into(),
                game_inst_name: right_game_inst.name().to_string(),
                oracle_name: left_export.name().to_string(),
            })?;

        compare_reduction(
            ctx,
            reduction_span,
            left_export.to(),
            right_export.to(),
            left_game_inst,
            right_game_inst,
            mapping_left,
            mapping_right,
            &mut traversal,
        )?;
    }
    Ok(())
}

fn check_distinct_mapped_games(
    ctx: &ParseTheoremContext,
    reduction_span: pest::Span,
    mapping_left: &ReductionMapping,
    mapping_right: &ReductionMapping,
) -> Result<(), ParseTheoremError> {
    // Assumption identity has priority when both roles repeat.
    for (role, left, right) in [
        (
            "assumption",
            mapping_left.assumption_game_instance_name(),
            mapping_right.assumption_game_instance_name(),
        ),
        (
            "construction",
            mapping_left.construction_game_instance_name(),
            mapping_right.construction_game_instance_name(),
        ),
    ] {
        if left.as_str() == right.as_str() {
            return Err(ReductionSameGameInstanceError {
                source_code: ctx.named_source(),
                at: (reduction_span.start()..reduction_span.end()).into(),
                role: role.to_string(),
                name: left.as_str().to_string(),
            }
            .into());
        }
    }
    Ok(())
}

fn handle_mapspec_assumption<'a>(
    ctx: &ParseTheoremContext,
    ast: Pair<'a, Rule>,
    assumption: &Assumption,
    is_hybrid: bool,
) -> Result<(ReductionMapping<'a>, String), ParseTheoremError> {
    let mapping_span = ast.as_span();
    let mut ast = ast.into_inner();

    let (assumption_game_inst_name_ast, construction_game_inst_name_ast) = ast
        .next_tuple()
        .expect("map_spec grammar requires assumption and construction game names");
    let assumption_game_inst_name_ast: GameInstanceName = assumption_game_inst_name_ast.into();

    let (assumption_game_inst, construction_game_inst, construction_game_inst_name) =
        resolve_mapping_games(
            ctx,
            &assumption_game_inst_name_ast,
            &construction_game_inst_name_ast,
            assumption,
            is_hybrid,
        )?;

    let mappings: Vec<_> = ast
        .flat_map(|p| p.into_inner().map(PackageInstanceName::from))
        .tuples()
        .collect();

    let pkg_offset_mapping = check_mapping_assignments(
        ctx,
        mapping_span,
        &mappings,
        assumption_game_inst,
        construction_game_inst,
    )?;
    check_assumption_coverage(ctx, mapping_span, &mappings, assumption_game_inst)?;
    check_incoming_wires(
        ctx,
        mapping_span,
        &pkg_offset_mapping,
        assumption_game_inst,
        construction_game_inst,
    )?;
    check_adversary_exports(
        ctx,
        &pkg_offset_mapping,
        assumption_game_inst,
        construction_game_inst,
    )?;

    // Preserve the original per-package order: forward wires, then reverse wires.
    for entry in &pkg_offset_mapping {
        let construction = &entry.construction_offset;
        let assumption = &entry.assumption_offset;
        for check in [check_construction_wires, check_assumption_wires] {
            check(
                ctx,
                mapping_span,
                &pkg_offset_mapping,
                assumption_game_inst,
                construction_game_inst,
                construction,
                assumption,
            )?;
        }
    }

    let mapping = ReductionMapping {
        assumption: assumption_game_inst_name_ast,
        construction: construction_game_inst_name_ast.into(),
        entries: mappings
            .into_iter()
            .map(|(left, right)| ReductionMappingEntry {
                assumption: left,
                construction: right,
            })
            .collect_vec(),
    };
    Ok((mapping, construction_game_inst_name))
}

fn resolve_mapping_games<'ctx>(
    ctx: &'ctx ParseTheoremContext,
    assumption_game_inst_name_ast: &GameInstanceName,
    construction_game_inst_name_ast: &Pair<Rule>,
    assumption: &Assumption,
    is_hybrid: bool,
) -> Result<(&'ctx GameInstance, &'ctx GameInstance, String), ParseTheoremError> {
    let assumption_game_inst_name_span = assumption_game_inst_name_ast.as_span();
    let construction_game_inst_name_span = construction_game_inst_name_ast.as_span();
    let assumption_game_inst_name = assumption_game_inst_name_ast.as_str();
    let construction_game_inst_name = if is_hybrid {
        if construction_game_inst_name_ast.as_rule() != Rule::hybrid_map_spec_ident {
            return Err(ReductionInvalidHybridMappingError {
                source_code: ctx.named_source(),
                at: (construction_game_inst_name_span.start()
                    ..construction_game_inst_name_span.end())
                    .into(),
            }
            .into());
        }
        let mut inner = construction_game_inst_name_ast.clone().into_inner();
        let (instance_name, bit_var_const) = inner
            .next_tuple()
            .expect("hybrid_map_spec_ident grammar requires an identifier and a boolean literal");
        let (instance_name, bit_var_const) = (instance_name.as_str(), bit_var_const.as_str());

        format!("{instance_name}${bit_var_const}$")
    } else {
        construction_game_inst_name_ast.as_str().to_string()
    };

    let (_, assumption_game_inst) =
        ctx.game_instance(assumption_game_inst_name)
            .ok_or_else(|| UndefinedGameInstanceError {
                source_code: ctx.named_source(),
                at: (assumption_game_inst_name_span.start()..assumption_game_inst_name_span.end())
                    .into(),
                game_inst_name: assumption_game_inst_name.to_string(),
            })?;

    let (_, construction_game_inst) =
        ctx.game_instance(&construction_game_inst_name)
            .ok_or_else(|| UndefinedGameInstanceError {
                source_code: ctx.named_source(),
                at: (construction_game_inst_name_span.start()
                    ..construction_game_inst_name_span.end())
                    .into(),
                game_inst_name: construction_game_inst_name.to_string(),
            })?;

    let assumption_game_is_really_assumption_game = assumption_game_inst_name
        == assumption.left_name
        || assumption_game_inst_name == assumption.right_name;

    let construction_game_is_actually_assumption_game = construction_game_inst_name
        == assumption.left_name
        || construction_game_inst_name == assumption.right_name;

    if !assumption_game_is_really_assumption_game {
        return Err(AssumptionMappingLeftGameInstanceIsNotFromAssumption {
            source_code: ctx.named_source(),
            at: (assumption_game_inst_name_span.start()..assumption_game_inst_name_span.end())
                .into(),
            game_instance_name: assumption_game_inst_name.to_string(),
            assumption_left_game_instance_name: assumption.left_name.clone(),
            assumption_right_game_instance_name: assumption.right_name.clone(),
        }
        .into());
    }

    if construction_game_is_actually_assumption_game {
        return Err(AssumptionMappingRightGameInstanceIsFromAssumption {
            source_code: ctx.named_source(),
            at: (construction_game_inst_name_span.start()..construction_game_inst_name_span.end())
                .into(),
            game_instance_name: construction_game_inst_name.to_string(),
            model_left_game_instance_name: assumption_game_inst_name.to_string(),
            model_right_game_instance_name: construction_game_inst_name.to_string(),
        }
        .into());
    }

    Ok((
        assumption_game_inst,
        construction_game_inst,
        construction_game_inst_name,
    ))
}

fn check_duplicate_assignments<'map, 'a>(
    ctx: &ParseTheoremContext,
    assumption: &'map PackageInstanceName<'a>,
    construction: &'map PackageInstanceName<'a>,
    assumption_names: &mut HashMap<&'a str, &'map PackageInstanceName<'a>>,
    construction_names: &mut HashMap<&'a str, &'map PackageInstanceName<'a>>,
) -> Result<(), ParseTheoremError> {
    // Check the assumption side first when both names are duplicates.
    for (name, seen) in [
        (assumption, assumption_names),
        (construction, construction_names),
    ] {
        if let Some(previous) = seen.get(name.as_str()) {
            let span = name.as_span();
            let previous_span = previous.as_span();
            return Err(AssumptionMappingDuplicatePackageInstanceError {
                source_code: ctx.named_source(),
                at_this: (span.start()..span.end()).into(),
                at_prev: (previous_span.start()..previous_span.end()).into(),
                pkg_inst_name: name.as_str().to_string(),
            }
            .into());
        }
        seen.insert(name.as_str(), name);
    }
    Ok(())
}

fn check_mapping_diff(
    ctx: &ParseTheoremContext,
    assumption: &PackageInstanceName,
    construction: &PackageInstanceName,
    diff: PackageInstanceDiff,
) -> Result<(), ParseTheoremError> {
    if matches!(diff, PackageInstanceDiff::Same) {
        return Ok(());
    }
    let assumption_span = assumption.as_span();
    let construction_span = construction.as_span();
    let at_assumption = (assumption_span.start()..assumption_span.end()).into();
    let at_construction = (construction_span.start()..construction_span.end()).into();
    let assumption_pkg_inst_name = assumption.as_str().to_string();
    let construction_pkg_inst_name = construction.as_str().to_string();
    match diff {
        PackageInstanceDiff::DifferentPackage(assumption_pkg_name, construction_pkg_name) => {
            Err(AssumptionMappingContainsDifferentPackagesError {
                source_code: ctx.named_source(),
                at_assumption,
                at_construction,
                assumption_pkg_inst_name,
                construction_pkg_inst_name,
                assumption_pkg_name,
                construction_pkg_name,
            }
            .into())
        }
        PackageInstanceDiff::DifferentParams(params) => {
            Err(AssumptionMappingParameterMismatchError {
                source_code: ctx.named_source(),
                at_assumption,
                at_construction,
                assumption_pkg_inst_name,
                construction_pkg_inst_name,
                param_names: params.join(", "),
            }
            .into())
        }
        PackageInstanceDiff::Same => Ok(()),
    }
}

fn resolve_mapping_package<'game>(
    ctx: &ParseTheoremContext,
    name: &PackageInstanceName,
    game: &'game GameInstance,
) -> Result<(usize, &'game PackageInstance), ParseTheoremError> {
    game.game()
        .pkgs
        .iter()
        .enumerate()
        .find(|(_, instance)| instance.name() == name.as_str())
        .ok_or_else(|| {
            let span = name.as_span();
            UndefinedPackageInstanceError {
                source_code: ctx.named_source(),
                at: (span.start()..span.end()).into(),
                pkg_inst_name: name.as_str().to_string(),
                in_game: game.game_name().to_string(),
            }
            .into()
        })
}

struct MappingEntry<'map, 'a> {
    assumption_offset: usize,
    construction_offset: usize,
    assumption_ast: &'map PackageInstanceName<'a>,
    construction_ast: &'map PackageInstanceName<'a>,
}

fn check_mapping_assignments<'map, 'a>(
    ctx: &ParseTheoremContext,
    mapping_span: pest::Span,
    mappings: &'map [(PackageInstanceName<'a>, PackageInstanceName<'a>)],
    assumption_game: &GameInstance,
    construction_game: &GameInstance,
) -> Result<Vec<MappingEntry<'map, 'a>>, ParseTheoremError> {
    let mut assumption_names = HashMap::new();
    let mut construction_names = HashMap::new();
    let mut entries = Vec::with_capacity(mappings.len());
    for (assumption_ast, construction_ast) in mappings {
        check_duplicate_assignments(
            ctx,
            assumption_ast,
            construction_ast,
            &mut assumption_names,
            &mut construction_names,
        )?;
        let (assumption_offset, assumption) =
            resolve_mapping_package(ctx, assumption_ast, assumption_game)?;
        let (construction_offset, construction) =
            resolve_mapping_package(ctx, construction_ast, construction_game)?;
        let diff = package_instances_diff(
            ctx,
            mapping_span,
            assumption,
            assumption_game,
            construction,
            construction_game,
        )?;
        check_mapping_diff(ctx, assumption_ast, construction_ast, diff)?;
        entries.push(MappingEntry {
            assumption_offset,
            construction_offset,
            assumption_ast,
            construction_ast,
        });
    }
    Ok(entries)
}

fn check_assumption_coverage(
    ctx: &ParseTheoremContext,
    mapping_span: pest::Span,
    mappings: &[(PackageInstanceName, PackageInstanceName)],
    assumption_game_inst: &GameInstance,
) -> Result<(), ParseTheoremError> {
    let assumption_game_pkg_inst_names: HashSet<_> = mappings
        .iter()
        .map(|(assumption, _)| assumption.as_str())
        .collect();

    for pkg_inst in &assumption_game_inst.game().pkgs {
        if !assumption_game_pkg_inst_names.contains(pkg_inst.name.as_str()) {
            let span = mapping_span;
            let at = (span.start()..span.end()).into();
            let pkg_inst_name = pkg_inst.name.to_string();
            return Err(AssumptionMappingMissesPackageInstanceError {
                source_code: ctx.named_source(),
                at,

                pkg_inst_name,
            }
            .into());
        }
    }

    Ok(())
}

fn rewrite_game_signature(
    ctx: &ParseTheoremContext,
    game: &GameInstance,
    sig: &OracleSig,
) -> OracleSig {
    InstantiationContext::new_game_instantiation_context(
        game.name(),
        ctx.theorem_name,
        &game.consts,
    )
    .rewrite_oracle_sig(sig.clone())
}

fn check_incoming_wires(
    ctx: &ParseTheoremContext,
    mapping_span: pest::Span,
    pkg_offset_mapping: &[MappingEntry],
    assumption_game_inst: &GameInstance,
    construction_game_inst: &GameInstance,
) -> Result<(), ParseTheoremError> {
    // cross-cut wires: check that all wires from the reduction subgraph into
    // the assumption subgraph point to oracles which the assumption game exports
    for edge in &construction_game_inst.game().edges {
        let dst_pkginst_mapping = pkg_offset_mapping
            .iter()
            .find(|entry| entry.construction_offset == edge.to());

        // constr_src is not in the mapping => it's in the reduction part
        let src_is_in_reduction_part = pkg_offset_mapping
            .iter()
            .all(|entry| entry.construction_offset != edge.from());

        // ignore edges that start in mapped packages, because we are only interested in cross-cut
        // edges
        if !src_is_in_reduction_part {
            continue;
        }

        if let Some(entry) = dst_pkginst_mapping {
            let assump_dst = entry.assumption_offset;
            let constr_dst_pkg_inst = &construction_game_inst.game().pkgs[edge.to()];
            let assump_dst_pkg_inst = &assumption_game_inst.game().pkgs[assump_dst];

            // this lookup is by comparing the oracle name, not the whole signature
            let assump_dst_export =
                assumption_game_inst.game().exports.iter().find(|export| {
                    export.to() == assump_dst && export.sig().name == edge.sig().name
                });

            let constr_sig_owned = rewrite_game_signature(ctx, construction_game_inst, edge.sig());
            let constr_sig = &constr_sig_owned;

            // if it's cross-cut, it needs to be exported, else error out
            let Some(assump_dst_export) = assump_dst_export else {
                let assumption_span = entry.assumption_ast.as_span();
                let assumption_at = (assumption_span.start()..assumption_span.end()).into();

                let construction_span = entry.construction_ast.as_span();
                let construction_at = (construction_span.start()..construction_span.end()).into();

                let assumption_pkg_inst_name =
                    assumption_game_inst.game().pkgs[assump_dst].name.clone();
                let construction_pkg_inst_name =
                    construction_game_inst.game().pkgs[edge.to()].name.clone();
                let oracle_name = constr_sig.name.clone();

                return Err(AssumptionExportsNotSufficientError {
                    source_code: ctx.named_source(),
                    assumption_at,
                    construction_at,
                    assumption_pkg_inst_name,
                    construction_pkg_inst_name,
                    oracle_name,
                }
                .into());
            };

            let assump_sig = assump_dst_export.sig();

            // rewrite the destination oracle signature as well and compare to check that they
            // match
            let assump_sig_fixed = rewrite_game_signature(ctx, assumption_game_inst, assump_sig);
            let constr_sig_fixed = rewrite_game_signature(ctx, construction_game_inst, constr_sig);

            // This check was a debug assertion. Keep its build-mode behavior;
            // making it unconditional would reject previously accepted inputs.
            #[cfg(debug_assertions)]
            if !constr_sig_fixed.types_match(&assump_sig_fixed) {
                return Err(
                    super::error::AssumptionMappingOracleSignatureMismatchError {
                        source_code: ctx.named_source(),
                        at: (mapping_span.start()..mapping_span.end()).into(),
                        oracle_name: constr_sig_fixed.name.clone(),
                        assumption_game_name: assumption_game_inst.game_name().to_string(),
                        construction_game_name: construction_game_inst.game_name().to_string(),
                        assumption_signature: assump_sig_fixed.to_oracle_type().to_string(),
                        construction_signature: constr_sig_fixed.to_oracle_type().to_string(),
                    }
                    .into(),
                );
            }
            #[cfg(not(debug_assertions))]
            let _ = (constr_sig_fixed, assump_sig_fixed);

            // check that the destination packages in construction and assumption are equivalent

            let diff = package_instances_diff(
                ctx,
                mapping_span,
                constr_dst_pkg_inst,
                construction_game_inst,
                assump_dst_pkg_inst,
                assumption_game_inst,
            )?;
            // Comparison remains construction-first: repeated assignments make
            // it asymmetric. Reorient only the diagnostic's package names.
            let diff = match diff {
                PackageInstanceDiff::DifferentPackage(construction, assumption) => {
                    PackageInstanceDiff::DifferentPackage(assumption, construction)
                }
                other => other,
            };
            check_mapping_diff(ctx, entry.assumption_ast, entry.construction_ast, diff)?;
        }
    }

    Ok(())
}

fn check_adversary_exports(
    ctx: &ParseTheoremContext,
    pkg_offset_mapping: &[MappingEntry],
    assumption_game_inst: &GameInstance,
    construction_game_inst: &GameInstance,
) -> Result<(), ParseTheoremError> {
    // cross-cut exports: check that all oracles the construction game exports to the adversary
    // directly from the assumption subgraph are also exported by the assumption game
    for constr_export in &construction_game_inst.game().exports {
        let Some(entry) = pkg_offset_mapping
            .iter()
            .find(|entry| entry.construction_offset == constr_export.to())
        else {
            // the export goes into the reduction part, so the adversary of the assumption does
            // not need access to it
            continue;
        };

        // this lookup is by comparing the oracle name, not the export alias
        let assump_has_export = assumption_game_inst.game().exports.iter().any(|export| {
            export.to() == entry.assumption_offset && export.sig().name == constr_export.sig().name
        });

        if !assump_has_export {
            let assumption_dst_name =
                &assumption_game_inst.game().pkgs[entry.assumption_offset].name;
            let assumption_span = entry.assumption_ast.as_span();
            let assumption_at = (assumption_span.start()..assumption_span.end()).into();

            let construction_span = entry.construction_ast.as_span();
            let construction_at = (construction_span.start()..construction_span.end()).into();

            return Err(AssumptionAdversaryExportsNotSufficientError {
                source_code: ctx.named_source(),
                assumption_at,
                construction_at,
                assumption_pkg_inst_name: assumption_dst_name.clone(),
                construction_pkg_inst_name: construction_game_inst.game().pkgs[constr_export.to()]
                    .name
                    .clone(),
                oracle_name: constr_export.sig().name.clone(),
            }
            .into());
        }
    }

    Ok(())
}

enum WiringDirection {
    ConstructionToAssumption,
    AssumptionToConstruction,
}

fn wiring_mismatch_diagnostic(
    ctx: &ParseTheoremContext,
    span: pest::Span,
    assumption: &Composition,
    construction: &Composition,
    direction: WiringDirection,
    edge: &Edge,
    mapped: (usize, usize),
) -> ParseTheoremError {
    let (direction, source, target) = match direction {
        WiringDirection::ConstructionToAssumption => {
            ("construction to assumption", construction, assumption)
        }
        WiringDirection::AssumptionToConstruction => {
            ("assumption to construction", assumption, construction)
        }
    };
    AssumptionMappingWiringMismatchError {
        source_code: ctx.named_source(),
        at: (span.start()..span.end()).into(),
        direction: direction.to_string(),
        assumption_game_name: assumption.name.clone(),
        construction_game_name: construction.name.clone(),
        from_pkg_inst_name: source.pkgs[edge.from()].name.clone(),
        to_pkg_inst_name: source.pkgs[edge.to()].name.clone(),
        mapped_from_pkg_inst_name: target.pkgs[mapped.0].name.clone(),
        mapped_to_pkg_inst_name: target.pkgs[mapped.1].name.clone(),
        import_name: edge.name().to_string(),
        oracle_name: edge.sig().name.clone(),
        oracle_signature: edge.sig().to_oracle_type().to_string(),
    }
    .into()
}

fn check_construction_wires(
    ctx: &ParseTheoremContext,
    mapping_span: pest::Span,
    pkg_offset_mapping: &[MappingEntry],
    assumption_game_inst: &GameInstance,
    construction_game_inst: &GameInstance,
    constr_src_pkg_inst_offs: &usize,
    assump_src_pkg_inst_offs: &usize,
) -> Result<(), ParseTheoremError> {
    // all edges in the construction game that start at the package instance we are currently
    // looking at. We are only looking at mapped package instances, so we know it is part
    // of the assumption part of the construction game.
    let construction_game_assumptionpart_edges = construction_game_inst
        .game()
        .edges
        .iter()
        .filter(|edge| edge.from() == *constr_src_pkg_inst_offs);

    // edge exists in construction => edge exists in assumption
    for construction_edge in construction_game_assumptionpart_edges {
        let destination = pkg_offset_mapping
            .iter()
            .find(|entry| entry.construction_offset == construction_edge.to())
            .ok_or_else(|| AssumptionMappingUnmappedDestinationError {
                source_code: ctx.named_source(),
                at: (mapping_span.start()..mapping_span.end()).into(),
                from_pkg_inst_name: construction_game_inst.game().pkgs[construction_edge.from()]
                    .name()
                    .to_string(),
                to_pkg_inst_name: construction_game_inst.game().pkgs[construction_edge.to()]
                    .name()
                    .to_string(),
                import_name: construction_edge.name().to_string(),
                oracle_name: construction_edge.sig().name.clone(),
            })?;

        let constr_sig_fixed =
            rewrite_game_signature(ctx, construction_game_inst, construction_edge.sig());
        let edge_exists_in_assumption =
            assumption_game_inst
                .game()
                .edges
                .iter()
                .any(|assumption_game_edge| {
                    let assump_sig_fixed = rewrite_game_signature(
                        ctx,
                        assumption_game_inst,
                        assumption_game_edge.sig(),
                    );

                    assumption_game_edge.from() == *assump_src_pkg_inst_offs
                        && assumption_game_edge.to() == destination.assumption_offset
                        && constr_sig_fixed.types_match(&assump_sig_fixed)
                });

        if !edge_exists_in_assumption {
            return Err(wiring_mismatch_diagnostic(
                ctx,
                mapping_span,
                assumption_game_inst.game(),
                construction_game_inst.game(),
                WiringDirection::ConstructionToAssumption,
                construction_edge,
                (*assump_src_pkg_inst_offs, destination.assumption_offset),
            ));
        }
    }

    Ok(())
}

fn check_assumption_wires(
    ctx: &ParseTheoremContext,
    mapping_span: pest::Span,
    pkg_offset_mapping: &[MappingEntry],
    assumption_game_inst: &GameInstance,
    construction_game_inst: &GameInstance,
    constr_src_pkg_inst_offs: &usize,
    assump_src_pkg_inst_offs: &usize,
) -> Result<(), ParseTheoremError> {
    // all edges in the assumtion game that start at the package instance we are currently
    // looking at.
    let assumption_game_edges = assumption_game_inst
        .game()
        .edges
        .iter()
        .filter(|edge| edge.from() == *assump_src_pkg_inst_offs);

    // edge exists in assumption => edge exists in construction
    for assumption_edge in assumption_game_edges {
        let destination = pkg_offset_mapping
            .iter()
            .find(|entry| entry.assumption_offset == assumption_edge.to())
            .expect("assumption coverage validation maps every assumption package instance");

        let edge_exists_in_construction =
            construction_game_inst
                .game()
                .edges
                .iter()
                .any(|construction_game_edge| {
                    construction_game_edge.from() == *constr_src_pkg_inst_offs
                        && construction_game_edge.to() == destination.construction_offset
                });

        if !edge_exists_in_construction {
            return Err(wiring_mismatch_diagnostic(
                ctx,
                mapping_span,
                assumption_game_inst.game(),
                construction_game_inst.game(),
                WiringDirection::AssumptionToConstruction,
                assumption_edge,
                (*constr_src_pkg_inst_offs, destination.construction_offset),
            ));
        }
    }
    Ok(())
}

fn package_instances_diff<'a>(
    ctx: &ParseTheoremContext,
    span: pest::Span,
    left_pkg_inst: &'a PackageInstance,
    left_game_inst: &GameInstance,
    right_pkg_inst: &PackageInstance,
    right_game_inst: &GameInstance,
) -> Result<PackageInstanceDiff<'a>, ParseTheoremError> {
    if left_pkg_inst.pkg.name != right_pkg_inst.pkg.name {
        return Ok(PackageInstanceDiff::DifferentPackage(
            left_pkg_inst.pkg.name.clone(),
            right_pkg_inst.pkg.name.clone(),
        ));
    }

    // Repeated params blocks can supply more than one assignment per name.
    if left_pkg_inst.params.len() != right_pkg_inst.params.len() {
        return Err(ReductionPackageParameterCountMismatchError {
            source_code: ctx.named_source(),
            at: (span.start()..span.end()).into(),
            left_pkg_inst_name: left_pkg_inst.name().to_string(),
            right_pkg_inst_name: right_pkg_inst.name().to_string(),
            left_count: left_pkg_inst.params.len(),
            right_count: right_pkg_inst.params.len(),
        }
        .into());
    }

    let mut different_params = vec![];
    let mut right_params = HashMap::new();
    for (ident, expression) in &right_pkg_inst.params {
        // Repeated params blocks are possible. Retain the first assignment to
        // match the previous linear search and keep left-side diagnostic order.
        right_params
            .entry(ident.name.as_str())
            .or_insert(expression);
    }

    for (param_ident, left_param_expr) in &left_pkg_inst.params {
        let right_param_expr = *right_params
            .get(param_ident.name.as_str())
            .expect("package instantiation validates every parameter of the same package type");

        // here we compare whether param_expr and other_param_expr match.
        // problem 1: they have identifiers in them that contain things like game names
        // problem 2: we have the game identifiers here, but we need the theorem identifiers,
        //            because otherwise we just compare the name strings used in the game
        //            and ignore the values assigned to the in game instantiation
        //
        // we solve both problems using Expression::map, which both resolves the game identifiers
        // to theorem identifiers and redacts game- and package-specific information.

        fn resolve_and_redact_expr(
            game_inst_const_mapping: &[(GameConstIdentifier, Expression)],
            expr: Expression,
        ) -> Expression {
            let kind = match expr.into_kind() {
                // redact game and package specific information from theorem identifiers
                ExpressionKind::Identifier(Identifier::TheoremIdentifier(
                    TheoremIdentifier::Const(mut theorem_const),
                )) => {
                    theorem_const.inst_info = None;
                    ExpressionKind::Identifier(theorem_const.into())
                }
                ExpressionKind::Identifier(Identifier::TheoremIdentifier(
                    TheoremIdentifier::LoopVar(mut theorem_loopvar),
                )) => {
                    theorem_loopvar.inst_info = None;
                    ExpressionKind::Identifier(theorem_loopvar.into())
                }

                // resolve game const identifiers
                ExpressionKind::Identifier(Identifier::GameIdentifier(GameIdentifier::Const(
                    ref game_const,
                ))) => {
                    let (_, assigned_expr) = game_inst_const_mapping
                        .iter()
                        .find(|(game_inst_param, _)| game_inst_param.name == game_const.name)
                        .expect("game instantiation assigns every declared game constant used by package parameters");

                    assigned_expr
                        .map(|expr| resolve_and_redact_expr(game_inst_const_mapping, expr))
                        .into_kind()
                }

                other => other,
            };

            Expression::from_kind(kind)
        }

        let redacted_left_param_expr =
            left_param_expr.map(|expr| resolve_and_redact_expr(&left_game_inst.consts, expr));
        let redacted_right_param_expr =
            right_param_expr.map(|expr| resolve_and_redact_expr(&right_game_inst.consts, expr));

        if redacted_left_param_expr != redacted_right_param_expr {
            different_params.push(param_ident.name.as_str());
        }
    }

    if !different_params.is_empty() {
        Ok(PackageInstanceDiff::DifferentParams(different_params))
    } else {
        Ok(PackageInstanceDiff::Same)
    }
}

enum PackageInstanceDiff<'a> {
    DifferentPackage(String, String),
    DifferentParams(Vec<&'a str>),
    Same,
}

// ----

#[derive(Clone, Debug)]
pub(crate) struct ReductionMapping<'a> {
    assumption: GameInstanceName<'a>,
    construction: GameInstanceName<'a>,

    entries: Vec<ReductionMappingEntry<'a>>,
}

impl<'a> ReductionMapping<'a> {
    pub(crate) fn assumption_game_instance_name(&self) -> &GameInstanceName<'a> {
        &self.assumption
    }

    pub(crate) fn construction_game_instance_name(&self) -> &GameInstanceName<'a> {
        &self.construction
    }

    pub(crate) fn entries(&self) -> &[ReductionMappingEntry<'a>] {
        &self.entries
    }
}

#[derive(Clone, Debug)]
pub(crate) struct ReductionMappingEntry<'a> {
    assumption: PackageInstanceName<'a>,
    construction: PackageInstanceName<'a>,
}

impl<'a> ReductionMappingEntry<'a> {
    #[allow(dead_code)]
    pub(crate) fn assumption(&self) -> &PackageInstanceName<'a> {
        &self.assumption
    }

    pub(crate) fn construction(&self) -> &PackageInstanceName<'a> {
        &self.construction
    }
}

#[cfg(test)]
mod traversal_tests {
    use super::*;
    use crate::package::Edge;
    use crate::parser::{
        tests::{games, packages},
        SspParser,
    };
    use pest::Parser;

    // Parse a small valid graph, then extend it without making the parser's
    // cost part of the traversal regression.
    fn router_game(depth: usize, cyclic: bool) -> GameInstance {
        let pkgs = packages::parse_files(&["Leaf.pkg.ssp", "Router.pkg.ssp"]);
        let mut game = games::parse_file("RightGame-router.comp.ssp", &pkgs);
        let router = game.pkgs.pop().unwrap();
        let sig = game.edges[0].sig().clone();
        game.edges.clear();
        for i in 1..=depth {
            let mut instance = router.clone();
            instance.name = format!("r{i}");
            game.pkgs.push(instance);
            let to = if i == depth {
                if cyclic {
                    1
                } else {
                    0
                }
            } else {
                i + 1
            };
            for name in ["A", "B"] {
                game.edges
                    .push(Edge::new(i, to, sig.clone(), Some(name.into())));
            }
        }
        GameInstance::new("context".into(), "Traversal".into(), game, vec![], vec![])
    }

    fn compare_with_budget(
        left: &GameInstance,
        right: &GameInstance,
        budget: usize,
    ) -> (Result<(), ParseTheoremError>, usize) {
        let ctx = ParseTheoremContext {
            file_name: "traversal.ssp",
            file_content: "context",
            theorem_name: "Traversal",
            scope: crate::util::scope::Scope::new(),
            types: vec![],
            consts: HashMap::new(),
            instances: vec![],
            instances_table: HashMap::new(),
            assumptions: vec![],
            propositions: vec![],
            game_hops: vec![],
        };
        let name = SspParser::parse(Rule::identifier, "context")
            .unwrap()
            .next()
            .unwrap();
        let mapping = ReductionMapping {
            assumption: name.clone().into(),
            construction: name.into(),
            entries: vec![],
        };
        let mut traversal = ReductionTraversal::new(left.game(), right.game());
        traversal.visit_budget = budget;
        let result = compare_reduction(
            &ctx,
            pest::Span::new("context", 0, 7).unwrap(),
            1,
            1,
            left,
            right,
            &mapping,
            &mapping,
            &mut traversal,
        );
        (result, traversal.visit_count)
    }

    #[test]
    fn deep_context_chain_passes() {
        let game = router_game(8192, false);
        let (result, visits) = compare_with_budget(&game, &game, 8193);
        result.unwrap();
        assert_eq!(visits, 8193);
    }

    #[test]
    fn deep_context_chain_reports_leaf_mismatch() {
        let left = router_game(8192, false);
        let mut right = left.clone();
        right.game.pkgs[0].pkg.name = "DifferentLeaf".into();
        let (result, _) = compare_with_budget(&left, &right, 8193);
        let Err(ParseTheoremError::ReductionContainsDifferentPackages(error)) = result else {
            panic!("expected the leaf package mismatch");
        };
        assert_eq!(error.right_pkg_name, "DifferentLeaf");
    }

    #[test]
    fn long_context_cycle_reports_cycle() {
        // Coprime cycle lengths require 16,637 distinct pairs before repetition.
        let left = router_game(127, true);
        let right = router_game(131, true);
        let (result, visits) = compare_with_budget(&left, &right, 127 * 131);
        let Err(ParseTheoremError::ReductionCyclicContext(error)) = result else {
            panic!("expected a cycle diagnostic");
        };
        assert_eq!(visits, 127 * 131);
        assert_eq!(error.left_pkg_inst_name, "r1");
        assert_eq!(error.right_pkg_inst_name, "r1");
    }
}
