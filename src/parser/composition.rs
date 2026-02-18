// SPDX-License-Identifier: MIT OR Apache-2.0

use super::{
    common::*,
    error::{
        DuplicateEdgeDefinitionError, DuplicateExportError,
        DuplicatePackageParameterDefinitionError, MissingEdgeForImportedOracleError,
        MissingPackageParameterDefinitionError, NoSuchPackageParameterError,
        OracleSigMismatchError, UndefinedOracleError, UndefinedPackageError,
        UndefinedPackageInstanceError, UnusedEdgeError,
    },
    package::ParsePackageError,
    ParseContext, Rule,
};
use crate::{
    debug_assert_matches,
    expressions::Expression,
    identifier::{game_ident::GameConstIdentifier, pkg_ident::PackageConstIdentifier},
    package::{Composition, Edge, Export, Package, PackageInstance},
    types::Type,
    util::scope::Error as ScopeError,
};
use itertools::Itertools as _;
use miette::{Diagnostic, NamedSource};
use pest::{iterators::Pair, Span};
use std::collections::HashMap;
use std::iter::FromIterator as _;
use thiserror::Error;

#[derive(Debug)]
pub struct ParseGameContext<'src> {
    pub file_name: &'src str,
    pub file_content: &'src str,
    pub game_name: &'src str,
    pub pkgs: &'src HashMap<String, Package>,

    pub scope: Scope,

    pub consts: HashMap<String, Type>,
    pub types: Vec<String>,

    pub instances: Vec<(PackageInstance, Span<'src>)>,
    pub instances_table: HashMap<String, (usize, PackageInstance, Span<'src>)>,

    pub edges: Vec<Edge>,
    pub exports: Vec<Export>,
}

impl<'src> ParseContext<'src> {
    fn game_context(
        self,
        game_name: &'src str,
        pkgs: &'src HashMap<String, Package>,
    ) -> ParseGameContext<'src> {
        let Self {
            file_name,
            file_content,
            scope,
            types,
        } = self;

        ParseGameContext {
            file_name,
            file_content,
            game_name,
            pkgs,

            scope,

            types,
            consts: HashMap::new(),

            instances: vec![],
            instances_table: HashMap::new(),

            edges: vec![],
            exports: vec![],
        }
    }
}

impl<'src> ParseGameContext<'src> {
    pub(crate) fn named_source(&self) -> NamedSource<String> {
        NamedSource::new(self.file_name, self.file_content.to_string())
    }

    pub(crate) fn parse_ctx(&self) -> ParseContext<'src> {
        ParseContext {
            file_name: self.file_name,
            file_content: self.file_content,
            scope: self.scope.clone(),
            types: self.types.clone(),
        }
    }
}

impl<'src> ParseGameContext<'src> {
    fn into_game(self) -> Composition {
        let mut consts = Vec::from_iter(self.consts);
        consts.sort();

        Composition {
            name: self.game_name.to_string(),
            consts,
            pkgs: self.instances.into_iter().map(|(inst, _)| inst).collect(),
            edges: self.edges,
            exports: self.exports,
        }
    }

    fn declare(&mut self, name: &str, clone: Declaration) -> Result<(), ScopeError> {
        self.scope.declare(name, clone)
    }
    // TODO: check dupes here?

    fn add_pkg_instance(&mut self, pkg_inst: PackageInstance, span: Span<'src>) {
        let offset = self.instances.len();
        self.instances.push((pkg_inst.clone(), span));
        self.instances_table
            .insert(pkg_inst.name.clone(), (offset, pkg_inst, span));
    }

    fn get_pkg_instance(&self, name: &str) -> Option<(usize, &PackageInstance)> {
        self.instances_table
            .get(name)
            .map(|(offset, pkg_inst, _)| (*offset, pkg_inst))
    }

    // TODO: check dupes here?
    fn add_const(&mut self, name: String, ty: Type) {
        self.consts.insert(name, ty);
    }

    fn add_edge(&mut self, edge: Edge) {
        self.edges.push(edge)
    }
    fn has_export(&mut self, name: &str) -> bool {
        self.exports.iter().any(|exp| exp.name() == name)
    }

    fn add_export(&mut self, export: &Export) {
        self.exports.push(export.clone());
    }
}

#[derive(Debug, Error, Diagnostic)]
pub enum ParseGameError {
    #[error(transparent)]
    #[diagnostic(transparent)]
    ParsePackage(#[from] ParsePackageError),

    #[error(transparent)]
    #[diagnostic(transparent)]
    ParseExpression(#[from] super::package::ParseExpressionError),

    #[error(transparent)]
    #[diagnostic(transparent)]
    UndefinedInstance(#[from] UndefinedPackageInstanceError),

    #[error(transparent)]
    #[diagnostic(transparent)]
    UndefinedPackage(#[from] UndefinedPackageError),

    #[error(transparent)]
    #[diagnostic(transparent)]
    UndefinedOracle(#[from] UndefinedOracleError),

    #[error(transparent)]
    #[diagnostic(transparent)]
    NoSuchParameter(#[from] NoSuchPackageParameterError),

    #[error(transparent)]
    #[diagnostic(transparent)]
    DuplicateParameterDefinition(#[from] DuplicatePackageParameterDefinitionError),

    #[error(transparent)]
    #[diagnostic(transparent)]
    MissingPackageParameterDefinition(#[from] MissingPackageParameterDefinitionError),

    #[diagnostic(transparent)]
    #[error(transparent)]
    HandleType(#[from] HandleTypeError),

    #[diagnostic(transparent)]
    #[error(transparent)]
    MissingEdgeForImportedOracle(#[from] MissingEdgeForImportedOracleError),

    #[diagnostic(transparent)]
    #[error(transparent)]
    UnusedEdge(#[from] UnusedEdgeError),

    #[diagnostic(transparent)]
    #[error(transparent)]
    DuplicateExport(#[from] DuplicateExportError),

    #[diagnostic(transparent)]
    #[error(transparent)]
    DuplicateEdgeDefinition(#[from] DuplicateEdgeDefinitionError),

    #[diagnostic[transparent]]
    #[error[transparent]]
    ConnectedOraclesDontMatch(#[from] OracleSigMismatchError),
}

pub(crate) fn handle_composition(
    file_name: &str,
    file_content: &str,
    ast: Pair<Rule>,
    pkg_map: &HashMap<String, Package>,
) -> Result<Composition, ParseGameError> {
    let mut inner = ast.into_inner();
    let game_name = inner.next().unwrap().as_str();

    let mut scope = Scope::new();
    scope.enter();

    let ctx = ParseContext::new(file_name, file_content).game_context(game_name, pkg_map);

    let spec = inner.next().unwrap();
    handle_comp_spec_list(ctx, spec)
}

/// Parses the main body of a game (aka composition).
/// This function takes ownership of the context because it needs to move all the information stored in there into the game.
pub(crate) fn handle_comp_spec_list<'src>(
    mut ctx: ParseGameContext<'src>,
    ast: Pair<'src, Rule>,
) -> Result<Composition, ParseGameError> {
    for comp_spec in ast.into_inner() {
        match comp_spec.as_rule() {
            Rule::const_decl => {
                let (name, ty) = handle_const_decl(&ctx.parse_ctx(), comp_spec)?;
                ctx.add_const(name.clone(), ty.clone());
                ctx.declare(
                    &name,
                    Declaration::Identifier(
                        GameConstIdentifier {
                            game_name: ctx.game_name.to_string(),
                            name: name.clone(),
                            ty,
                            inst_info: None,
                            game_inst_name: None,
                            theorem_name: None,
                            assigned_value: None,
                        }
                        .into(),
                    ),
                )
                .unwrap();
            }
            Rule::instance_decl => {
                handle_instance_decl(&mut ctx, comp_spec)?;
            }
            Rule::compose_decl => handle_compose_assign_body_list(&mut ctx, comp_spec)?,
            _ => {
                unreachable!();
            }
        }
    }

    // Check that all imported oracles have been assigned in the compositions
    // This is just the single-instance case. The general case needs help from the smt solver
    for (offset, (inst, inst_span)) in ctx.instances.iter().enumerate() {
        for (import, _) in &inst.pkg.imports {
            let edge_exists = ctx
                .edges
                .iter()
                .any(|edge| edge.from() == offset && edge.name() == import.name);

            if !edge_exists {
                return Err(MissingEdgeForImportedOracleError {
                    source_code: ctx.named_source(),
                    pkg_inst_name: inst.name.clone(),
                    pkg_name: inst.pkg.name.clone(),
                    oracle_name: import.name.clone(),
                    at: (inst_span.start()..inst_span.end()).into(),
                }
                .into());
            }
        }
    }

    Ok(ctx.into_game())
}

pub(crate) fn handle_compose_assign_body_list(
    ctx: &mut ParseGameContext,
    ast: Pair<Rule>,
) -> Result<(), ParseGameError> {
    debug_assert!(matches!(ast.as_rule(), Rule::compose_decl));

    for body in ast.into_inner() {
        debug_assert!(matches!(body.as_rule(), Rule::compose_assign_body));

        let mut inner = body.into_inner();
        let src_inst_name_ast = inner.next().unwrap();
        let src_inst_name_span = src_inst_name_ast.as_span();
        let src_inst_name = src_inst_name_ast.as_str();

        let compose_assign_list_ast = inner.next().unwrap();
        debug_assert_eq!(compose_assign_list_ast.as_rule(), Rule::compose_assign_list);

        if src_inst_name == "adversary" {
            for export in handle_export_compose_assign_list(ctx, compose_assign_list_ast)? {
                if ctx.has_export(export.name()) {
                    return Err(ParseGameError::DuplicateExport(DuplicateExportError {
                        source_code: ctx.named_source(),
                        at: (src_inst_name_span.start()..src_inst_name_span.end()).into(),
                        oracle_name: export.name().to_string(),
                        game_name: ctx.game_name.to_string(),
                    }));
                }

                ctx.add_export(&export);
            }
        } else {
            let source_pkgidx = ctx
                .instances_table
                .get(src_inst_name)
                .ok_or(UndefinedPackageInstanceError {
                    source_code: ctx.named_source(),
                    at: (src_inst_name_span.start()..src_inst_name_span.end()).into(),
                    pkg_inst_name: src_inst_name.to_string(),
                    in_game: ctx.game_name.to_string(),
                })?
                .0;

            for edge in
                handle_edges_compose_assign_list(ctx, compose_assign_list_ast, source_pkgidx)?
            {
                ctx.add_edge(edge)
            }
        }
    }

    Ok(())
}

/// parses the oracle wiring assignment list for the exports.
fn handle_export_compose_assign_list(
    ctx: &mut ParseGameContext,
    ast: Pair<Rule>,
) -> Result<Vec<Export>, ParseGameError> {
    // compose_assign_list = { compose_assign ~ ( "," ~ compose_assign )* ~ ","? }
    assert_eq!(ast.as_rule(), Rule::compose_assign_list);

    let mut exports = vec![];

    // Iterate over the assignment pairs
    for assignment in ast.into_inner() {
        // compose_assign = { compose_assign_modifier? ~ identifier ~ ":" ~ identifier }
        assert_eq!(assignment.as_rule(), Rule::compose_assign);

        let assignment = assignment.into_inner().next().unwrap();
        let aliased = assignment.as_rule() == Rule::compose_assign_alias;
        let mut assignment = assignment.into_inner();

        let alias = if aliased {
            let alias_name_ast = assignment.next().unwrap();
            let alias_name = alias_name_ast.as_str();
            Some(alias_name.to_string())
        } else {
            None
        };

        let oracle_name_ast = assignment.next().unwrap();
        let oracle_name = oracle_name_ast.as_str();
        let oracle_name_span = oracle_name_ast.as_span();

        let dst_pkg_inst_name_ast = assignment.next().unwrap();
        let dst_pkg_inst_name = dst_pkg_inst_name_ast.as_str();
        let dst_pkg_inst_name_span = dst_pkg_inst_name_ast.as_span();

        // look up destination package instance
        let (dst_offset, dst_inst) =
            ctx.get_pkg_instance(dst_pkg_inst_name)
                .ok_or(UndefinedPackageInstanceError {
                    source_code: ctx.named_source(),
                    at: (dst_pkg_inst_name_span.start()..dst_pkg_inst_name_span.end()).into(),
                    pkg_inst_name: dst_pkg_inst_name.to_string(),
                    in_game: ctx.game_name.to_string(),
                })?;

        // look up authorative oracle signature from destination package instance
        let oracle_sig = dst_inst
            .pkg
            .oracles
            .iter()
            .find(|oracle_def| oracle_def.sig.name == oracle_name)
            .ok_or(UndefinedOracleError {
                source_code: ctx.named_source(),
                at: (oracle_name_span.start()..oracle_name_span.end()).into(),
                oracle_name: oracle_name.to_string(),
            })?
            .sig
            .clone();

        // make the signature use the constants from the game, not the package
        let oracle_sig = dst_inst.instantiate_oracle_signature(oracle_sig);

        exports.push(Export::new(dst_offset, oracle_sig, alias));
    }

    Ok(exports)
}

/// parses the oracle wiring assignment list for the package instance with index `source_pkgidx`.
fn handle_edges_compose_assign_list(
    ctx: &mut ParseGameContext,
    ast: Pair<Rule>,
    source_pkgidx: usize,
) -> Result<Vec<Edge>, ParseGameError> {
    // compose_assign_list = { compose_assign ~ ( "," ~ compose_assign )* ~ ","? }
    assert_eq!(ast.as_rule(), Rule::compose_assign_list);

    let mut edges = vec![];

    // Iterate over the assignment pairs
    for assignment in ast.into_inner() {
        // compose_assign = { compose_assign_modifier? ~ identifier ~ ":" ~ identifier }
        assert_eq!(assignment.as_rule(), Rule::compose_assign);

        let assignment_span = assignment.as_span();
        let assignment = assignment.into_inner().next().unwrap();
        let aliased = assignment.as_rule() == Rule::compose_assign_alias;
        let mut assignment = assignment.into_inner();

        let (alias, alias_span) = if aliased {
            let alias_name_ast = assignment.next().unwrap();
            let alias_name = alias_name_ast.as_str();
            let alias_name_span = alias_name_ast.as_span();
            (Some(alias_name.to_string()), Some(alias_name_span))
        } else {
            (None, None)
        };

        let oracle_name_ast = assignment.next().unwrap();
        let oracle_name = oracle_name_ast.as_str();
        let oracle_name_span = oracle_name_ast.as_span();

        let dst_pkg_inst_name_ast = assignment.next().unwrap();
        let dst_pkg_inst_name = dst_pkg_inst_name_ast.as_str();
        let dst_pkg_inst_name_span = dst_pkg_inst_name_ast.as_span();

        // look up destination package instance
        let (dst_offset, dst_inst) =
            ctx.get_pkg_instance(dst_pkg_inst_name)
                .ok_or(UndefinedPackageInstanceError {
                    source_code: ctx.named_source(),
                    at: (dst_pkg_inst_name_span.start()..dst_pkg_inst_name_span.end()).into(),
                    pkg_inst_name: dst_pkg_inst_name.to_string(),
                    in_game: ctx.game_name.to_string(),
                })?;

        // fail if imported edge is not assigned
        let (src_pkg_inst, _) = &ctx.instances[source_pkgidx];
        let import_name = if let Some(ref alias) = alias {
            alias
        } else {
            oracle_name
        };
        let import_span = if let Some(alias_span) = alias_span {
            alias_span
        } else {
            oracle_name_span
        };
        let (src_oracle_sig, _span) = src_pkg_inst
            .pkg
            .imports
            .iter()
            .find(|(osig, _)| import_name == osig.name)
            .ok_or_else(|| {
                ParseGameError::UnusedEdge(UnusedEdgeError {
                    source_code: ctx.named_source(),
                    at: (import_span.start()..import_span.end()).into(),
                    pkg_inst_name: src_pkg_inst.name.clone(),
                    pkg_name: src_pkg_inst.pkg.name.clone(),
                    oracle_name: oracle_name.to_string(),
                    game_name: ctx.game_name.to_string(),
                })
            })?;

        // look up authorative oracle signature from destination package instance
        let dst_oracle_sig = dst_inst
            .pkg
            .oracles
            .iter()
            .find(|oracle_def| oracle_def.sig.name == oracle_name)
            .ok_or(UndefinedOracleError {
                source_code: ctx.named_source(),
                at: (oracle_name_span.start()..oracle_name_span.end()).into(),
                oracle_name: oracle_name.to_string(),
            })?
            .sig
            .clone();

        // make the signature use the constants from the game, not the package
        let dst_oracle_sig = dst_inst.instantiate_oracle_signature(dst_oracle_sig);
        let src_oracle_sig = src_pkg_inst.instantiate_oracle_signature(src_oracle_sig.clone());

        if !dst_oracle_sig.types_match(&src_oracle_sig) {
            dbg!(src_oracle_sig);
            dbg!(dst_oracle_sig);
            return Err(ParseGameError::ConnectedOraclesDontMatch(
                OracleSigMismatchError {
                    source_code: ctx.named_source(),
                    at: (assignment_span.start()..assignment_span.end()).into(),
                    oracle_name: oracle_name.to_string(),
                    src_pkg_inst_name: src_pkg_inst.name.to_string(),
                    dst_pkg_inst_name: dst_pkg_inst_name.to_string(),
                },
            ));
        }

        let found_duplicate_edge = edges
            .iter()
            .any(|edge: &Edge| edge.from() == source_pkgidx && edge.sig().name == oracle_name);

        if found_duplicate_edge {
            return Err(DuplicateEdgeDefinitionError {
                source_code: ctx.named_source(),
                at: (oracle_name_span.start()..oracle_name_span.end()).into(),
                pkg_inst_name: src_pkg_inst.name.to_string(),
                oracle_name: oracle_name.to_string(),
                game_name: ctx.game_name.to_string(),
            }
            .into());
        }

        edges.push(Edge::new(source_pkgidx, dst_offset, dst_oracle_sig, alias));
    }

    Ok(edges)
}

use crate::util::scope::{Declaration, Scope};

fn handle_types_def_list(
    ctx: &mut ParseGameContext,
    ast: Pair<Rule>,
) -> Result<Vec<(String, Type)>, ParseGameError> {
    ast.into_inner()
        .map(|pair_ast| {
            let mut inner = pair_ast.into_inner();
            let name = inner.next().unwrap().as_str();
            let ty = handle_type(&ctx.parse_ctx(), inner.next().unwrap())?;

            Ok((name.to_string(), ty))
        })
        .collect()
}

pub(crate) fn handle_instance_assign_list(
    ctx: &mut ParseGameContext,
    ast: Pair<Rule>,
    pkg_inst_name: &str,
    pkg: &Package,
) -> Result<
    (
        Vec<(PackageConstIdentifier, Expression)>,
        Vec<(String, Type)>,
    ),
    ParseGameError,
> {
    debug_assert_matches!(ast.as_rule(), Rule::instance_assign_list);
    let span = ast.as_span();
    let mut params = vec![];
    let mut types = vec![];

    for elem in ast.into_inner() {
        match elem.as_rule() {
            Rule::params_def => {
                if let Some(params_def_list) = elem.into_inner().next() {
                    let defs =
                        handle_game_params_def_list(ctx, pkg, pkg_inst_name, params_def_list)?;
                    params.extend(defs.into_iter().map(|(name, value)| {
                        (
                            PackageConstIdentifier {
                                pkg_name: pkg.name.to_string(),
                                name,
                                ty: value.get_type(),
                                // we don't resolve it here yet, so we can easily find it when
                                // searching this list when we don't have the value yet.
                                game_name: None,
                                game_assignment: None,
                                pkg_inst_name: None,
                                game_inst_name: None,
                                theorem_name: None,
                            },
                            value,
                        )
                    }))
                }
            }
            Rule::types_def => {
                let mut defs = handle_types_def_list(ctx, elem.into_inner().next().unwrap())?;
                types.append(&mut defs);
            }
            _ => unreachable!("{:#?}", elem),
        }
    }

    let missing_params_vec: Vec<_> = pkg
        .params
        .iter()
        .filter_map(|(name, _, _)| {
            if params.iter().any(|(p, _)| &p.name == name) {
                None
            } else {
                Some(name.clone())
            }
        })
        .collect();
    if !missing_params_vec.is_empty() {
        let missing_params = missing_params_vec.iter().join(", ");
        return Err(MissingPackageParameterDefinitionError {
            source_code: ctx.named_source(),
            at: (span.start()..span.end()).into(),
            pkg_name: pkg.name.clone(),
            pkg_inst_name: pkg_inst_name.to_string(),
            missing_params_vec,
            missing_params,
        }
        .into());
    }

    Ok((params, types))
}

pub(crate) fn handle_instance_decl<'src>(
    ctx: &mut ParseGameContext<'src>,
    ast: Pair<'src, Rule>,
) -> Result<(), ParseGameError> {
    debug_assert_matches!(ast.as_rule(), Rule::instance_decl);
    let span = ast.as_span();

    let mut inner = ast.into_inner();
    let pkg_inst_name_ast = inner.next().unwrap();
    debug_assert_matches!(pkg_inst_name_ast.as_rule(), Rule::identifier);
    let pkg_inst_name = pkg_inst_name_ast.as_str();

    let pkg_name_ast = inner.next().unwrap();
    let pkg_name = pkg_name_ast.as_str();
    let pkg_name_span = pkg_name_ast.as_span();

    let pkg = ctx
        .pkgs
        .get(pkg_name)
        .ok_or(ParseGameError::UndefinedPackage(UndefinedPackageError {
            source_code: ctx.named_source(),
            at: (pkg_name_span.start()..pkg_name_span.end()).into(),
            pkg_name: pkg_name.to_string(),
        }))?;

    let instance_assign_ast = inner.next().unwrap();
    let (mut param_list, type_list) =
        handle_instance_assign_list(ctx, instance_assign_ast, pkg_inst_name, pkg)?;

    param_list.sort();

    // check that const param lists match
    let mut typed_params: Vec<_> = param_list
        .iter()
        .map(|(pkg_param, expr)| (pkg_param.ident(), expr.get_type()))
        .collect();
    typed_params.sort();

    let missing_params: Vec<_> = pkg
        .params
        .iter()
        .filter(|&(specd_name, _, _)| {
            // only items, that are not in the defined list
            // i.e. "all not equals"
            typed_params
                .iter()
                .all(|(defined_name, _)| specd_name != defined_name)
        })
        .collect();

    if !missing_params.is_empty() {
        panic!("found missing params: {missing_params:?}");
    }

    /* we currently don't handle type parameters
        // check that type param lists match
        let mut assigned_types: Vec<_> = type_list
            .iter()
            .map(|(pkg_type, _)| pkg_type)
            .cloned()
            .collect();
        assigned_types.sort();

        let mut pkg_types: Vec<_> = pkg.types.iter().map(|(ty, _span)| ty.clone()).collect();
        pkg_types.sort();

        if assigned_types != pkg_types {
            println!("assigned: {assigned_types:?}");
            println!("pkg:      {pkg_types:?}");
            // TODO include the difference in here
            return Err(error::SpanError::new_with_span(
                error::Error::TypeParameterMismatch {
                    game_name: ctx.game_name.to_string(),
                    pkg_name: pkg_name.to_string(),
                    pkg_inst_name: pkg_inst_name.to_string(),
                },
                span,
            ));
        }
    */

    let pkg_inst = PackageInstance::new(pkg_inst_name, ctx.game_name, pkg, param_list, type_list);
    ctx.add_pkg_instance(pkg_inst, span);

    Ok(())
}
