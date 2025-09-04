use super::{
    common::*,
    error::{
        DuplicateEdgeDefinitionError, DuplicatePackageParameterDefinitionError,
        MissingEdgeForImportedOracleError, MissingPackageParameterDefinitionError,
        NoSuchPackageParameterError, OracleSigMismatchError, UndefinedOracleError,
        UndefinedPackageError, UndefinedPackageInstanceError, UnusedEdgeError,
    },
    package::{handle_expression, ForComp, MultiInstanceIndices, ParsePackageError},
    ParseContext, Rule,
};
use crate::{
    debug_assert_matches,
    expressions::Expression,
    identifier::{
        game_ident::{GameConstIdentifier, GameIdentifier},
        pkg_ident::PackageConstIdentifier,
        Identifier,
    },
    package::{
        Composition, Edge, Export, MultiInstanceEdge, MultiInstanceExport,
        NotSingleInstanceEdgeError, NotSingleInstanceExportError, OracleSig, Package,
        PackageInstance,
    },
    types::Type,
    util::scope::Error as ScopeError,
};
use itertools::Itertools as _;
use miette::{Diagnostic, NamedSource};
use pest::{
    iterators::{Pair, Pairs},
    Span,
};
use std::collections::HashMap;
use std::convert::TryInto;
use std::iter::FromIterator as _;
use thiserror::Error;

#[derive(Debug)]
pub struct ParseGameContext<'a> {
    pub file_name: &'a str,
    pub file_content: &'a str,
    pub game_name: &'a str,
    pub pkgs: &'a HashMap<String, Package>,

    pub scope: Scope,

    pub consts: HashMap<String, Type>,
    pub types: Vec<String>,

    pub instances: Vec<(PackageInstance, Span<'a>)>,
    pub instances_table: HashMap<String, (usize, PackageInstance, Span<'a>)>,

    pub edges: Vec<Edge>,
    pub exports: Vec<Export>,

    pub multi_inst_edges: Vec<MultiInstanceEdge>,
    pub multi_inst_exports: Vec<MultiInstanceExport>,
}

impl<'a> ParseContext<'a> {
    fn game_context(
        self,
        game_name: &'a str,
        pkgs: &'a HashMap<String, Package>,
    ) -> ParseGameContext<'a> {
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

            multi_inst_edges: vec![],
            multi_inst_exports: vec![],
        }
    }
}

impl<'a> ParseGameContext<'a> {
    pub fn named_source(&self) -> NamedSource<String> {
        NamedSource::new(self.file_name, self.file_content.to_string())
    }

    pub fn parse_ctx(&self) -> ParseContext<'a> {
        ParseContext {
            file_name: self.file_name,
            file_content: self.file_content,
            scope: self.scope.clone(),
            types: self.types.clone(),
        }
    }
}

impl<'a> ParseGameContext<'a> {
    fn into_game(self) -> Composition {
        let mut consts = Vec::from_iter(self.consts);
        consts.sort();

        Composition {
            name: self.game_name.to_string(),
            consts,
            pkgs: self.instances.into_iter().map(|(inst, _)| inst).collect(),
            edges: self.edges,
            exports: self.exports,
            multi_inst_edges: self.multi_inst_edges,
            multi_inst_exports: self.multi_inst_exports,

            // this one will be populated in a transform, not in the parser
            split_exports: vec![],
        }
    }

    fn declare(&mut self, name: &str, clone: Declaration) -> Result<(), ScopeError> {
        self.scope.declare(name, clone)
    }
    // TODO: check dupes here?

    fn add_pkg_instance(&mut self, pkg_inst: PackageInstance, span: Span<'a>) {
        let offset = self.instances.len();
        self.instances.push((pkg_inst.clone(), span));
        self.instances_table
            .insert(pkg_inst.name.clone(), (offset, pkg_inst, span));
    }

    fn has_pkg_instance(&self, name: &str) -> bool {
        self.instances_table.contains_key(name)
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
    fn add_export(&mut self, export: Export) {
        self.exports.push(export)
    }

    fn add_multi_inst_edge(&mut self, edge: MultiInstanceEdge) {
        self.multi_inst_edges.push(edge)
    }
    fn add_multi_inst_export(&mut self, export: MultiInstanceExport) {
        self.multi_inst_exports.push(export)
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
    DuplicateEdgeDefinition(#[from] DuplicateEdgeDefinitionError),

    #[diagnostic[transparent]]
    #[error[transparent]]
    ConnectedOraclesDontMatch(#[from] OracleSigMismatchError),
}

pub fn handle_composition(
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
pub fn handle_comp_spec_list<'a>(
    mut ctx: ParseGameContext<'a>,
    ast: Pair<'a, Rule>,
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
            Rule::game_for => {
                handle_for_loop(&mut ctx, comp_spec)?;
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
            let edge_exists = ctx.edges.iter().any(|edge| {
                matches!(edge, Edge(edge_src_offset, _, OracleSig {
                    name: edge_oracle_name,
                    ..
                }) if *edge_src_offset == offset && *edge_oracle_name == import.name)
            });

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

pub fn handle_compose_assign_list_multi_inst(
    ctx: &mut ParseGameContext,
    ast: Pairs<Rule>,
) -> Result<Vec<(String, String, Vec<Expression>)>, ParseGameError> {
    ast.map(|assignment| -> Result<_, ParseGameError> {
        let mut line_builder = (None, None, vec![]);
        for piece in assignment.into_inner() {
            let piece_span = piece.as_span();
            match piece.as_rule() {
                Rule::identifier if line_builder.0.is_none() => {
                    line_builder.0 = Some(piece.as_str().to_string())
                }
                Rule::identifier if line_builder.1.is_none() => {
                    if !ctx.has_pkg_instance(piece.as_str()) {
                        return Err(ParseGameError::UndefinedInstance(
                            UndefinedPackageInstanceError {
                                source_code: ctx.named_source(),
                                at: (piece_span.start()..piece_span.end()).into(),
                                pkg_inst_name: piece.as_str().to_string(),
                                in_game: ctx.game_name.to_string(),
                            },
                        ));
                    }

                    line_builder.1 = Some(piece.as_str().to_string())
                }
                Rule::compose_assign_modifier_with_index => line_builder.2.append(
                    &mut piece
                        .into_inner()
                        .next()
                        .unwrap()
                        .into_inner()
                        .map(|e| {
                            handle_expression(&ctx.parse_ctx(), e, Some(&Type::Integer))
                                .map_err(ParseGameError::ParseExpression)
                        })
                        .collect::<Result<Vec<Expression>, ParseGameError>>()?,
                ),
                _ => unreachable!(),
            }
        }

        Ok((
            line_builder.0.unwrap(),
            line_builder.1.unwrap(),
            line_builder.2,
        ))
        // let mut inner = assignment.into_inner();
        // let oracle_name = inner.next().unwrap().as_str();
        // let dst_inst_name = inner.next().unwrap().as_str();
        //
        // (oracle_name.to_owned(), dst_inst_name.to_owned())
    })
    .collect::<Result<Vec<_>, _>>()
}

/*
#[derive(Debug)]
pub enum ParseGameError {
    UndeclaredInstance(String, FilePosition),
    NoSuchOracleInInstance(String, String, FilePosition),
    ParseExpressionError(super::common::ParseExpressionError),
}

impl std::fmt::Display for ParseGameError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ParseGameError::UndeclaredInstance(inst_name, _) => {
                write!(f, "instance {inst_name:?} not declared")
            }
            ParseGameError::NoSuchOracleInInstance(oracle_name, inst_name, _) => {
                write!(
                    f,
                    "instace {inst_name:?} does not have oracle {oracle_name:?}"
                )
            }
            ParseGameError::ParseExpressionError(err) => {
                write!(f, "error parsing expression: {err}")
            }
        }
    }
}

impl std::error::Error for ParseGameError {}
impl crate::error::LocationError for ParseGameError {
    fn file_pos<'a>(&'a self) -> &'a FilePosition {
        match self {
            ParseGameError::ParseExpressionError(err) => err.file_pos(),
            ParseGameError::UndeclaredInstance(_, file_pos) => file_pos,
            ParseGameError::NoSuchOracleInInstance(_, _, file_pos) => file_pos,
        }
    }
}
*/

pub fn handle_for_loop_body<'a>(
    ctx: &mut ParseGameContext<'a>,
    ast: Pair<'a, Rule>,
) -> Result<(), ParseGameError> {
    for comp_spec in ast.into_inner() {
        match comp_spec.as_rule() {
            Rule::game_for => handle_for_loop(ctx, comp_spec)?,

            Rule::instance_decl => handle_instance_decl_multi_inst(ctx, comp_spec)?,

            Rule::compose_decl_multi_inst => {
                handle_compose_assign_body_list(ctx, comp_spec)?;
            }
            _ => unreachable!(),
        }
    }

    Ok(())
}

pub fn handle_compose_assign_body_list(
    ctx: &mut ParseGameContext,
    ast: Pair<Rule>,
) -> Result<(), ParseGameError> {
    debug_assert!(matches!(
        ast.as_rule(),
        Rule::compose_decl | Rule::compose_decl_multi_inst
    ));

    for body in ast.into_inner() {
        debug_assert!(matches!(
            body.as_rule(),
            Rule::compose_assign_body | Rule::compose_assign_body_multi_inst
        ));

        let mut inner = body.into_inner();
        let src_inst_name_ast = inner.next().unwrap();
        let src_inst_name_span = src_inst_name_ast.as_span();
        let src_inst_name = src_inst_name_ast.as_str();

        let source_instance_idx = if inner.peek().unwrap().as_rule() == Rule::indices_ident {
            inner
                .next()
                .unwrap()
                .into_inner()
                .map(|idx_ident| ctx.scope.lookup_identifier(idx_ident.as_str()).unwrap())
                .collect()
        } else {
            vec![]
        };

        let compose_assign_list_ast = inner.next().unwrap();
        debug_assert_eq!(compose_assign_list_ast.as_rule(), Rule::compose_assign_list);

        if src_inst_name == "adversary" {
            for multi_inst_export in
                handle_export_compose_assign_list_multi_inst(ctx, compose_assign_list_ast)?
            {
                match multi_inst_export.try_into() {
                    Ok(export) => ctx.add_export(export),
                    Err(NotSingleInstanceExportError(multi_export)) => {
                        ctx.add_multi_inst_export(multi_export)
                    }
                }
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

            for multi_instance_edge in handle_edges_compose_assign_list_multi_inst(
                ctx,
                compose_assign_list_ast,
                &source_instance_idx,
                source_pkgidx,
            )? {
                match multi_instance_edge.try_into() {
                    Ok(edge) => ctx.add_edge(edge),
                    Err(NotSingleInstanceEdgeError(multi_edge)) => {
                        ctx.add_multi_inst_edge(multi_edge)
                    }
                }
            }
        }
    }

    Ok(())
}

/// parses the oracle wiring assignment list for the exports.
fn handle_export_compose_assign_list_multi_inst(
    ctx: &mut ParseGameContext,
    ast: Pair<Rule>,
) -> Result<Vec<MultiInstanceExport>, ParseGameError> {
    // compose_assign_list = { compose_assign ~ ( "," ~ compose_assign )* ~ ","? }
    assert_eq!(ast.as_rule(), Rule::compose_assign_list);

    let mut exports = vec![];

    // Iterate over the assignment pairs
    for assignment in ast.into_inner() {
        // compose_assign = { compose_assign_modifier? ~ identifier ~ ":" ~ identifier }
        assert_eq!(assignment.as_rule(), Rule::compose_assign);

        let mut assignment = assignment.into_inner();

        // extract the base information from the parse tree. This is a bit tricky, because we may
        // start with an optional modifier.
        let first = assignment.peek().unwrap();
        let (modifier_ast, oracle_name_ast, dst_pkg_inst_name_ast) = match first.as_rule() {
            Rule::identifier => {
                let oracle_name = assignment.next().unwrap();
                let dst_inst_name = assignment.next().unwrap();
                (None, oracle_name, dst_inst_name)
            }
            Rule::compose_assign_modifier_with_index => {
                // compose_assign_modifier_with_index =  { "with" ~ "index" ~ indices_expr}
                let modifier = assignment.next().unwrap();
                let oracle_name = assignment.next().unwrap();
                let dst_inst_name = assignment.next().unwrap();
                (Some(modifier), oracle_name, dst_inst_name)
            }
            _ => unreachable!(),
        };

        let oracle_name = oracle_name_ast.as_str();
        let oracle_name_span = oracle_name_ast.as_span();
        let dst_pkg_inst_name = dst_pkg_inst_name_ast.as_str();
        let dst_pkg_inst_name_span = dst_pkg_inst_name_ast.as_span();

        // parse the index modifiers. currently we don't use this.
        let dst_inst_idx: Option<Vec<Expression>> = modifier_ast
            .map(|modifier| {
                modifier
                    .into_inner()
                    .next()
                    .unwrap()
                    .into_inner()
                    .map(|idx| handle_expression(&ctx.parse_ctx(), idx, Some(&Type::Integer)))
                    .collect()
            })
            .transpose()?;

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

        assert!(oracle_sig.multi_inst_idx.indices.is_empty());

        // refine the indices (not sure this is correct, but we don't do this now anyway)
        let oracle_sig = match dst_inst_idx.map(MultiInstanceIndices::new) {
            Some(multi_inst_idx) => OracleSig {
                multi_inst_idx,
                ..oracle_sig
            },
            None => oracle_sig,
        };

        // make the signature use the constants from the game, not the package
        let oracle_sig = dst_inst.instantiate_oracle_signature(oracle_sig);

        exports.push(MultiInstanceExport {
            dest_pkgidx: dst_offset,
            oracle_sig,
        });
    }

    Ok(exports)
}

/// parses the oracle wiring assignment list for the package instance with index `source_pkgidx`.
fn handle_edges_compose_assign_list_multi_inst(
    ctx: &mut ParseGameContext,
    ast: Pair<Rule>,
    source_instance_idx: &[Identifier],
    source_pkgidx: usize,
) -> Result<Vec<MultiInstanceEdge>, ParseGameError> {
    // compose_assign_list = { compose_assign ~ ( "," ~ compose_assign )* ~ ","? }
    assert_eq!(ast.as_rule(), Rule::compose_assign_list);

    let mut edges = vec![];

    // Iterate over the assignment pairs
    for assignment in ast.into_inner() {
        // compose_assign = { compose_assign_modifier? ~ identifier ~ ":" ~ identifier }
        assert_eq!(assignment.as_rule(), Rule::compose_assign);

        let assignment_span = assignment.as_span();
        let mut assignment = assignment.into_inner();

        // extract the base information from the parse tree. This is a bit tricky, because we may
        // start with an optional modifier.
        let first = assignment.peek().unwrap();
        let (modifier_ast, oracle_name_ast, dst_pkg_inst_name_ast) = match first.as_rule() {
            Rule::identifier => {
                let oracle_name = assignment.next().unwrap();
                let dst_inst_name = assignment.next().unwrap();
                (None, oracle_name, dst_inst_name)
            }
            Rule::compose_assign_modifier_with_index => {
                // compose_assign_modifier_with_index =  { "with" ~ "index" ~ indices_expr}
                let modifier = assignment.next().unwrap();
                let oracle_name = assignment.next().unwrap();
                let dst_inst_name = assignment.next().unwrap();
                (Some(modifier), oracle_name, dst_inst_name)
            }
            _ => unreachable!(),
        };

        let oracle_name = oracle_name_ast.as_str();
        let oracle_name_span = oracle_name_ast.as_span();
        let dst_pkg_inst_name = dst_pkg_inst_name_ast.as_str();
        let dst_pkg_inst_name_span = dst_pkg_inst_name_ast.as_span();

        // parse the index modifiers. currently we don't use this.
        let dst_inst_idx: Option<Vec<Expression>> = modifier_ast
            .map(|modifier| {
                modifier
                    .into_inner()
                    .next()
                    .unwrap()
                    .into_inner()
                    .map(|idx| handle_expression(&ctx.parse_ctx(), idx, Some(&Type::Integer)))
                    .collect()
            })
            .transpose()?;

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
        let (src_oracle_sig, _span) = src_pkg_inst
            .pkg
            .imports
            .iter()
            .find(|(osig, _)| oracle_name == osig.name)
            .ok_or_else(|| {
                ParseGameError::UnusedEdge(UnusedEdgeError {
                    source_code: ctx.named_source(),
                    at: (oracle_name_span.start()..oracle_name_span.end()).into(),
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

        // refine the indices (not sure this is correct, but we don't do this now anyway)
        let dst_oracle_sig = match dst_inst_idx.map(MultiInstanceIndices::new) {
            Some(multi_inst_idx) => OracleSig {
                multi_inst_idx,
                ..dst_oracle_sig
            },
            None => dst_oracle_sig,
        };

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

        if edges.iter().any(|existing_edge: &MultiInstanceEdge| {
            // TODO: this will probably fail for real multi-instance, handle that later

            existing_edge.source_pkgidx == source_pkgidx
                && existing_edge.oracle_sig.name == oracle_name
        }) {
            return Err(DuplicateEdgeDefinitionError {
                source_code: ctx.named_source(),
                at: (oracle_name_span.start()..oracle_name_span.end()).into(),
                pkg_inst_name: src_pkg_inst.name.to_string(),
                oracle_name: oracle_name.to_string(),
                game_name: ctx.game_name.to_string(),
            }
            .into());
        }

        edges.push(MultiInstanceEdge {
            dest_pkgidx: dst_offset,
            oracle_sig: dst_oracle_sig,
            source_pkgidx,
            source_instance_idx: source_instance_idx.to_vec(),
        });
    }

    Ok(edges)
}

pub fn handle_for_loop<'a>(
    ctx: &mut ParseGameContext<'a>,
    ast: Pair<'a, Rule>,
) -> Result<(), ParseGameError> {
    let mut parsed: Vec<Pair<Rule>> = ast.into_inner().collect();
    let decl_var_name = parsed[0].as_str();
    let lower_bound = handle_expression(&ctx.parse_ctx(), parsed.remove(1), Some(&Type::Integer))?;
    let lower_bound_type = parsed[1].as_str();
    let bound_var_name = parsed[2].as_str();
    let upper_bound_type = parsed[3].as_str();
    let upper_bound = handle_expression(&ctx.parse_ctx(), parsed.remove(4), Some(&Type::Integer))?;
    let body_ast = parsed.remove(4);

    if decl_var_name != bound_var_name {
        todo!("return proper error here")
    }

    let start_comp = match lower_bound_type {
        "<" => ForComp::Lt,
        "<=" => ForComp::Lte,
        _ => unreachable!(),
    };
    let end_comp = match upper_bound_type {
        "<" => ForComp::Lt,
        "<=" => ForComp::Lte,
        _ => unreachable!(),
    };

    let loopvar = crate::identifier::game_ident::GameLoopVarIdentifier {
        game_name: ctx.game_name.to_string(),
        name: decl_var_name.to_string(),
        start: Box::new(lower_bound),
        end: Box::new(upper_bound),
        start_comp,
        end_comp,
        game_inst_name: None,
        theorem_name: None,
        inst_info: None,
    };
    let loopvar = GameIdentifier::LoopVar(loopvar);
    let loopvar = Identifier::GameIdentifier(loopvar);
    let decl = Declaration::Identifier(loopvar);

    ctx.scope.enter();
    ctx.declare(decl_var_name, decl).unwrap();

    let result = handle_for_loop_body(ctx, body_ast);

    ctx.scope.leave();

    result
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

pub fn handle_instance_assign_list(
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

pub fn handle_instance_decl_multi_inst<'a>(
    ctx: &mut ParseGameContext<'a>,
    ast: Pair<'a, Rule>,
) -> Result<(), ParseGameError> {
    let span = ast.as_span();
    let mut inner = ast.into_inner();
    let inst_name = inner.next().unwrap().as_str();
    let game_name = ctx.game_name;

    let indices_ast = inner.next().unwrap();
    let indices = indices_ast
        .into_inner()
        .map(|index_ast| handle_expression(&ctx.parse_ctx(), index_ast, Some(&Type::Integer)))
        .collect::<Result<Vec<_>, _>>()?;

    let pkg_name_ast = inner.next().unwrap();
    let pkg_name_span = pkg_name_ast.as_span();
    let pkg_name = pkg_name_ast.as_str();
    let data = inner.next().unwrap();

    let pkg = ctx.pkgs.get(pkg_name).ok_or(UndefinedPackageError {
        source_code: ctx.named_source(),
        at: (pkg_name_span.start()..pkg_name_span.end()).into(),
        pkg_name: pkg_name.to_string(),
    })?;

    let (mut param_list, type_list) = handle_instance_assign_list(ctx, data, inst_name, pkg)?;

    param_list.sort();

    /* We don't type parameteres currently.
        // check that const param lists match
        let mut typed_params: Vec<_> = param_list
            .iter()
            .map(|(pkg_param, comp_param)| (pkg_param.name.clone(), comp_param.get_type()))
            .collect();
        typed_params.sort();

        let mut pkg_params: Vec<_> = pkg
            .params
            .iter()
            .cloned()
            .map(|(name, ty, _)| (name, ty))
            .collect();
        pkg_params.sort();

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
                    pkg_inst_name: inst_name.to_string(),
                },
                span,
            ));
        }
    */

    let multi_instance_indices = MultiInstanceIndices::new(indices);

    let inst = PackageInstance::new(
        inst_name,
        game_name,
        pkg,
        multi_instance_indices,
        param_list,
        type_list,
    );

    ctx.add_pkg_instance(inst, span);

    /*
        let resolved_inst = match ResolveTypesPackageInstanceTransform.transform_package_instance(&inst)
        {
            Ok((inst, _)) => Ok(inst),
            Err(err) => Err(error::Error::from(err).with_span(span)),
        }?;

        ctx.add_pkg_instance(resolved_inst);
    */

    Ok(())
}

pub fn handle_instance_decl<'a>(
    ctx: &mut ParseGameContext<'a>,
    ast: Pair<'a, Rule>,
) -> Result<(), ParseGameError> {
    debug_assert_matches!(ast.as_rule(), Rule::instance_decl);
    let span = ast.as_span();

    let mut inner = ast.into_inner();
    let pkg_inst_name_ast = inner.next().unwrap();
    debug_assert_matches!(pkg_inst_name_ast.as_rule(), Rule::identifier);
    let pkg_inst_name = pkg_inst_name_ast.as_str();

    let index_or_pkgname = inner.next().unwrap();
    let (multi_instance_indices, pkg_name, pkg_name_span) = match index_or_pkgname.as_rule() {
        // TODO: this is most likely the wrong rule to check against. Write tests!
        Rule::index_id_list => {
            let indices_ast = index_or_pkgname.into_inner();
            let indices: Vec<_> = indices_ast
                .map(|index| handle_expression(&ctx.parse_ctx(), index, Some(&Type::Integer)))
                .collect::<Result<_, _>>()?;

            let pkg_name_ast = inner.next().unwrap();
            (
                MultiInstanceIndices::new(indices),
                pkg_name_ast.as_str(),
                pkg_name_ast.as_span(),
            )
        }
        Rule::identifier => (
            MultiInstanceIndices::empty(),
            index_or_pkgname.as_str(),
            index_or_pkgname.as_span(),
        ),
        _ => unreachable!(),
    };

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

    let pkg_inst = PackageInstance::new(
        pkg_inst_name,
        ctx.game_name,
        pkg,
        multi_instance_indices,
        param_list,
        type_list,
    );
    ctx.add_pkg_instance(pkg_inst, span);

    /*
        match ResolveTypesPackageInstanceTransform.transform_package_instance(&pkg_inst) {
            Ok((pkg_inst, _)) => {
                ctx.add_pkg_instance(pkg_inst);
                Ok(())
            }
            Err(err) => Err(error::Error::from(err).with_span(span)),
        }
    */
    Ok(())
}

pub fn handle_compose_assign_list(ast: Pairs<Rule>) -> Vec<(String, String)> {
    ast.map(|assignment| {
        let mut inner = assignment.into_inner();

        let oracle_name = inner.next().unwrap().as_str();
        let dst_inst_name = inner.next().unwrap().as_str();

        (oracle_name.to_owned(), dst_inst_name.to_owned())
    })
    .collect()
}

pub fn handle_index_id_list(ast: Pair<Rule>) -> Vec<String> {
    assert_eq!(ast.as_rule(), Rule::index_id_list);
    ast.into_inner()
        .map(|ast| ast.as_str().to_string())
        .collect()
}
