// SPDX-License-Identifier: MIT OR Apache-2.0

use itertools::Itertools;
use std::collections::HashMap;

use crate::{
    expressions::Expression,
    gamehops::conjecture::Conjecture,
    gamehops::equivalence::Equivalence,
    gamehops::hybrid::Hybrid,
    gamehops::reduction::Assumption,
    gamehops::GameHop,
    identifier::{
        game_ident::GameConstIdentifier,
        theorem_ident::{TheoremConstIdentifier, TheoremIdentifier::Const},
        Identifier,
    },
    package::{Composition, Package},
    parser::{
        error::{
            AssumptionMappingContainsDifferentPackagesError,
            AssumptionMappingDuplicatePackageInstanceError,
            AssumptionMappingLeftGameInstanceIsNotFromAssumption,
            ReductionContainsDifferentPackagesError, UnprovenTheoremError,
        },
        Rule,
    },
    proof::Proof,
    theorem::{Claim, GameInstance, Theorem},
    types::Type,
    util::scope::{Declaration, Error as ScopeError, Scope},
};

use miette::{Diagnostic, NamedSource};
use pest::{
    iterators::{Pair, Pairs},
    Span,
};
use thiserror::Error;

use super::{
    ast::GameInstanceName,
    common::{self, HandleTypeError},
    error::{
        AssumptionExportsNotSufficientError, AssumptionMappingMissesPackageInstanceError,
        AssumptionMappingParameterMismatchError,
        AssumptionMappingRightGameInstanceIsFromAssumption, DuplicateGameParameterDefinitionError,
        InvalidGameInstanceInReductionError, MissingGameParameterDefinitionError,
        NoSuchGameParameterError, ReductionInconsistentAssumptionBoundaryError,
        ReductionPackageInstanceParameterMismatchError, UndefinedAssumptionError,
        UndefinedGameError, UndefinedGameInstanceError, UndefinedPackageInstanceError,
    },
    package::ParseExpressionError,
    ParseContext,
};

#[derive(Debug)]
pub(crate) struct ParseTheoremContext<'a> {
    pub file_name: &'a str,
    pub file_content: &'a str,
    pub scope: Scope,

    pub types: Vec<String>,

    pub theorem_name: &'a str,

    pub consts: HashMap<String, Type>,
    pub instances: Vec<GameInstance>,
    pub instances_table: HashMap<String, (usize, GameInstance)>,
    pub assumptions: Vec<Assumption>,
    pub propositions: Vec<Proof<'a>>,
    pub game_hops: Vec<GameHop<'a>>,
}

impl<'a> ParseContext<'a> {
    fn theorem_context(self, theorem_name: &'a str) -> ParseTheoremContext<'a> {
        let Self {
            file_name,
            file_content,
            scope,
            types,
        } = self;

        ParseTheoremContext {
            file_name,
            file_content,
            theorem_name,

            scope,

            consts: HashMap::new(),
            types,

            instances: vec![],
            instances_table: HashMap::new(),
            assumptions: vec![],
            propositions: vec![],
            game_hops: vec![],
        }
    }
}

impl<'a> ParseTheoremContext<'a> {
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

impl ParseTheoremContext<'_> {
    fn declare(&mut self, name: &str, clone: Declaration) -> Result<(), ScopeError> {
        self.scope.declare(name, clone)
    }
    // TODO: check dupes here?

    fn add_game_instance(&mut self, game_inst: GameInstance) {
        let offset = self.instances.len();
        self.instances.push(game_inst.clone());
        self.instances_table
            .insert(game_inst.name().to_string(), (offset, game_inst));
    }

    pub(crate) fn game_instance(&self, name: &str) -> Option<(usize, &GameInstance)> {
        self.instances_table
            .get(name)
            .map(|(offset, game_inst)| (*offset, game_inst))
    }

    // TODO: check dupes here?
    fn add_const(&mut self, name: String, ty: Type) {
        self.consts.insert(name, ty);
    }
}

#[derive(Debug, Error, Diagnostic)]
pub enum ParseTheoremError {
    #[diagnostic(transparent)]
    #[error(transparent)]
    ParseExpression(#[from] ParseExpressionError),

    #[diagnostic(transparent)]
    #[error(transparent)]
    UndefinedGame(#[from] UndefinedGameError),

    #[diagnostic(transparent)]
    #[error(transparent)]
    UndefinedPackageInstance(#[from] UndefinedPackageInstanceError),

    #[diagnostic(transparent)]
    #[error(transparent)]
    UndefinedGameInstance(#[from] UndefinedGameInstanceError),

    #[diagnostic(transparent)]
    #[error(transparent)]
    UndefinedAssumption(#[from] UndefinedAssumptionError),

    #[diagnostic(transparent)]
    #[error(transparent)]
    AssumptionMappingLeftGameInstanceIsNotFromAssumption(
        #[from] AssumptionMappingLeftGameInstanceIsNotFromAssumption,
    ),

    #[diagnostic(transparent)]
    #[error(transparent)]
    AssumptionMappingRightGameInstanceIsFromAssumption(
        #[from] AssumptionMappingRightGameInstanceIsFromAssumption,
    ),

    #[diagnostic(transparent)]
    #[error(transparent)]
    DuplicateGameParameterDefinition(#[from] DuplicateGameParameterDefinitionError),

    #[diagnostic(transparent)]
    #[error(transparent)]
    MissingGameParameterDefinition(#[from] MissingGameParameterDefinitionError),

    #[diagnostic(transparent)]
    #[error(transparent)]
    NoSuchGameParameter(#[from] NoSuchGameParameterError),

    #[diagnostic(transparent)]
    #[error(transparent)]
    HandleType(#[from] HandleTypeError),

    #[diagnostic(transparent)]
    #[error(transparent)]
    UnprovenTheorem(#[from] UnprovenTheoremError),

    #[diagnostic(transparent)]
    #[error(transparent)]
    AssumptionMappingContainsDifferentPackages(
        #[from] AssumptionMappingContainsDifferentPackagesError,
    ),

    #[diagnostic(transparent)]
    #[error(transparent)]
    AssumptionMappingParameterMismatch(#[from] AssumptionMappingParameterMismatchError),

    #[diagnostic(transparent)]
    #[error(transparent)]
    AssumptionMappingDuplicatePackageInstance(
        #[from] AssumptionMappingDuplicatePackageInstanceError,
    ),

    #[diagnostic(transparent)]
    #[error(transparent)]
    AssumptionMappingMissesPackageInstance(#[from] AssumptionMappingMissesPackageInstanceError),

    #[diagnostic(transparent)]
    #[error(transparent)]
    ReductionContainsDifferentPackages(#[from] ReductionContainsDifferentPackagesError),

    #[diagnostic(transparent)]
    #[error(transparent)]
    ReductionInconsistentAssumptionBoundary(#[from] ReductionInconsistentAssumptionBoundaryError),

    #[diagnostic(transparent)]
    #[error(transparent)]
    ReductionPackageInstanceParameterMismatch(
        #[from] ReductionPackageInstanceParameterMismatchError,
    ),

    #[diagnostic(transparent)]
    #[error(transparent)]
    AssumptionExportsNotSufficient(#[from] AssumptionExportsNotSufficientError),

    #[diagnostic(transparent)]
    #[error(transparent)]
    InvalidGameInstanceInReduction(#[from] InvalidGameInstanceInReductionError),

    #[diagnostic(transparent)]
    #[error(transparent)]
    ScopeError(#[from] ScopeError),
}

pub fn handle_theorem<'a>(
    file_name: &'a str,
    file_content: &'a str,
    ast: Pair<'a, Rule>,
    pkgs: HashMap<String, Package>,
    games: HashMap<String, Composition>,
) -> Result<Theorem<'a>, ParseTheoremError> {
    let mut iter = ast.into_inner();
    let theorem_name = iter.next().unwrap().as_str();
    let theorem_ast = iter.next().unwrap();

    let ctx = ParseContext::new(file_name, file_content);
    let mut ctx = ctx.theorem_context(theorem_name);
    ctx.scope.enter();

    for ast in theorem_ast.into_inner() {
        match ast.as_rule() {
            Rule::const_decl => {
                let (const_name, ty) = common::handle_const_decl(&ctx.parse_ctx(), ast)?;
                let clone = Declaration::Identifier(Identifier::TheoremIdentifier(Const(
                    TheoremConstIdentifier {
                        theorem_name: theorem_name.to_string(),
                        name: const_name.clone(),
                        ty: ty.clone(),
                        inst_info: None,
                    },
                )));
                ctx.declare(&const_name, clone)?;
                ctx.add_const(const_name, ty);
            }
            Rule::assumptions => {
                handle_assumptions(&mut ctx, ast.into_inner())?;
            }
            Rule::propositions => {
                handle_propositions(&mut ctx, ast.into_inner())?;
            }
            Rule::game_hops => {
                handle_game_hops(&mut ctx, ast.into_inner())?;
            }
            Rule::instance_decl => {
                handle_instance_decl(&mut ctx, ast, &games)?;
            }
            Rule::hybrid_instance_decl => {
                handle_hybrid_instance_decl(&mut ctx, ast, &games)?;
            }
            otherwise => unreachable!("found {:?} in theorem", otherwise),
        }
    }

    let ParseTheoremContext {
        theorem_name,
        consts,
        instances,
        assumptions,
        propositions,
        game_hops,
        ..
    } = ctx;

    if propositions.is_empty() {
        log::warn!("No propositions defined, only verifying gamehops");
    }

    let mut consts: Vec<_> = consts.into_iter().collect();
    consts.sort();

    Ok(Theorem {
        name: theorem_name.to_string(),
        consts,
        instances,
        assumptions,
        proofs: propositions,
        game_hops,
        pkgs: pkgs.into_values().collect(),
    })
}

fn handle_instance_decl<'a>(
    ctx: &mut ParseTheoremContext<'a>,
    ast: Pair<'a, Rule>,
    games: &HashMap<String, Composition>,
) -> Result<(), ParseTheoremError> {
    let mut ast = ast.into_inner();

    let game_inst_name = ast.next().unwrap().as_str().to_string();
    let game_name_ast = ast.next().unwrap();
    let game_name_span = game_name_ast.as_span();
    let game_name = game_name_ast.as_str();
    let body_ast = ast.next().unwrap();

    let game = games.get(game_name).ok_or(UndefinedGameError {
        source_code: ctx.named_source(),
        at: (game_name_span.start()..game_name_span.end()).into(),
        game_name: game_name.to_string(),
    })?;

    let (types, consts) = handle_instance_assign_list(ctx, &game_inst_name, game, body_ast)?;

    let consts_as_ident = consts
        .iter()
        .map(|(ident, expr)| (ident.clone(), expr.clone()))
        .collect();

    // println!("printing constant assignment in the parser:");
    // println!("  {consts_as_ident:#?}");

    let game_inst = GameInstance::new(
        game_inst_name,
        ctx.theorem_name.to_string(),
        game.clone(),
        types,
        consts_as_ident,
    );
    ctx.add_game_instance(game_inst);

    Ok(())
}

fn handle_hybrid_instance_decl<'a>(
    ctx: &mut ParseTheoremContext<'a>,
    ast: Pair<'a, Rule>,
    games: &HashMap<String, Composition>,
) -> Result<(), ParseTheoremError> {
    ctx.scope.enter();

    if !ctx.consts.contains_key("hybrid$loop") {
        ctx.consts.insert("hybrid$loop".to_string(), Type::Integer);
    }

    let mut ast = ast.into_inner();

    let game_inst_name = ast.next().unwrap().as_str().to_string();

    let loop_var_ast = ast.next().unwrap();
    let _loop_var_span = loop_var_ast.as_span();
    let loop_var_name = loop_var_ast.as_str();
    let clone = Declaration::Identifier(Identifier::TheoremIdentifier(Const(
        TheoremConstIdentifier {
            theorem_name: ctx.theorem_name.to_string(),
            name: "hybrid$loop".to_string(),
            ty: Type::Integer,
            inst_info: None,
        },
    )));
    ctx.declare(loop_var_name, clone)?;

    let bit_var_ast = ast.next().unwrap();
    let _bit_var_span = bit_var_ast.as_span();
    let bit_var_name = bit_var_ast.as_str();
    let clone = Declaration::Identifier(Identifier::TheoremIdentifier(Const(
        TheoremConstIdentifier {
            theorem_name: ctx.theorem_name.to_string(),
            name: "hybrid$bit".to_string(),
            ty: Type::Boolean,
            inst_info: None,
        },
    )));
    ctx.declare(bit_var_name, clone)?;

    let game_name_ast = ast.next().unwrap();
    let game_name_span = game_name_ast.as_span();
    let game_name = game_name_ast.as_str();

    let body_ast = ast.next().unwrap();

    let game = games.get(game_name).ok_or(UndefinedGameError {
        source_code: ctx.named_source(),
        at: (game_name_span.start()..game_name_span.end()).into(),
        game_name: game_name.to_string(),
    })?;

    let (types, consts) = handle_instance_assign_list(ctx, &game_inst_name, game, body_ast)?;

    let (hybrid_const, consts_as_ident): (Vec<_>, Vec<_>) = consts
        .iter()
        .map(|(ident, expr)| (ident.clone(), expr.clone()))
        .partition(|(ident, _expr)| ident.name == loop_var_name || ident.name == bit_var_name);
    let loopvar_const = hybrid_const
        .iter()
        .find(|(ident, _expr)| ident.name == loop_var_name);
    let bitvar_const = hybrid_const
        .iter()
        .find(|(ident, _expr)| ident.name == bit_var_name);

    let mut patched_consts = consts_as_ident.clone();
    if let Some(loopvar_const) = loopvar_const {
        patched_consts.push((loopvar_const.0.clone(), loopvar_const.1.clone()))
    }
    if let Some(bitvar_const) = bitvar_const {
        patched_consts.push((
            bitvar_const.0.clone(),
            Expression::BooleanLiteral("false".to_string()),
        ))
    }
    let game_inst = GameInstance::new(
        format!("{game_inst_name}$false$"),
        ctx.theorem_name.to_string(),
        game.clone(),
        types.clone(),
        patched_consts,
    );
    ctx.add_game_instance(game_inst);

    let mut patched_consts = consts_as_ident.clone();
    if let Some(loopvar_const) = loopvar_const {
        patched_consts.push((loopvar_const.0.clone(), loopvar_const.1.clone()))
    }
    if let Some(bitvar_const) = bitvar_const {
        patched_consts.push((
            bitvar_const.0.clone(),
            Expression::BooleanLiteral("true".to_string()),
        ))
    }
    let game_inst = GameInstance::new(
        format!("{game_inst_name}$true$"),
        ctx.theorem_name.to_string(),
        game.clone(),
        types.clone(),
        patched_consts,
    );
    ctx.add_game_instance(game_inst);

    let mut patched_consts = consts_as_ident;
    if let Some(loopvar_const) = loopvar_const {
        patched_consts.push((
            loopvar_const.0.clone(),
            Expression::Add(
                Box::new(loopvar_const.1.clone()),
                Box::new(Expression::IntegerLiteral(1)),
            ),
        ))
    }
    if let Some(bitvar_const) = bitvar_const {
        patched_consts.push((
            bitvar_const.0.clone(),
            Expression::BooleanLiteral("false".to_string()),
        ))
    }
    let game_inst = GameInstance::new(
        format!("{game_inst_name}$false$+"),
        ctx.theorem_name.to_string(),
        game.clone(),
        types,
        patched_consts,
    );
    ctx.add_game_instance(game_inst);

    ctx.scope.leave();

    Ok(())
}

fn handle_instance_assign_list(
    ctx: &ParseTheoremContext,
    game_inst_name: &str,
    game: &Composition,
    ast: Pair<Rule>,
) -> Result<(Vec<(String, Type)>, Vec<(GameConstIdentifier, Expression)>), ParseTheoremError> {
    let span = ast.as_span();
    let ast = ast.into_inner();

    let types = vec![];
    let mut consts = vec![];

    for ast in ast {
        match ast.as_rule() {
            Rule::types_def => {
                //let ast = ast.into_inner().next().unwrap();
                //types.extend(common::handle_types_def_list(ast, inst_name, file_name)?);
            }
            Rule::params_def => {
                if let Some(ast) = ast.into_inner().next() {
                    let defs =
                        common::handle_theorem_params_def_list(ctx, game, game_inst_name, ast)?;

                    consts.extend(defs.into_iter().map(|(name, value)| {
                        (
                            GameConstIdentifier {
                                game_name: game.name.to_string(),
                                name,
                                ty: value.get_type(),
                                assigned_value: Some(Box::new(value.clone())),
                                inst_info: None,
                                game_inst_name: Some(game_inst_name.to_string()),
                                theorem_name: Some(ctx.theorem_name.to_string()),
                            },
                            value,
                        )
                    }));
                }
            }
            otherwise => {
                unreachable!("unexpected {:?} at {:?}", otherwise, ast.as_span())
            }
        }
    }

    let missing_params_vec: Vec<_> = game
        .consts
        .iter()
        .filter_map(|(name, _)| {
            if consts.iter().any(|(p, _)| &p.name == name) {
                None
            } else {
                Some(name.clone())
            }
        })
        .collect();

    if !missing_params_vec.is_empty() {
        let missing_params = missing_params_vec.iter().join(", ");
        return Err(MissingGameParameterDefinitionError {
            source_code: ctx.named_source(),
            at: (span.start()..span.end()).into(),
            game_name: game.name.clone(),
            game_inst_name: game_inst_name.to_string(),
            missing_params_vec,
            missing_params,
        }
        .into());
    }

    Ok((types, consts))
}

fn handle_assumptions(
    ctx: &mut ParseTheoremContext,
    ast: Pairs<Rule>,
) -> Result<(), ParseTheoremError> {
    for pair in ast {
        let ((name, _), (left_name, left_name_span), (right_name, right_name_span)) =
            handle_string_triplet(&mut pair.into_inner());

        ctx.game_instance(&left_name)
            .ok_or(UndefinedGameInstanceError {
                source_code: ctx.named_source(),
                at: (left_name_span.start()..left_name_span.end()).into(),
                game_inst_name: left_name.clone(),
            })?;

        if ctx.game_instance(&right_name).is_none() {
            return Err(UndefinedGameInstanceError {
                source_code: ctx.named_source(),
                at: (right_name_span.start()..right_name_span.end()).into(),
                game_inst_name: right_name.clone(),
            }
            .into());
        }

        ctx.assumptions.push(Assumption {
            name,
            left_name,
            right_name,
        })
    }

    Ok(())
}

fn handle_propositions(
    ctx: &mut ParseTheoremContext,
    ast: Pairs<Rule>,
) -> Result<(), ParseTheoremError> {
    for pair in ast {
        let span = pair.as_span();
        let ((name, _), (left_name, left_name_span), (right_name, right_name_span)) =
            handle_string_triplet(&mut pair.into_inner());

        ctx.game_instance(&left_name)
            .ok_or(UndefinedGameInstanceError {
                source_code: ctx.named_source(),
                at: (left_name_span.start()..left_name_span.end()).into(),
                game_inst_name: left_name.clone(),
            })?;

        if ctx.game_instance(&right_name).is_none() {
            return Err(UndefinedGameInstanceError {
                source_code: ctx.named_source(),
                at: (right_name_span.start()..right_name_span.end()).into(),
                game_inst_name: right_name.clone(),
            }
            .into());
        }

        let proof = Proof::try_new(
            &ctx.instances,
            &ctx.game_hops,
            name.clone(),
            left_name,
            right_name,
        )
        .ok_or(UnprovenTheoremError {
            source_code: ctx.named_source(),
            at: (span.start()..span.end()).into(),
            theorem_name: name,
        })?;
        ctx.propositions.push(proof)
    }

    Ok(())
}

fn handle_game_hops<'a>(
    ctx: &mut ParseTheoremContext<'a>,
    ast: Pairs<'a, Rule>,
) -> Result<(), ParseTheoremError> {
    for hop_ast in ast {
        let game_hop = match hop_ast.as_rule() {
            Rule::conjecture => handle_conjecture(ctx, hop_ast)?,
            Rule::equivalence => handle_equivalence(ctx, hop_ast)?,
            Rule::hybrid => handle_hybrid(ctx, hop_ast)?,
            Rule::reduction => super::reduction::handle_reduction(ctx, hop_ast)?,
            otherwise => unreachable!("found {:?} in game_hops", otherwise),
        };
        ctx.game_hops.push(game_hop)
    }

    Ok(())
}

pub(crate) fn handle_hybrid<'a>(
    ctx: &mut ParseTheoremContext<'a>,
    ast: Pair<'a, Rule>,
) -> Result<GameHop<'a>, ParseTheoremError> {
    let mut ast = ast.into_inner();

    let hybrid_name_ast = ast.next().unwrap();
    let reduction_ast = ast.next().unwrap();
    debug_assert_eq!(reduction_ast.as_rule(), Rule::hybrid_reduction);
    let equivalence_ast = ast.next().unwrap();
    debug_assert_eq!(equivalence_ast.as_rule(), Rule::hybrid_equivalence);

    let left_reduction_name = format!("{}$false$", hybrid_name_ast.as_str());
    let right_reduction_name = format!("{}$true$", hybrid_name_ast.as_str());
    let reduction = super::reduction::handle_reduction_body(
        ctx,
        &left_reduction_name,
        &right_reduction_name,
        hybrid_name_ast.as_span().start()..hybrid_name_ast.as_span().end(),
        reduction_ast.into_inner().next().unwrap(),
        true,
    )?;

    let left_equiv_name = format!("{}$true$", hybrid_name_ast.as_str());
    let right_equiv_name = format!("{}$false$+", hybrid_name_ast.as_str());
    let equivalence = {
        let equivalence_data: Vec<_> = equivalence_ast
            .into_inner()
            .map(handle_equivalence_oracle)
            .collect();

        let trees: Vec<_> = equivalence_data
            .iter()
            .cloned()
            .map(|(oracle_name, _, lemmas)| {
                (
                    oracle_name,
                    lemmas.into_iter().map(Claim::from_tuple).collect(),
                )
            })
            .collect();

        let invariants: Vec<_> = equivalence_data
            .iter()
            .cloned()
            .map(|(oracle_name, inv_paths, _)| (oracle_name, inv_paths))
            .collect();

        if ctx.game_instance(&left_equiv_name).is_none() {
            return Err(UndefinedGameInstanceError {
                source_code: ctx.named_source(),
                at: (hybrid_name_ast.as_span().start()..hybrid_name_ast.as_span().end()).into(),
                game_inst_name: hybrid_name_ast.as_str().to_string(),
            }
            .into());
        }
        if ctx.game_instance(&right_equiv_name).is_none() {
            return Err(UndefinedGameInstanceError {
                source_code: ctx.named_source(),
                at: (hybrid_name_ast.as_span().start()..hybrid_name_ast.as_span().end()).into(),
                game_inst_name: hybrid_name_ast.as_str().to_string(),
            }
            .into());
        }

        Equivalence::new(left_equiv_name, right_equiv_name, invariants, trees)
    };

    Ok(GameHop::Hybrid(Hybrid::new(
        hybrid_name_ast.into(),
        equivalence,
        reduction,
        left_reduction_name,
        right_reduction_name,
    )))
}

pub(crate) fn handle_conjecture<'a>(
    _ctx: &mut ParseTheoremContext<'a>,
    ast: Pair<'a, Rule>,
) -> Result<GameHop<'a>, ParseTheoremError> {
    let mut ast = ast.into_inner();

    let [left_game, right_game]: [GameInstanceName; 2] = handle_identifiers(&mut ast);

    Ok(GameHop::Conjecture(Conjecture::new(left_game, right_game)))
}

fn handle_equivalence<'a>(
    ctx: &mut ParseTheoremContext,
    ast: Pair<'a, Rule>,
) -> Result<GameHop<'a>, ParseTheoremError> {
    let mut ast = ast.into_inner();
    let (left_name, right_name) = handle_string_pair(&mut ast);

    let equivalence_data: Vec<_> = ast.map(handle_equivalence_oracle).collect();

    let trees: Vec<_> = equivalence_data
        .iter()
        .cloned()
        .map(|(oracle_name, _, lemmas)| {
            (
                oracle_name,
                lemmas.into_iter().map(Claim::from_tuple).collect(),
            )
        })
        .collect();

    let invariants: Vec<_> = equivalence_data
        .iter()
        .cloned()
        .map(|(oracle_name, inv_paths, _)| (oracle_name, inv_paths))
        .collect();

    if ctx.game_instance(left_name.as_str()).is_none() {
        return Err(UndefinedGameInstanceError {
            source_code: ctx.named_source(),
            at: (left_name.as_span().start()..left_name.as_span().end()).into(),
            game_inst_name: left_name.as_str().to_string(),
        }
        .into());
    }
    if ctx.game_instance(right_name.as_str()).is_none() {
        return Err(UndefinedGameInstanceError {
            source_code: ctx.named_source(),
            at: (right_name.as_span().start()..right_name.as_span().end()).into(),
            game_inst_name: right_name.as_str().to_string(),
        }
        .into());
    }

    let eq = Equivalence::new(
        left_name.as_str().to_string(),
        right_name.as_str().to_string(),
        invariants,
        trees,
    );

    Ok(GameHop::Equivalence(eq))
}

fn handle_equivalence_oracle(ast: Pair<Rule>) -> (String, Vec<String>, Vec<(String, Vec<String>)>) {
    let mut ast = ast.into_inner();
    let oracle_name = ast.next().unwrap().as_str().to_string();
    let invariant_paths = handle_invariant_spec(next_pairs(&mut ast));
    let lemmas = handle_lemmas_spec(next_pairs(&mut ast));

    (oracle_name, invariant_paths, lemmas)
}

fn handle_invariant_spec(ast: Pairs<Rule>) -> Vec<String> {
    ast.map(|ast| ast.as_str().to_string()).collect()
}

fn handle_lemmas_spec(ast: Pairs<Rule>) -> Vec<(String, Vec<String>)> {
    ast.map(handle_lemma_line).collect()
}

fn handle_lemma_line(ast: Pair<Rule>) -> (String, Vec<String>) {
    let mut ast = ast.into_inner();
    let name = next_str(&mut ast).to_string();
    let deps = ast.map(|dep| dep.as_str().to_string()).collect();

    (name, deps)
}

fn handle_string_triplet<'a>(
    ast: &mut Pairs<'a, Rule>,
) -> ((String, Span<'a>), (String, Span<'a>), (String, Span<'a>)) {
    let mut strs: Vec<_> = ast
        .take(3)
        .map(|str| (str.as_str().to_string(), str.as_span()))
        .collect();

    (strs.remove(0), strs.remove(0), strs.remove(0))
}

pub(crate) fn handle_identifiers<'a, T: crate::parser::ast::Identifier<'a>, const N: usize>(
    ast: &mut Pairs<'a, Rule>,
) -> [T; N] {
    ast.take(N)
        .map(T::from)
        .collect::<Vec<_>>()
        .try_into()
        .unwrap()
}

fn handle_string_pair<'a>(ast: &mut Pairs<'a, Rule>) -> (Pair<'a, Rule>, Pair<'a, Rule>) {
    let [left, right] = ast.take(2).collect::<Vec<_>>().try_into().unwrap();

    (left, right)
}

fn next_pairs<'a>(ast: &'a mut Pairs<Rule>) -> Pairs<'a, Rule> {
    ast.next().unwrap().into_inner()
}

fn next_str<'a>(ast: &'a mut Pairs<Rule>) -> &'a str {
    ast.next().unwrap().as_str()
}
