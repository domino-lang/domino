// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::expressions::ExpressionKind;
use crate::identifier::game_ident::{GameConstIdentifier, GameIdentifier};
use crate::identifier::pkg_ident::{PackageConstIdentifier, PackageIdentifier};
use crate::identifier::Identifier;
use crate::package::{Composition, Package};
use crate::parser::composition::ParseGameError;
use crate::types::{CountSpec, TypeKind};
use crate::{debug_assert_matches, expressions::Expression, types::Type};

use super::composition::ParseGameContext;
use super::error::{
    DuplicateGameParameterDefinitionError, DuplicatePackageParameterDefinitionError,
    ExpectedExpressionIdentifierError, MissingGameParameterDefinitionError,
    MissingPackageParameterDefinitionError, NoSuchGameParameterError, NoSuchPackageParameterError,
    NoSuchTypeError, ParseNumberError, UndefinedIdentifierError,
};
use super::package::{
    handle_identifier_in_code_rhs, HandleIdentifierRhsError, ParseIdentifierError,
};
use super::theorem::{ParseTheoremContext, ParseTheoremError};
use super::{ParseContext, Rule};

use itertools::Itertools;
use miette::SourceSpan;
use pest::iterators::Pair;

use std::collections::{HashMap, HashSet};

pub(crate) fn handle_countspec(
    ctx: &ParseContext,
    tree: Pair<Rule>,
) -> Result<CountSpec, HandleTypeError> {
    assert_eq!(tree.as_rule(), Rule::countspec);
    if let Some(inner) = tree.into_inner().next() {
        let span = inner.as_span();
        match inner.as_rule() {
            Rule::identifier => {
                let name = inner.as_str();
                let ident = handle_identifier_in_code_rhs(ctx, &inner, name)?;
                Ok(CountSpec::Identifier(Box::new(ident)))
            }
            Rule::num => {
                let num_str = inner.as_str();
                let num = num_str.parse().map_err(|source| ParseNumberError {
                    source_code: ctx.named_source(),
                    at: (span.start()..span.end()).into(),
                    num_str: num_str.to_string(),
                    source,
                })?;
                Ok(CountSpec::Literal(num))
            }
            other => unreachable!("unexpected: {other:?}"),
        }
    } else {
        Ok(CountSpec::Any)
    }
}

#[derive(Debug, thiserror::Error, miette::Diagnostic)]
pub enum HandleTypeError {
    #[error(transparent)]
    #[diagnostic(transparent)]
    NoSuchType(#[from] NoSuchTypeError),

    #[error(transparent)]
    #[diagnostic(transparent)]
    ParseIdentifier(#[from] Box<ParseIdentifierError>),

    #[error(transparent)]
    #[diagnostic(transparent)]
    ParseNumber(#[from] ParseNumberError),

    #[error(transparent)]
    #[diagnostic(transparent)]
    UndefinedIdentifier(#[from] UndefinedIdentifierError),

    #[diagnostic(transparent)]
    #[error(transparent)]
    ExpectedExpressionIdentifier(#[from] ExpectedExpressionIdentifierError),
}

impl From<HandleIdentifierRhsError> for HandleTypeError {
    fn from(value: HandleIdentifierRhsError) -> Self {
        match value {
            HandleIdentifierRhsError::UndefinedIdentifier(err) => Self::UndefinedIdentifier(err),
            HandleIdentifierRhsError::ExpectedExpressionIdentifier(err) => {
                Self::ExpectedExpressionIdentifier(err)
            }
        }
    }
}

pub(crate) fn handle_type(ctx: &ParseContext, ty: Pair<Rule>) -> Result<Type, HandleTypeError> {
    let kind = match ty.as_rule() {
        Rule::type_empty => TypeKind::Empty,
        Rule::type_bool => TypeKind::Boolean,
        Rule::type_integer => TypeKind::Integer,
        Rule::type_string => TypeKind::String,
        Rule::type_maybe => {
            TypeKind::Maybe(Box::new(handle_type(ctx, ty.into_inner().next().unwrap())?))
        }
        Rule::type_bits => TypeKind::Bits(handle_countspec(ctx, ty.into_inner().next().unwrap())?),
        Rule::type_tuple => TypeKind::Tuple(
            ty.into_inner()
                .map(|t| handle_type(ctx, t))
                .collect::<Result<_, _>>()?,
        ),
        Rule::type_table => {
            let mut inner = ty.into_inner();
            let indextype = handle_type(ctx, inner.next().unwrap())?;
            let valuetype = handle_type(ctx, inner.next().unwrap())?;
            TypeKind::Table(Box::new(indextype), Box::new(valuetype))
        }
        Rule::type_fn => {
            let mut inner = ty.into_inner();
            let argtys = inner
                .next()
                .unwrap()
                .into_inner()
                .map(|spec| handle_type(ctx, spec.into_inner().next().unwrap()))
                .collect::<Result<_, _>>()?;
            let ty = handle_type(ctx, inner.next().unwrap())?;
            TypeKind::Fn(argtys, Box::new(ty))
        }
        Rule::type_userdefined => {
            let type_name = ty.as_str();
            if ctx
                .types
                .iter()
                .any(|declared_type| declared_type == type_name)
            {
                TypeKind::UserDefined(ty.as_str().to_string())
            } else {
                let span = ty.as_span();
                return Err(NoSuchTypeError {
                    source_code: ctx.named_source(),
                    at: (span.start()..span.end()).into(),
                    type_name: type_name.to_string(),
                }
                .into());
            }
        }
        _ => {
            unreachable!("{:#?}", ty)
        }
    };

    Ok(Type::from_kind(kind))
}

pub(crate) fn handle_game_params_def_list(
    ctx: &ParseGameContext,
    pkg: &Package,
    pkg_inst_name: &str,
    ast: Pair<Rule>,
) -> std::result::Result<Vec<(String, Expression)>, super::composition::ParseGameError> {
    debug_assert_matches!(ast.as_rule(), Rule::params_def_list);
    let mut defined_params = HashMap::<String, SourceSpan>::new();
    let block_span = ast.as_span();

    // We need to process ints first, so we can rewrite the Bits(<some int>) that contain the name
    // of the const parameter on one side, and the name of the value that is assigned on the other.
    // We first split the two...
    let (ints, others): (Vec<_>, _) = ast
        .into_inner()
        // loop over the parameter definitions
        .map(|inner| {
            let pair_span = inner.as_span();
            let mut inner = inner.into_inner();
            let name_ast = inner.next().unwrap();
            let value_ast = inner.next().unwrap();

            let name_span = name_ast.as_span();
            let name = name_ast.as_str();

            // look up the parameter clone from the package
            let maybe_param_info = pkg.params.iter().find(|(name_, _, _)| name == name_);

            // if it desn't exist, return an error
            let (_, expected_type, _) = maybe_param_info.ok_or(NoSuchPackageParameterError {
                source_code: ctx.named_source(),
                at: (name_span.start()..name_span.end()).into(),
                param_name: name.to_string(),
                pkg_name: pkg.name.clone(),
            })?;

            Ok((pair_span, name_ast, value_ast, expected_type.clone()))
        })
        .partition(
            |res| matches!(res, Ok((_, _, _, ty)) if matches!(ty.kind(), TypeKind::Integer)),
        );

    let mut bits_rewrite_rules = vec![];

    // ... then we parse the ints and add populate a list of rewrite rules
    //     for all the Bits types ...
    let ints: Vec<_> = ints
        .into_iter()
        .map(|res| {
            res.and_then(|(pair_span, name_ast, value_ast, expected_type)| {
                // parse the assigned value, and set the expected type to what the clone
                // prescribes.
                let value = super::package::handle_expression(
                    &ctx.parse_ctx(),
                    value_ast.clone(),
                    Some(&expected_type),
                )?;

                let assigned_countspec = match value.into_kind() {
                    ExpressionKind::Identifier(ident) => CountSpec::Identifier(Box::new(ident)),
                    // TODO:: enforce somehow that this number is not negative
                    ExpressionKind::IntegerLiteral(num) => CountSpec::Literal(num as u64),
                    _ => {
                        //return Err(todo!());
                        todo!()
                    }
                };

                let name: &str = name_ast.as_str();

                bits_rewrite_rules.push((
                    Type::bits(CountSpec::Identifier(Box::new(
                        Identifier::PackageIdentifier(PackageIdentifier::Const(
                            PackageConstIdentifier {
                                pkg_name: pkg.name.clone(),
                                name: name.to_string(),
                                ty: Type::integer(),
                                game_name: None,
                                pkg_inst_name: None,
                                game_inst_name: None,
                                theorem_name: None,
                                game_assignment: None,
                            },
                        )),
                    ))),
                    Type::bits(assigned_countspec),
                ));

                Ok((pair_span, name_ast, value_ast, expected_type))
            })
        })
        .collect();

    // ... then we map the other values to rewrite the types according to the rules defined
    //     above ...
    let others_iter = others.into_iter().map(|res| {
        res.map(|(pair_span, name_ast, value_ast, ty)| {
            (
                pair_span,
                name_ast,
                value_ast,
                ty.rewrite_type(&bits_rewrite_rules),
            )
        })
    });

    // and then we chain the two again and do the rest of the processing
    ints
        .into_iter()
        .chain(others_iter)
        .map(|res: Result<(pest::Span, Pair<Rule>, Pair<Rule>, Type), ParseGameError>| -> Result<(String, Expression), ParseGameError> {
        let (pair_span, name_ast, value_ast, expected_type) = res?;
        let name: &str = name_ast.as_str();
        let name_span: pest::Span = name_ast.as_span();

        // check that the defined parameter hasn't been defined before
        // (insert returns Some(x) if x has been written before)
        if let Some(prev_span) = defined_params.insert(
            name.to_string(),
            (pair_span.start()..pair_span.end()).into(),
        ) {
            Err(DuplicatePackageParameterDefinitionError {
                source_code: ctx.named_source(),
                at: (name_span.start()..name_span.end()).into(),
                other: prev_span,
                param_name: name.to_string(),
                pkg_inst_name: pkg_inst_name.to_string(),
            })?;
        }

        // parse the assigned value, and set the expected type to what the clone
        // prescribes.
        let value =
            super::package::handle_expression(&ctx.parse_ctx(), value_ast, Some(&expected_type))?;

        Ok((name.to_string(), value))
    })
        .collect::<std::result::Result<Vec<_>, super::composition::ParseGameError>>()
        .and_then(|list| {
            let definied_names: HashSet<String> = defined_params.keys().cloned().collect();
            let declared_names: HashSet<String> =
                pkg.params.iter().map(|(name, _, _)| name).cloned().collect();

            let missing_params_vec: Vec<_> = declared_names
                .difference(&definied_names)
                .cloned()
                .collect();
            let missing_params = missing_params_vec.iter().join(", ");

            if !missing_params_vec.is_empty() {
                Err(MissingPackageParameterDefinitionError {
                    source_code: ctx.named_source(),
                    at: (block_span.start()..block_span.end()).into(),
                    pkg_name: pkg.name.clone(),
                    pkg_inst_name: pkg_inst_name.to_string(),
                    missing_params_vec,
                    missing_params,
                }
                .into())
            } else {
                Ok(list)
            }
        })
}

pub(crate) fn handle_theorem_params_def_list(
    ctx: &ParseTheoremContext,
    game: &Composition,
    game_inst_name: &str,
    ast: Pair<Rule>,
) -> Result<Vec<(String, Expression)>, ParseTheoremError> {
    let params = &game.consts;
    let mut defined_params = HashMap::<String, SourceSpan>::new();
    let block_span = ast.as_span();

    // We need to process ints first, so we can rewrite the Bits(<some int>) that contain the name
    // of the const parameter on one side, and the name of the value that is assigned on the other.
    // We first split the two...
    let (ints, others): (Vec<_>, _) = ast
        .into_inner()
        .map(|inner| {
            let pair_span = inner.as_span();
            let mut inner = inner.into_inner();
            let name_ast = inner.next().unwrap();
            let value_ast = inner.next().unwrap();

            let name_span = name_ast.as_span();
            let name = name_ast.as_str();

            // look up the parameter clone from the game
            let maybe_param_info = params.iter().find(|(name_, _)| name == name_);

            // if it desn't exist, return an error
            let (_, expected_type) = maybe_param_info.ok_or(NoSuchGameParameterError {
                source_code: ctx.named_source(),
                at: (name_span.start()..name_span.end()).into(),
                param_name: name.to_string(),
                game_name: game.name.clone(),
            })?;

            Ok((pair_span, name_ast, value_ast, expected_type.clone()))
        })
        .partition(
            |result| matches!(result, Ok((_, _, _, ty)) if matches!(ty.kind(), TypeKind::Integer)),
        );

    let mut bits_rewrite_rules = vec![];

    // ... then we parse the ints and add populate a list of rewrite rules
    //     for all the Bits types ...
    for res in &ints {
        // skip entries with errors. We'll catch the error when we iterate over the combined
        // iterator below.
        let Ok((_, name_ast, value_ast, expected_type)) = res.as_ref() else {
            continue;
        };

        // parse the assigned value, and set the expected type to what the clone
        // prescribes.
        let value = super::package::handle_expression(
            &ctx.parse_ctx(),
            value_ast.clone(),
            Some(expected_type),
        )?;

        let assigned_countspec = match value.into_kind() {
            ExpressionKind::Identifier(ident) => CountSpec::Identifier(Box::new(ident)),
            // TODO:: enforce somehow that this number is not negative
            ExpressionKind::IntegerLiteral(num) => CountSpec::Literal(num as u64),
            _ => {
                //return Err(todo!());
                todo!()
            }
        };

        let name: &str = name_ast.as_str();

        bits_rewrite_rules.push((
            Type::bits(CountSpec::Identifier(Box::new(Identifier::GameIdentifier(
                GameIdentifier::Const(GameConstIdentifier {
                    game_name: game.name.clone(),
                    name: name.to_string(),
                    ty: Type::integer(),
                    game_inst_name: None,
                    theorem_name: None,
                    inst_info: None,
                    assigned_value: None,
                }),
            )))),
            Type::bits(assigned_countspec),
        ));
    }

    // ... then we map the other values to rewrite the types according to the rules defined
    //     above ...
    let others_iter = others.into_iter().map(|res| {
        res.map(|(pair_span, name_ast, value_ast, ty)| {
            (
                pair_span,
                name_ast,
                value_ast,
                ty.rewrite_type(&bits_rewrite_rules),
            )
        })
    });

    // and then we chain the two again and do the rest of the processing
    ints
        .into_iter()
        .chain(others_iter)
        .map(|res: Result<(pest::Span, Pair<Rule>, Pair<Rule>, Type), ParseTheoremError>| -> Result<(String, Expression), ParseTheoremError> {
        let (pair_span, name_ast, value_ast, expected_type) = res?;
        let name: &str = name_ast.as_str();
        let name_span: pest::Span = name_ast.as_span();

            // check that the defined parameter hasn't been defined before
            // (insert returns Some(x) if x has been written before)
            if let Some(prev_span) = defined_params.insert(
                name.to_string(),
                (pair_span.start()..pair_span.end()).into(),
            ) {
                return Err(DuplicateGameParameterDefinitionError {
                    source_code: ctx.named_source(),
                    at: (name_span.start()..name_span.end()).into(),
                    other: prev_span,
                    param_name: name.to_string(),
                    game_inst_name: game_inst_name.to_string(),
                }
                .into());
            }


            let value = super::package::handle_expression(
                &ctx.parse_ctx(),
                value_ast,
                Some(&expected_type),
            )?;

            Ok((name.to_owned(), value.clone()))
        })
        .collect::<std::result::Result<Vec<_>, ParseTheoremError>>()
        .and_then(|list| {
            let definied_names: HashSet<String> = defined_params.keys().cloned().collect();
            let declared_names: HashSet<String> =
                params.iter().map(|(name, _)| name).cloned().collect();

            let missing_params_vec: Vec<_> = declared_names
                .difference(&definied_names)
                .cloned()
                .collect();
            let missing_params = missing_params_vec.iter().join(", ");

            if !missing_params_vec.is_empty() {
                Err(MissingGameParameterDefinitionError {
                    source_code: ctx.named_source(),
                    at: (block_span.start()..block_span.end()).into(),
                    game_name: game.name.clone(),
                    game_inst_name: game_inst_name.to_string(),
                    missing_params_vec,
                    missing_params,
                }
                .into())
            } else {
                Ok(list)
            }
        })
}

/*
pub fn handle_types_def_list(
    ast: Pair<Rule>,
    inst_name: &str,
    file_name: &str,
) -> std::result::Result<Vec<(String, Type)>, ParseGameError> {
    ast.into_inner()
        .map(|def_spec| handle_types_def_spec(def_spec, inst_name, file_name))
        .collect()
}

pub fn handle_types_def_spec(
    ast: Pair<Rule>,
    inst_name: &str,
    _file_name: &str,
) -> Result<(String, Type)> {
    let span = ast.as_span();
    let mut iter = ast.into_inner();

    let fst = iter.next().unwrap();

    let snd = iter.next().unwrap();

    let snd_span = snd.as_span();
    let snd_type = handle_type(snd);

        let place = crate::transforms::resolvetypes::Place::Types {
            inst_name: inst_name.to_string(),
            type_name: format!("{:?}", fst.as_str()),
        };

        let tf = crate::transforms::resolvetypes::ResolveTypesTypeTransform::new(place);

        if let Err(err) = tf.transform_type(&snd_type, &(span.start()..span.end()).into()) {
            return Err(error::Error::from(err).with_span(snd_span));
        }

    Ok((fst.as_str().to_string(), snd_type))
}
    */

pub fn handle_const_decl(
    ctx: &ParseContext,
    ast: Pair<Rule>,
) -> Result<(String, Type), HandleTypeError> {
    let mut inner = ast.into_inner();
    let name = inner.next().unwrap().as_str().to_owned();
    handle_type(ctx, inner.next().unwrap()).map(|t| (name, t))
}
