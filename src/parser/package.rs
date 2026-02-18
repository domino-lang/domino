// SPDX-License-Identifier: MIT OR Apache-2.0

use super::{
    common::*,
    error::{
        ArgumentCountMismatchError, ExpectedExpressionIdentifierError,
        IdentifierAlreadyDeclaredError, IllegalLiteralError, MissingReturnError, ParserScopeError,
        TypeMismatchError, UndefinedIdentifierError, UntypedNoneTypeInferenceError,
        WrongArgumentCountInInvocationError,
    },
    ParseContext, Rule,
};
use crate::{
    expressions::{Expression, ExpressionKind},
    identifier::{
        pkg_ident::{
            PackageConstIdentifier, PackageIdentifier, PackageLocalIdentifier,
            PackageOracleArgIdentifier, PackageOracleCodeLoopVarIdentifier, PackageStateIdentifier,
        },
        Identifier,
    },
    package::{OracleDef, OracleSig, Package},
    parser::error::{
        ForLoopIdentifersDontMatchError, NoSuchOracleError, OracleAlreadyImportedError,
    },
    statement::{CodeBlock, FilePosition, IfThenElse, InvokeOracle, Pattern, Statement},
    types::{CountSpec, Type, TypeKind},
    util::scope::{Declaration, OracleContext, Scope},
};

use miette::{Diagnostic, NamedSource, SourceSpan};
use pest::iterators::Pair;
use thiserror::Error;

use std::collections::HashMap;
use std::hash::Hash;

#[derive(Clone, Debug)]
pub struct ParsePackageContext<'src> {
    pub file_name: &'src str,
    pub file_content: &'src str,
    pub scope: Scope,

    pub pkg_name: &'src str,
    pub oracles: Vec<OracleDef>,
    pub state: Vec<(String, Type, SourceSpan)>,
    pub params: Vec<(String, Type, SourceSpan)>,
    pub types: Vec<String>,
    pub imported_oracles: HashMap<String, (OracleSig, SourceSpan)>,
}

impl<'src> ParseContext<'src> {
    fn pkg_parse_context(self, pkg_name: &'src str) -> ParsePackageContext<'src> {
        let mut scope = Scope::new();
        scope.enter();

        ParsePackageContext {
            file_name: self.file_name,
            file_content: self.file_content,
            pkg_name,
            scope,

            oracles: vec![],
            state: vec![],
            params: vec![],
            types: vec![],
            imported_oracles: HashMap::new(),
        }
    }
}

impl<'src> ParsePackageContext<'src> {
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

impl<'src> From<ParsePackageContext<'src>> for ParseContext<'src> {
    fn from(value: ParsePackageContext<'src>) -> Self {
        Self {
            file_name: value.file_name,
            file_content: value.file_content,
            scope: value.scope,
            types: value.types,
        }
    }
}

#[derive(Debug, Error, Diagnostic)]
pub enum ParsePackageError {
    #[error("error parsing package's import oracle block: {0}")]
    #[diagnostic(transparent)]
    ParseImportOracleSig(#[from] ParseImportOraclesError),

    #[error("error parsing oracle definition: {0}")]
    #[diagnostic(transparent)]
    ParseOracleDef(#[from] ParseOracleDefError),

    #[error(transparent)]
    #[diagnostic(transparent)]
    IdentifierAlreadyDeclared(#[from] IdentifierAlreadyDeclaredError),

    #[diagnostic(transparent)]
    #[error(transparent)]
    HandleType(#[from] HandleTypeError),

    #[diagnostic(transparent)]
    #[error(transparent)]
    NoSuchOracle(#[from] NoSuchOracleError),

    #[error(transparent)]
    #[diagnostic(transparent)]
    ParseExpression(#[from] ParseExpressionError),

    #[error("error parsing identifier: {0}")]
    #[diagnostic(transparent)]
    ParseIdentifier(#[from] ParseIdentifierError),

    #[error(transparent)]
    #[diagnostic(transparent)]
    UndefinedIdentifier(#[from] UndefinedIdentifierError),

    #[error(transparent)]
    #[diagnostic(transparent)]
    TypeMismatch(#[from] TypeMismatchError),

    #[error(transparent)]
    #[diagnostic(transparent)]
    ArgumentCountMismatch(#[from] ArgumentCountMismatchError),

    #[error(transparent)]
    #[diagnostic(transparent)]
    OracleAlreadyImported(#[from] OracleAlreadyImportedError),

    #[error(transparent)]
    #[diagnostic(transparent)]
    Scope(#[from] ParserScopeError),

    #[error(transparent)]
    #[diagnostic(transparent)]
    ForLoopIdentifersDontMatch(#[from] ForLoopIdentifersDontMatchError),

    #[error(transparent)]
    #[diagnostic(transparent)]
    WrongArgumentCountInInvocation(#[from] WrongArgumentCountInInvocationError),

    #[error(transparent)]
    #[diagnostic(transparent)]
    MissingReturn(#[from] MissingReturnError),
}

#[derive(Error, Debug)]
pub enum ParseOracleSigError {}

pub fn handle_pkg(
    file_name: &str,
    file_content: &str,
    pkg: Pair<Rule>,
) -> Result<(String, Package), ParsePackageError> {
    let mut inner = pkg.into_inner();
    let pkg_name = inner.next().unwrap().as_str();
    let spec = inner.next().unwrap();

    let ctx = ParseContext::new(file_name, file_content).pkg_parse_context(pkg_name);

    let pkg = handle_pkg_spec(ctx, spec)?;
    Ok((pkg_name.to_owned(), pkg))
}

pub enum IdentType {
    State,
    Const,
}

pub fn handle_pkg_spec<'src>(
    mut ctx: ParsePackageContext<'src>,
    pkg_spec: Pair<'src, Rule>,
) -> Result<Package, ParsePackageError> {
    // TODO(2024-04-03): get rid of the unwraps in params, state, import_oracles
    for spec in pkg_spec.into_inner() {
        match spec.as_rule() {
            Rule::types => {
                for types_list in spec.into_inner() {
                    ctx.types.append(&mut handle_types_list(types_list))
                }
            }
            Rule::params => {
                ctx.scope.enter();
                let ast = spec.into_inner().next();
                let params_option_result: Option<Result<_, _>> =
                    ast.map(|params| handle_decl_list(&mut ctx, params, IdentType::Const));

                params_option_result.transpose()?;
            }
            Rule::state => {
                ctx.scope.enter();
                let ast = spec.into_inner().next();
                let state_option_result: Option<Result<_, _>> =
                    ast.map(|state| handle_decl_list(&mut ctx, state, IdentType::State));
                state_option_result.transpose()?;
            }
            Rule::import_oracles => {
                ctx.scope.enter();
                let body_ast = spec.into_inner().next().unwrap();
                handle_import_oracles_body(&mut ctx, body_ast)?;
            }
            Rule::oracle_def => {
                handle_oracle_def(&mut ctx, spec)?;
            }
            _ => unreachable!("unhandled ast node in package: {}", spec),
        }
    }

    Ok(Package {
        name: ctx.pkg_name.to_string(),
        oracles: ctx.oracles,
        types: ctx.types,
        params: ctx.params,
        imports: ctx
            .imported_oracles
            .iter()
            .map(|(_k, (v, loc))| (v.clone(), *loc))
            .collect(),
        state: ctx.state,
        //split_oracles: vec![],
        file_name: ctx.file_name.to_string(),
        file_contents: ctx.file_content.to_string(),
    })
}

pub fn handle_decl_list(
    ctx: &mut ParsePackageContext,
    decl_list: Pair<Rule>,
    ident_type: IdentType,
) -> Result<(), ParsePackageError> {
    for entry in decl_list.into_inner() {
        let parse_ctx = ctx.parse_ctx();
        let span = entry.as_span();
        let mut inner = entry.into_inner();
        let name_ast = inner.next().unwrap();
        let name_span = name_ast.as_span();
        let name = name_ast.as_str();
        let ty = handle_type(&parse_ctx, inner.next().unwrap())?;

        let ident: Identifier = match ident_type {
            IdentType::State => {
                ctx.state.push((
                    name.to_string(),
                    ty.clone(),
                    (span.start()..span.end()).into(),
                ));
                PackageStateIdentifier::new(name.to_string(), ctx.pkg_name.to_string(), ty.clone())
                    .into()
            }
            IdentType::Const => {
                ctx.params.push((
                    name.to_string(),
                    ty.clone(),
                    (span.start()..span.end()).into(),
                ));
                PackageConstIdentifier::new(name.to_string(), ctx.pkg_name.to_string(), ty.clone())
                    .into()
            }
        };

        ctx.scope
            .declare(name, Declaration::Identifier(ident))
            .map_err(|_| {
                let length = name_span.end() - name_span.start();

                IdentifierAlreadyDeclaredError {
                    at: (name_span.start(), length).into(),
                    ident_name: name.to_string(),
                    source_code: NamedSource::new(ctx.file_name, ctx.file_content.to_string()),
                }
            })?;
    }

    Ok(())
}

// TODO: identifier is optional, type needs custom type info
pub fn handle_arglist(
    ctx: &ParsePackageContext,
    arglist: Pair<Rule>,
) -> Result<Vec<(String, Type)>, HandleTypeError> {
    let parse_ctx = ctx.parse_ctx();

    arglist
        .into_inner()
        .map(|arg| {
            let mut inner = arg.into_inner();
            let id = inner.next().unwrap().as_str();
            let ty = handle_type(&parse_ctx, inner.next().unwrap())?;
            Ok((id.to_string(), ty))
        })
        .collect::<Result<_, _>>()
}

#[derive(Error, Debug, Diagnostic)]
pub enum ParseExpressionError {
    #[error(transparent)]
    #[diagnostic(transparent)]
    UndefinedIdentifier(#[from] UndefinedIdentifierError),

    #[error(transparent)]
    #[diagnostic(transparent)]
    ArgumentCountMismatch(#[from] ArgumentCountMismatchError),

    #[error(transparent)]
    #[diagnostic(transparent)]
    IllegalLiteral(#[from] IllegalLiteralError),

    #[error(transparent)]
    #[diagnostic(transparent)]
    TypeMismatch(#[from] TypeMismatchError),

    #[diagnostic(transparent)]
    #[error(transparent)]
    HandleType(#[from] HandleTypeError),

    #[diagnostic(transparent)]
    #[error(transparent)]
    UntypedNoneTypeInference(#[from] UntypedNoneTypeInferenceError),

    #[diagnostic(transparent)]
    #[error(transparent)]
    ExpectedExpressionIdentifier(#[from] ExpectedExpressionIdentifierError),
}

impl From<HandleIdentifierRhsError> for ParseExpressionError {
    fn from(value: HandleIdentifierRhsError) -> Self {
        match value {
            HandleIdentifierRhsError::UndefinedIdentifier(err) => Self::UndefinedIdentifier(err),
            HandleIdentifierRhsError::ExpectedExpressionIdentifier(err) => {
                Self::ExpectedExpressionIdentifier(err)
            }
        }
    }
}

pub fn handle_expression(
    ctx: &ParseContext,
    ast: Pair<Rule>,
    expected_type: Option<&Type>,
) -> Result<Expression, ParseExpressionError> {
    let span = ast.as_span();
    let kind = match ast.as_rule() {
        Rule::expr_add => {
            if let Some(ty_expect) = expected_type {
                if !ty_expect.kind().is_integer() {
                    return Err(TypeMismatchError {
                        at: (span.start()..span.end()).into(),
                        expected: ty_expect.clone(),
                        got: Type::integer(),
                        source_code: ctx.named_source(),
                    }
                    .into());
                }
            }

            let mut inner = ast.into_inner();

            let lhs_ast = inner.next().unwrap();
            let rhs_ast = inner.next().unwrap();
            let span = lhs_ast.as_span();

            let lhs = handle_expression(ctx, lhs_ast, expected_type)?;

            let ty_lhs = lhs.get_type();

            if !ty_lhs.kind().is_integer() {
                return Err(TypeMismatchError {
                    at: (span.start()..span.end()).into(),
                    expected: Type::integer(),
                    got: ty_lhs,
                    source_code: ctx.named_source(),
                }
                .into());
            }

            let rhs = handle_expression(ctx, rhs_ast, Some(&ty_lhs))?;

            ExpressionKind::Add(Box::new(lhs), Box::new(rhs))
        }
        Rule::expr_sub => {
            let mut inner = ast.into_inner();
            let lhs = handle_expression(ctx, inner.next().unwrap(), expected_type)?;
            let rhs = handle_expression(ctx, inner.next().unwrap(), expected_type)?;
            ExpressionKind::Sub(Box::new(lhs), Box::new(rhs))
        }
        Rule::expr_mul => {
            let mut inner = ast.into_inner();
            let lhs = handle_expression(ctx, inner.next().unwrap(), expected_type)?;
            let rhs = handle_expression(ctx, inner.next().unwrap(), expected_type)?;
            ExpressionKind::Mul(Box::new(lhs), Box::new(rhs))
        }
        Rule::expr_div => {
            let mut inner = ast.into_inner();
            let lhs = handle_expression(ctx, inner.next().unwrap(), expected_type)?;
            let rhs = handle_expression(ctx, inner.next().unwrap(), expected_type)?;
            ExpressionKind::Div(Box::new(lhs), Box::new(rhs))
        }
        Rule::expr_smaller => {
            let mut inner = ast.into_inner();
            let lhs = handle_expression(ctx, inner.next().unwrap(), Some(&Type::integer()))?;
            let rhs = handle_expression(ctx, inner.next().unwrap(), Some(&Type::integer()))?;
            ExpressionKind::LessThen(Box::new(lhs), Box::new(rhs))
        }
        Rule::expr_greater => {
            let mut inner = ast.into_inner();
            let lhs = handle_expression(ctx, inner.next().unwrap(), Some(&Type::integer()))?;
            let rhs = handle_expression(ctx, inner.next().unwrap(), Some(&Type::integer()))?;
            ExpressionKind::GreaterThen(Box::new(lhs), Box::new(rhs))
        }
        Rule::expr_smaller_eq => {
            let mut inner = ast.into_inner();
            let lhs = handle_expression(ctx, inner.next().unwrap(), Some(&Type::integer()))?;
            let rhs = handle_expression(ctx, inner.next().unwrap(), Some(&Type::integer()))?;
            ExpressionKind::LessThenEq(Box::new(lhs), Box::new(rhs))
        }
        Rule::expr_greater_eq => {
            let mut inner = ast.into_inner();
            let lhs = handle_expression(ctx, inner.next().unwrap(), Some(&Type::integer()))?;
            let rhs = handle_expression(ctx, inner.next().unwrap(), Some(&Type::integer()))?;
            ExpressionKind::GreaterThenEq(Box::new(lhs), Box::new(rhs))
        }

        Rule::expr_and => ExpressionKind::And(
            ast.into_inner()
                .map(|expr| handle_expression(ctx, expr, Some(&Type::boolean())))
                .collect::<Result<_, _>>()?,
        ),
        Rule::expr_or => ExpressionKind::Or(
            ast.into_inner()
                .map(|expr| handle_expression(ctx, expr, Some(&Type::boolean())))
                .collect::<Result<_, _>>()?,
        ),
        Rule::expr_xor => ExpressionKind::Xor(
            ast.into_inner()
                .map(|expr| handle_expression(ctx, expr, Some(&Type::boolean())))
                .collect::<Result<_, _>>()?,
        ),
        Rule::expr_not => {
            let mut inner = ast.into_inner();
            let content = handle_expression(ctx, inner.next().unwrap(), Some(&Type::boolean()))?;
            ExpressionKind::Not(Box::new(content))
        }

        Rule::expr_equals => {
            let mut pairs = ast.into_inner();

            let first = pairs.next().unwrap();
            let first = handle_expression(ctx, first, None)?;

            let first_type = first.get_type();

            ExpressionKind::Equals(
                vec![Ok(first)]
                    .into_iter()
                    .chain(pairs.map(|expr| handle_expression(ctx, expr, Some(&first_type))))
                    .collect::<Result<_, _>>()?,
            )
        }
        Rule::expr_not_equals => {
            let mut pairs = ast.into_inner();

            let first = pairs.next().unwrap();
            let first = handle_expression(ctx, first, None)?;

            let first_type = first.get_type();

            ExpressionKind::Not(Box::new(Expression::equals(
                vec![Ok(first)]
                    .into_iter()
                    .chain(pairs.map(|expr| handle_expression(ctx, expr, Some(&first_type))))
                    .collect::<Result<_, _>>()?,
            )))
        }
        Rule::expr_none => {
            let ty = handle_type(ctx, ast.into_inner().next().unwrap())?;
            ExpressionKind::None(ty)
        }

        Rule::expr_untyped_none => match expected_type {
            None => {
                // we can't guess the None type, need it set from outside
                // in this case the caller didn't tell us anything
                return Err(UntypedNoneTypeInferenceError {
                    source_code: ctx.named_source(),
                    at: (span.start()..span.end()).into(),
                }
                .into());
            }
            Some(expected_type) => match expected_type.kind() {
                // we can't guess the None type, need it set from outside
                // in this case the caller said it's a maybe but we don't know what's inside
                TypeKind::Maybe(t) if matches!(t.as_ref().kind(), TypeKind::Unknown) => {
                    return Err(UntypedNoneTypeInferenceError {
                        source_code: ctx.named_source(),
                        at: (span.start()..span.end()).into(),
                    }
                    .into());
                }
                // the caller gave us the type, we use that
                TypeKind::Maybe(inner_type) => ExpressionKind::None(*inner_type.clone()),
                // the caller expected some none-maybe type, that's an error
                _ => {
                    return Err(TypeMismatchError {
                        source_code: ctx.named_source(),
                        at: (span.start()..span.end()).into(),
                        expected: expected_type.to_owned(),
                        got: Type::maybe(Type::unknown()),
                    }
                    .into());
                }
            },
        },

        Rule::expr_some => {
            // make sure the expected type is a maybe.
            // if yes, extract the expected type for the inner expression
            // if not, abort with an error
            let expected_type = if let Some(ty_expect) = expected_type {
                let TypeKind::Maybe(ty) = ty_expect.kind() else {
                    return Err(TypeMismatchError {
                        at: (span.start()..span.end()).into(),
                        expected: ty_expect.clone(),
                        // TODO: maybe actually keep parsing here to produce better diagnostic
                        // output (whole type)
                        got: Type::maybe(Type::unknown()),
                        source_code: ctx.named_source(),
                    }
                    .into());
                };
                if ty.kind().is_unknown() {
                    None
                } else {
                    Some(*ty.clone())
                }
            } else {
                None
            };

            let expr = handle_expression(
                ctx,
                ast.into_inner().next().unwrap(),
                expected_type.as_ref(),
            )?;
            ExpressionKind::Some(Box::new(expr))
        }
        Rule::expr_unwrap => {
            let expected_type: Option<Type> = if let Some(ty) = expected_type {
                Some(Type::maybe(ty.clone()))
            } else {
                Some(Type::maybe(Type::unknown()))
            };
            let expr = handle_expression(
                ctx,
                ast.into_inner().next().unwrap(),
                expected_type.as_ref(),
            )?;
            ExpressionKind::Unwrap(Box::new(expr))
        }

        Rule::expr_newtable => {
            let mut inner = ast.into_inner();
            let [idxty_ast, valty_ast] = [inner.next().unwrap(), inner.next().unwrap()];

            let idxty = handle_type(ctx, idxty_ast)?;
            let valty = handle_type(ctx, valty_ast)?;

            ExpressionKind::EmptyTable(Type::table(idxty, valty))
        }
        Rule::table_access => {
            let expr_span = ast.as_span();
            let mut inner = ast.into_inner();

            let ident_ast = inner.next().unwrap();
            let ident_span = ident_ast.as_span();
            let ident_name = ident_ast.as_str();
            let ident = handle_identifier_in_code_rhs(ctx, &ident_ast, ident_name)?;

            // We first fetch the identifier. Since this is an identifier, we know the full type,
            // so we learn most by doing this first. No need for inference here.
            let TypeKind::Table(idx_type, val_type) = ident.get_type().into_kind() else {
                return Err(ParseExpressionError::TypeMismatch(TypeMismatchError {
                    at: (ident_span.start()..ident_span.end()).into(),
                    expected: Type::table(Type::unknown(), Type::unknown()),
                    got: ident.get_type(),
                    source_code: ctx.named_source(),
                }));
            };

            // Check that the type we got matches the expected type, if it is set
            if let Some(expected_type) = expected_type {
                // The expected value should be a maybe. if it isn't we return an error
                let TypeKind::Maybe(expected_value_type) = expected_type.kind() else {
                    return Err(ParseExpressionError::TypeMismatch(TypeMismatchError {
                        at: (expr_span.start()..expr_span.end()).into(),
                        expected: expected_type.clone(),
                        got: Type::maybe(*val_type.clone()),
                        source_code: ctx.named_source(),
                    }));
                };

                // Ensure that the expected type is unknown or matches
                if !(expected_value_type.kind().is_unknown()
                    || expected_value_type.kind() == val_type.kind())
                {
                    return Err(ParseExpressionError::TypeMismatch(TypeMismatchError {
                        at: (expr_span.start()..expr_span.end()).into(),
                        expected: expected_type.clone(),
                        got: Type::maybe(*val_type.clone()),
                        source_code: ctx.named_source(),
                    }));
                }
            };

            let idx_expr = handle_expression(ctx, inner.next().unwrap(), Some(&*idx_type))?;

            // XXX: not sure what is meant with this TODO
            // TODO properly parse this identifier
            ExpressionKind::TableAccess(ident, Box::new(idx_expr))
        }

        Rule::fn_call => {
            let span = ast.as_span();
            let mut inner = ast.into_inner();
            let ident_ast = inner.next().unwrap();
            let ident_span = ident_ast.as_span();
            let ident = ident_ast.as_str();
            let decl = ctx
                .scope
                .lookup(ident)
                .ok_or(ParseExpressionError::UndefinedIdentifier(
                    UndefinedIdentifierError {
                        at: (span.start()..span.end()).into(),
                        ident_name: ident.to_string(),
                        source_code: NamedSource::new(ctx.file_name, ctx.file_content.to_string()),
                    },
                ))?;
            let ident = decl
                .into_identifier()
                .map_err(|_| ExpectedExpressionIdentifierError {
                    at: (ident_span.start()..ident_span.end()).into(),
                    oracle_name: ident.to_string(),
                    source_code: NamedSource::new(ctx.file_name, ctx.file_content.to_string()),
                })?;
            let TypeKind::Fn(exp_args_tys, ret_ty) = ident.get_type().into_kind() else {
                // callee is not a function
                return Err(TypeMismatchError {
                    at: (ident_span.start()..ident_span.end()).into(),
                    expected: Type::fun(vec![], Type::unknown()),
                    got: ident.get_type(),
                    source_code: ctx.named_source(),
                }
                .into());
            };
            let arg_asts = match inner.next() {
                None => vec![],
                Some(inner_args) => inner_args.into_inner().collect(),
            };
            if let Some(expected_type) = expected_type {
                if expected_type != ret_ty.as_ref() {
                    // the function's return type doesn't match what we expect
                    return Err(TypeMismatchError {
                        at: (ident_span.start()..ident_span.end()).into(),
                        expected: expected_type.clone(),
                        got: *ret_ty,
                        source_code: ctx.named_source(),
                    }
                    .into());
                }
            }
            if exp_args_tys.len() != arg_asts.len() {
                // callee has wrong number of args
                return Err(ArgumentCountMismatchError {
                    at: (span.start()..span.end()).into(),
                    expected: exp_args_tys.len(),
                    got: arg_asts.len(),
                    source_code: ctx.named_source(),
                }
                .into());
            }
            let args = arg_asts
                .into_iter()
                .zip(exp_args_tys)
                .map(|(arg_ast, exp_ty)| handle_expression(ctx, arg_ast, Some(&exp_ty)))
                .collect::<Result<Vec<_>, _>>()?;

            ExpressionKind::FnCall(ident, args)
        }

        Rule::identifier => {
            let span = ast.as_span();

            let name = ast.as_str().to_string();
            let decl = ctx
                .scope
                .lookup(&name)
                .ok_or(ParseExpressionError::UndefinedIdentifier(
                    UndefinedIdentifierError {
                        at: (span.start()..span.end()).into(),
                        ident_name: name.clone(),
                        source_code: NamedSource::new(ctx.file_name, ctx.file_content.to_string()),
                    },
                ))?;

            let ident = match decl {
                Declaration::Identifier(ident) => ident,
                Declaration::Oracle(_, _) => {
                    todo!("handle error, user tried assigning to an oracle")
                }
            };
            ExpressionKind::Identifier(ident)
        }

        Rule::literal_bits_zero | Rule::literal_bits_one => {
            let span = ast.as_span();
            let literal_str = ast.clone().as_str();

            let content = &ast.as_str()[0..1];
            let inner = ast.into_inner().next().unwrap();
            let cspec = handle_countspec(ctx, inner)?;
            if cspec == CountSpec::Any {
                return Err(ParseExpressionError::IllegalLiteral(IllegalLiteralError {
                    at: (span.start()..span.end()).into(),
                    literal_str: literal_str.to_string(),
                    source_code: NamedSource::new(ctx.file_name, ctx.file_content.to_string()),
                }));
            }
            ExpressionKind::BitsLiteral(content.to_string(), Type::bits(cspec))
        }

        Rule::literal_boolean => {
            let litval = ast.as_str().to_string();
            ExpressionKind::BooleanLiteral(litval)
        }
        Rule::literal_integer => {
            let litval = ast.as_str().trim().to_string();

            ExpressionKind::IntegerLiteral(litval.parse().unwrap_or_else(|_| {
                // The grammar only allows ASCII_DIGIT+ here, so we should be fine?
                // Maybe if the number is too big?
                unreachable!(
                    "error at position {:?}..{:?}: could not parse as int: {}",
                    ast.as_span().start_pos().line_col(),
                    ast.as_span().end_pos().line_col(),
                    ast.as_str(),
                )
            }))
        }
        // TODO: we can't infer the type for empty sets and lists.
        //       this means we either need separate expressions for empty ones (that have a type),
        //       or they all need a type, like None
        Rule::literal_emptyset => ExpressionKind::Set(vec![]),
        Rule::expr_list => ExpressionKind::List(
            ast.into_inner()
                .map(|expr| handle_expression(ctx, expr, None))
                .collect::<Result<_, _>>()?,
        ),
        Rule::expr_tuple => {
            if let Some(expected_type) = expected_type {
                let TypeKind::Tuple(types) = expected_type.kind() else {
                    // what if there is an expected type, but it's not a tuple?
                    let inner_types = ast
                        .into_inner()
                        .map(|expr| handle_expression(ctx, expr, None).map(|expr| expr.get_type()))
                        .collect::<Result<Vec<_>, _>>()?;

                    return Err(TypeMismatchError {
                        at: (span.start()..span.end()).into(),
                        expected: expected_type.to_owned(),
                        got: Type::tuple(inner_types),
                        source_code: ctx.named_source(),
                    }
                    .into());
                };

                let expr_asts = ast.into_inner().collect::<Vec<_>>();

                // what if there is an expected type and it's a tuple, but it's the wrong length?
                if expr_asts.len() != types.len() {
                    let inner_types = expr_asts
                        .into_iter()
                        .map(|expr| handle_expression(ctx, expr, None).map(|expr| expr.get_type()))
                        .collect::<Result<Vec<_>, _>>()?;

                    return Err(TypeMismatchError {
                        at: (span.start()..span.end()).into(),
                        expected: expected_type.to_owned(),
                        got: Type::tuple(inner_types),
                        source_code: ctx.named_source(),
                    }
                    .into());
                }

                ExpressionKind::Tuple(
                    expr_asts
                        .into_iter()
                        .zip(types.iter())
                        .map(|(ast, expected_type)| {
                            handle_expression(ctx, ast, Some(expected_type))
                        })
                        .collect::<Result<_, _>>()?,
                )
            } else {
                ExpressionKind::Tuple(
                    ast.into_inner()
                        .map(|expr| handle_expression(ctx, expr, None))
                        .collect::<Result<_, _>>()?,
                )
            }
        }
        Rule::expr_set => ExpressionKind::Set(
            ast.into_inner()
                .map(|expr| handle_expression(ctx, expr, None))
                .collect::<Result<_, _>>()?,
        ),
        _ => unreachable!("Unhandled expression {:#?}", ast),
    };
    let expr = Expression::from_kind(kind);

    if let Some(expected) = expected_type {
        let got = expr.get_type();
        let at: SourceSpan = (span.start()..span.end()).into();

        let expecting_unknown_maybe =
            matches!(expected.kind(),  TypeKind::Maybe(inner) if inner.kind().is_unknown());
        let got_a_maybe = matches!(got.kind(), TypeKind::Maybe(_));

        // we allow a mismatch if we don't know what the type in the maybe is, and got some kind of
        // maybe. This is effectively a form of type inference.
        let allow_mismatch = expecting_unknown_maybe && got_a_maybe;

        if *expected != got && !allow_mismatch {
            let expected = expected.clone();

            return Err(ParseExpressionError::TypeMismatch(TypeMismatchError {
                at,
                expected,
                got,
                source_code: NamedSource::new(ctx.file_name, ctx.file_content.to_string()),
            }));
        }
    }

    Ok(expr)
}

#[derive(Error, Debug, Diagnostic)]
pub enum ParseCodeError {}

pub fn handle_identifier_in_code_rhs(
    ctx: &ParseContext,
    ast: &Pair<Rule>,
    name: &str,
) -> Result<Identifier, HandleIdentifierRhsError> {
    let span = ast.as_span();
    let ident = ctx
        .scope
        .lookup(name)
        .ok_or(UndefinedIdentifierError {
            at: (span.start()..span.end()).into(),
            ident_name: name.to_string(),
            source_code: NamedSource::new(ctx.file_name, ctx.file_content.to_string()),
        })?
        .into_identifier()
        .map_err(|_| ExpectedExpressionIdentifierError {
            at: (span.start()..span.end()).into(),
            oracle_name: name.to_string(),
            source_code: NamedSource::new(ctx.file_name, ctx.file_content.to_string()),
        })?;

    Ok(ident)
}

#[derive(Debug, Error, Diagnostic)]
pub enum HandleIdentifierRhsError {
    #[diagnostic(transparent)]
    #[error(transparent)]
    UndefinedIdentifier(#[from] UndefinedIdentifierError),

    #[diagnostic(transparent)]
    #[error(transparent)]
    ExpectedExpressionIdentifier(#[from] ExpectedExpressionIdentifierError),
}

pub fn handle_identifier_in_code_lhs(
    ctx: &mut ParsePackageContext,
    name_ast: Pair<Rule>,
    oracle_name: &str,
    expression_type: Type,
) -> Result<Identifier, ParseIdentifierError> {
    let name = name_ast.as_str();
    let span = name_ast.as_span();

    let scope = &mut ctx.scope;

    let ident = if let Some(decl) = scope.lookup(name) {
        decl.into_identifier()
            .map_err(|_| ExpectedExpressionIdentifierError {
                at: (span.start()..span.end()).into(),
                oracle_name: name.to_string(),
                source_code: NamedSource::new(ctx.file_name, ctx.file_content.to_string()),
            })?
    } else {
        let ident =
            Identifier::PackageIdentifier(PackageIdentifier::Local(PackageLocalIdentifier {
                pkg_name: ctx.pkg_name.to_string(),
                oracle_name: oracle_name.to_string(),
                name: name.to_string(),
                ty: expression_type.clone(),
                pkg_inst_name: None,
                game_name: None,
                game_inst_name: None,
                theorem_name: None,
            }));

        if scope
            .declare(name, Declaration::Identifier(ident.clone()))
            .is_err()
        {
            unreachable!()
        }

        ident
    };

    let declared_ident_type = ident.get_type();
    if declared_ident_type != expression_type {
        Err(ParseIdentifierError::TypeMismatch(TypeMismatchError {
            at: (span.start()..span.end()).into(),
            expected: declared_ident_type,
            got: expression_type,
            source_code: ctx.named_source(),
        }))
    } else {
        Ok(ident)
    }
}

#[derive(Debug, Error, Diagnostic)]
pub enum ParseIdentifierError {
    #[error(transparent)]
    #[diagnostic(transparent)]
    ParseExpression(ParseExpressionError),

    #[error(transparent)]
    #[diagnostic(transparent)]
    IdentifierAlreadyDeclared(#[from] IdentifierAlreadyDeclaredError),

    #[error(transparent)]
    #[diagnostic(transparent)]
    TypeMismatch(TypeMismatchError),

    #[diagnostic(transparent)]
    #[error(transparent)]
    ExpectedExpressionIdentifier(#[from] ExpectedExpressionIdentifierError),
}

// Helper structures and functions for unified assign statement handling

#[allow(clippy::large_enum_variant)]
enum OracleExprResult {
    Expression(Expression),
    Sample(Type, Option<String>), // Type to sample, optional sample name
    Invoke(String, Vec<Expression>, Type), // Oracle name, args, return type
}

fn handle_pattern(
    ctx: &mut ParsePackageContext,
    pattern_ast: Pair<Rule>,
    oracle_name: &str,
    value_type: Type,
) -> Result<Pattern, ParsePackageError> {
    use crate::statement::Pattern;

    let parse_ctx = ctx.parse_ctx();

    match pattern_ast.as_rule() {
        Rule::pattern_ident => {
            let ident = handle_identifier_in_code_lhs(ctx, pattern_ast, oracle_name, value_type)?;
            Ok(Pattern::Ident(ident))
        }
        Rule::pattern_table => {
            let pattern_span = pattern_ast.as_span();
            let mut inner = pattern_ast.into_inner();
            let name_ast = inner.next().unwrap();

            let index_ast = inner.next().unwrap();

            let index_expr = match ctx.scope.lookup_identifier(name_ast.as_str()) {
                Some(ident) => match ident.get_type().kind() {
                    TypeKind::Table(key_ty, _) => {
                        handle_expression(&parse_ctx, index_ast, Some(key_ty.as_ref()))?
                    }
                    _ => {
                        return Err(ParsePackageError::TypeMismatch(TypeMismatchError {
                            source_code: ctx.named_source(),
                            at: (pattern_span.start()..pattern_span.end()).into(),
                            expected: Type::table(Type::unknown(), value_type),
                            got: ident.get_type(),
                        }));
                    }
                },

                None => {
                    return Err(ParsePackageError::UndefinedIdentifier(
                        UndefinedIdentifierError {
                            source_code: ctx.named_source(),
                            at: (name_ast.as_span().start()..name_ast.as_span().end()).into(),
                            ident_name: name_ast.as_str().to_string(),
                        },
                    ))
                }
            };

            // For table patterns, we need to handle the Maybe wrapper correctly
            // The value_type coming in might be Maybe(T) or T depending on the RHS
            // If it's Maybe(T), the table type is Table(key_type, T)
            // If it's not Maybe, then we have a type error (caught later)
            let table_value_type = match value_type.clone().into_kind() {
                TypeKind::Maybe(inner_type) => *inner_type,
                _ => value_type.clone(), // For samples, the type is not wrapped in Maybe
            };

            let table_type = Type::table(index_expr.get_type(), table_value_type);

            let ident = handle_identifier_in_code_lhs(ctx, name_ast, oracle_name, table_type)?;

            Ok(Pattern::Table {
                ident,
                index: index_expr,
            })
        }
        Rule::pattern_tuple => {
            let TypeKind::Tuple(tys) = value_type.clone().into_kind() else {
                let span = pattern_ast.as_span();
                return Err(TypeMismatchError {
                    at: (span.start()..span.end()).into(),
                    expected: Type::unknown(), // We expect a tuple but don't know the exact type yet
                    got: value_type,
                    source_code: ctx.named_source(),
                }
                .into());
            };

            let idents: Vec<Identifier> = pattern_ast
                .into_inner()
                .enumerate()
                .map(|(i, pattern_ident)| {
                    handle_identifier_in_code_lhs(ctx, pattern_ident, oracle_name, tys[i].clone())
                })
                .collect::<Result<_, _>>()?;

            Ok(Pattern::Tuple(idents))
        }
        _ => unreachable!("unexpected pattern rule: {:?}", pattern_ast.as_rule()),
    }
}

fn handle_assign_rhs(
    ctx: &ParsePackageContext,
    assign_rhs_ast: Pair<Rule>,
    expected_type: Option<&Type>,
) -> Result<OracleExprResult, ParsePackageError> {
    let parse_ctx = ctx.parse_ctx();

    match assign_rhs_ast.as_rule() {
        Rule::assign_rhs_sample => {
            let mut inner = assign_rhs_ast.into_inner();
            let ty = handle_type(&parse_ctx, inner.next().unwrap())?;

            // Check for optional sample_name
            let sample_name = inner
                .next()
                // If we have another token, it should be the identifier after kw_sample_name
                // But kw_sample_name is silent (_), so we get the identifier directly
                .map(|kw_or_ident| kw_or_ident.as_str().to_string());

            Ok(OracleExprResult::Sample(ty, sample_name))
        }
        Rule::assign_rhs_invoke => {
            let mut inner = assign_rhs_ast.into_inner();
            let oracle_call = inner.next().unwrap();
            let oracle_call_span = oracle_call.as_span();

            let mut call_inner = oracle_call.into_inner();
            let oracle_name_ast = call_inner.next().unwrap();
            let oracle_name_span = oracle_name_ast.as_span();
            let oracle_name = oracle_name_ast.as_str();

            // Look up the oracle
            let oracle_decl = ctx
                .scope
                .lookup(oracle_name)
                .ok_or_else(|| NoSuchOracleError {
                    source_code: ctx.named_source(),
                    at: (oracle_name_span.start()..oracle_name_span.end()).into(),
                    oracle_name: oracle_name.to_string(),
                })?;

            let Declaration::Oracle(_target_oracle_ctx, target_oracle_sig) = oracle_decl else {
                return Err(NoSuchOracleError {
                    source_code: ctx.named_source(),
                    at: (oracle_name_span.start()..oracle_name_span.end()).into(),
                    oracle_name: oracle_name.to_string(),
                }
                .into());
            };

            // Parse arguments
            let mut args = vec![];
            for ast in call_inner {
                let args_iter = ast.into_inner();
                let (arg_count, _) = args_iter.size_hint();
                if arg_count != target_oracle_sig.args.len() {
                    return Err(WrongArgumentCountInInvocationError {
                        source_code: ctx.named_source(),
                        span: (oracle_call_span.start()..oracle_call_span.end()).into(),
                        oracle_name: oracle_name.to_string(),
                        expected_num: target_oracle_sig.args.len(),
                        got_num: arg_count,
                    }
                    .into());
                }

                let arglist: Result<Vec<_>, _> = args_iter
                    .zip(target_oracle_sig.args.iter())
                    .map(|(expr, (_, ty))| handle_expression(&parse_ctx, expr, Some(ty)))
                    .collect();
                args.extend(arglist?.into_iter());
            }

            Ok(OracleExprResult::Invoke(
                oracle_name.to_string(),
                args,
                target_oracle_sig.ty.clone(),
            ))
        }
        _ => {
            // It's a regular expression
            let expr = handle_expression(&parse_ctx, assign_rhs_ast, expected_type)?;
            Ok(OracleExprResult::Expression(expr))
        }
    }
}

pub fn handle_code(
    ctx: &mut ParsePackageContext,
    code: Pair<Rule>,
    oracle_sig: &OracleSig,
) -> Result<CodeBlock, ParsePackageError> {
    let oracle_name = &oracle_sig.name;
    code.into_inner()
        .map(|stmt| {
            let span = stmt.as_span();
            let full_span = (span.start()..span.end()).into();

            // TODO: check that we return in all cases (so we know the code we pass to the
            //       transforms is known to be valid)

            let stmt = match stmt.as_rule() {
                // assign | return_stmt | abort | ite
                Rule::ite => {
                    let mut inner = stmt.into_inner();
                    let cond = handle_expression(&ctx.parse_ctx(), inner.next().unwrap(), Some(&Type::boolean()))?;
                    let then_ast = inner.next().unwrap();
                    let then_span = then_ast.as_span();
                    let then_block = handle_code(
                        ctx,
                        then_ast,
                        oracle_sig,
                    )?;
                    let maybe_elsecode = inner.next();
                    let (else_span, else_block) = match maybe_elsecode {
                        None => (None, CodeBlock(vec![])),
                        Some(c) => (Some(c.as_span()), handle_code(ctx, c, oracle_sig)?),
                    };

                    let else_span = if let Some(else_span) = else_span {
                        (else_span.start()..else_span.end()).into()
                    } else {
                        (then_span.end()..then_span.end()).into()
                    };
                    let then_span = (then_span.start()..then_span.end()).into();

                    let ite = IfThenElse{
                        cond,
                        then_block,
                        else_block,
                        then_span,
                        else_span,
                        full_span,
                    };


                    Statement::IfThenElse(ite)
                }
                Rule::return_stmt => {
                    let mut inner = stmt.into_inner();
                    let maybe_expr = inner.next();


                    let expr = maybe_expr.map(|expr| handle_expression(&ctx.parse_ctx(), expr, Some(&oracle_sig.ty))).transpose()?;
                    Statement::Return(expr, full_span)
                }
                Rule::assert => {
                    let mut inner = stmt.into_inner();
                    let expr = handle_expression(&ctx.parse_ctx(), inner.next().unwrap(), Some(&Type::boolean()))?;

                    Statement::IfThenElse(IfThenElse { cond: expr, then_block: CodeBlock(vec![]), else_block: CodeBlock(vec![Statement::Abort(full_span)]), then_span: full_span, else_span: full_span, full_span })
                }
                Rule::abort => Statement::Abort(full_span),
                Rule::invoke_stmt => {
                    let mut inner = stmt.into_inner();
                    let oracle_call = inner.next().unwrap();
                    let oracle_call_span = oracle_call.as_span();

                    let mut call_inner = oracle_call.into_inner();
                    let oracle_name_ast = call_inner.next().unwrap();
                    let oracle_name_span = oracle_name_ast.as_span();
                    let oracle_name = oracle_name_ast.as_str();

                    let oracle_decl = ctx
                        .scope
                        .lookup(oracle_name)
                        .ok_or_else(|| NoSuchOracleError {
                            source_code: ctx.named_source(),
                            at: (oracle_name_span.start()..oracle_name_span.end()).into(),
                            oracle_name: oracle_name.to_string(),
                        })?;

                    let Declaration::Oracle(_target_oracle_ctx, target_oracle_sig) = oracle_decl else {
                        return Err(NoSuchOracleError {
                            source_code: ctx.named_source(),
                            at: (oracle_name_span.start()..oracle_name_span.end()).into(),
                            oracle_name: oracle_name.to_string(),
                        }
                        .into());
                    };

                    let mut args = vec![];
                    for ast in call_inner {
                        let args_iter = ast.into_inner();
                        let (arg_count, _) = args_iter.size_hint();
                        if arg_count != target_oracle_sig.args.len() {
                            return Err(WrongArgumentCountInInvocationError {
                                source_code: ctx.named_source(),
                                span: (oracle_call_span.start()..oracle_call_span.end()).into(),
                                oracle_name: oracle_name.to_string(),
                                expected_num: target_oracle_sig.args.len(),
                                got_num: arg_count,
                            }
                            .into());
                        }

                        let arglist: Result<Vec<_>, _> = args_iter
                            .zip(target_oracle_sig.args.iter())
                            .map(|(expr, (_, ty))| handle_expression(&ctx.parse_ctx(), expr, Some(ty)))
                            .collect();
                        args.extend(arglist?.into_iter());
                    }

                    Statement::InvokeOracle (InvokeOracle{
                        oracle_name: oracle_name.to_string(),
                        args,
                        edge: None,
                        file_pos: full_span,
                    })
                }
                Rule::assign => {
                    use crate::statement::{Assignment, AssignmentRhs, Pattern};

                    let mut inner = stmt.into_inner();
                    let pattern_ast = inner.next().unwrap();
                    let assign_rhs_ast = inner.next().unwrap();

                    // First, try to infer expected type from the pattern if it's an existing identifier
                    let expected_type = match pattern_ast.as_rule() {
                        Rule::pattern_ident => {
                            let name = pattern_ast.as_str();
                            match ctx.scope.lookup(name) {
                                Some(Declaration::Identifier(ident)) => Some(ident.get_type()),
                                _ => None,
                            }
                        }
                        Rule::pattern_table => {
                            let mut inner = pattern_ast.clone().into_inner();
                            let name = inner.next().unwrap();

                            match ctx.scope.lookup_identifier(name.as_str()) {
                                Some(ident) => match ident.get_type().kind() {
                                    TypeKind::Table(_key_ty, value_ty) => {
                                        Some(Type::maybe(*value_ty.clone()))
                                    }
                                    _ => None,
                                },
                                _ => {
                                    return Err(ParsePackageError::UndefinedIdentifier(
                                        UndefinedIdentifierError {
                                            source_code: ctx.named_source(),
                                            at: (name.as_span().start()..name.as_span().end()).into(),
                                            ident_name: name.as_str().to_string(),
                                        },
                                    ))
                                },
                            }
                        }
                        Rule::pattern_tuple => None,
                        _ => unreachable!()

                    };

                    // Handle the right-hand side oracle expression
                    let assign_rhs_result = handle_assign_rhs(ctx, assign_rhs_ast, expected_type.as_ref())?;

                    // Determine the value type based on oracle expression result
                    let value_type = match &assign_rhs_result {
                        OracleExprResult::Expression(expr) => expr.get_type(),
                        OracleExprResult::Sample(ty, _) => ty.clone(),
                        OracleExprResult::Invoke(_, _, ty) => ty.clone(),
                    };

                    // Handle the pattern with the value type
                    let pattern = handle_pattern(
                        ctx,
                        pattern_ast,
                        oracle_name,
                        value_type.clone(),
                    )?;

                    // Validate pattern + RHS combinations
                    if let (Pattern::Tuple(_), OracleExprResult::Sample(..)) = (&pattern, &assign_rhs_result) {
                        panic!("Cannot sample into tuple pattern - this should be prevented by grammar")
                    }

                    // Create the RHS
                    let rhs = match assign_rhs_result {
                        OracleExprResult::Expression(expr) => AssignmentRhs::Expression(expr),
                        OracleExprResult::Sample(ty, sample_name) => AssignmentRhs::Sample {
                            ty,
                            sample_name,
                            sample_id: None,
                        },
                        OracleExprResult::Invoke(oracle_name, args, return_type) => {
                            AssignmentRhs::Invoke {
                                oracle_name,
                                args,
                                edge: None,
                                return_type: Some(return_type),
                            }
                        }
                    };

                    Statement::Assignment(Assignment { pattern, rhs }, full_span)
                }
                Rule::for_ => {
                    let mut parsed: Vec<Pair<Rule>> = stmt.into_inner().collect();
                    let decl_var_name = parsed[0].as_str();
                    let lower_bound = handle_expression(&ctx.parse_ctx(), parsed.remove(1), Some(&Type::integer()))?;
                    let lower_bound_type = parsed[1].as_str();
                    let bound_var_name = parsed[2].as_str();
                    let upper_bound_type = parsed[3].as_str();
                    let upper_bound = handle_expression(&ctx.parse_ctx(), parsed.remove(4), Some(&Type::integer()))?;

                    if decl_var_name != bound_var_name {
                        todo!("return proper error here")
                    }

                    let lower_bound_type = match lower_bound_type {
                        "<" => ForComp::Lt,
                        "<=" => ForComp::Lte,
                        _ => panic!(),
                    };

                    let upper_bound_type = match upper_bound_type {
                        "<" => ForComp::Lt,
                        "<=" => ForComp::Lte,
                        _ => panic!(),
                    };
                    let loopvar = PackageOracleCodeLoopVarIdentifier {
                        name: decl_var_name.to_string(),
                        pkg_name: ctx.pkg_name.to_string(),
                        start: Box::new(lower_bound.clone()),
                        end: Box::new(upper_bound.clone()),
                        start_comp: lower_bound_type,
                        end_comp: upper_bound_type,
                        pkg_inst_name: None,
                        game_name: None,
                        game_inst_name: None,
                        theorem_name: None,
                    };
                    let loopvar: Identifier = loopvar.into();

                    ctx.scope.enter();
                    ctx.scope
                        .declare(decl_var_name, Declaration::Identifier(loopvar.clone()))
                        .unwrap();

                    let body =
                        handle_code(ctx, parsed.remove(4),oracle_sig)?;
                    ctx.scope.leave();

                    Statement::For(loopvar, lower_bound, upper_bound, body, full_span)
                }
                _ => {
                    unreachable!("{:#?}", stmt)
                }
            };

            Ok(stmt)
        })
        .collect::<Result<_, _>>()
        .map(CodeBlock)
}

#[derive(Error, Debug, Diagnostic)]
pub enum ParseOracleDefError {
    #[error(transparent)]
    #[diagnostic(transparent)]
    ParseCode(#[from] ParseCodeError),
}

pub fn handle_oracle_def(
    ctx: &mut ParsePackageContext,
    oracle_def: Pair<Rule>,
) -> Result<(), ParsePackageError> {
    let span = oracle_def.as_span();
    let source_span = SourceSpan::from(span.start()..span.end());
    let mut inner = oracle_def.into_inner();

    let sig = handle_oracle_sig(ctx, inner.next().unwrap())?;

    ctx.scope.enter();

    for (name, ty) in &sig.args {
        ctx.scope
            .declare(
                name,
                Declaration::Identifier(Identifier::PackageIdentifier(
                    PackageIdentifier::OracleArg(PackageOracleArgIdentifier {
                        pkg_name: ctx.pkg_name.to_string(),
                        oracle_name: sig.name.clone(),
                        name: name.clone(),
                        ty: ty.clone(),
                        pkg_inst_name: None,
                        game_name: None,
                        game_inst_name: None,
                        theorem_name: None,
                    }),
                )),
            )
            .map_err(|e| {
                ParsePackageError::Scope(ParserScopeError {
                    source_code: ctx.named_source(),
                    at: (span.start()..span.end()).into(),
                    related: vec![e],
                })
            })?;
    }

    let code = handle_code(ctx, inner.next().unwrap(), &sig)?;

    ctx.scope.leave();

    if !matches!(sig.ty.kind(), TypeKind::Empty) {
        fn check_block(
            ctx: &ParsePackageContext,
            oracle_name: &str,
            span: &SourceSpan,
            code: &CodeBlock,
        ) -> Result<(), ParsePackageError> {
            let stmt = code
                .0
                .iter()
                .last()
                .ok_or(ParsePackageError::MissingReturn(MissingReturnError {
                    at: *span,
                    oracle_name: oracle_name.to_string(),
                    source_code: ctx.named_source(),
                }))?;
            match stmt {
                Statement::Return(Some(_), _) => {
                    // Type is already verified by parse_expression
                    Ok(())
                }
                Statement::IfThenElse(ite) => {
                    let then = &ite.then_block;
                    let els = &ite.else_block;

                    check_block(ctx, oracle_name, span, then)?;
                    check_block(ctx, oracle_name, span, els)
                }
                _ => Err(ParsePackageError::MissingReturn(MissingReturnError {
                    at: *span,
                    oracle_name: oracle_name.to_string(),
                    source_code: ctx.named_source(),
                })),
            }
        }
        check_block(ctx, &sig.name, &source_span, &code)?;
    }

    let oracle_def = OracleDef {
        sig,
        code,
        file_pos: source_span,
    };

    ctx.oracles.push(oracle_def);

    Ok(())
}

pub fn handle_oracle_sig(
    ctx: &ParsePackageContext,
    oracle_sig: Pair<Rule>,
) -> Result<OracleSig, ParsePackageError> {
    let mut inner = oracle_sig.into_inner();
    let name = inner.next().unwrap().as_str();
    let maybe_arglist = inner.next().unwrap();
    let args = if maybe_arglist.as_str() == "" {
        vec![]
    } else {
        handle_arglist(ctx, maybe_arglist.into_inner().next().unwrap())?
    };

    let maybe_ty = inner.next();
    let ty = match maybe_ty {
        None => Type::empty(),
        Some(t) => handle_type(&ctx.parse_ctx(), t)?,
    };

    Ok(OracleSig {
        name: name.to_string(),
        ty,
        args,
    })
}

pub fn handle_oracle_imports_oracle_sig(
    ctx: &mut ParsePackageContext,
    oracle_sig: Pair<Rule>,
) -> Result<OracleSig, ParsePackageError> {
    debug_assert_eq!(oracle_sig.as_rule(), Rule::import_oracles_oracle_sig);

    let _span = oracle_sig.as_span();

    let mut inner = oracle_sig.into_inner();

    let name = inner.next().unwrap().as_str();
    let args = {
        let mut arglist = vec![];

        while let Some(next) = inner.peek() {
            match next.as_rule() {
                Rule::oracle_maybe_arglist => {
                    if !next.as_str().is_empty() {
                        arglist = handle_arglist(ctx, next.into_inner().next().unwrap())?;
                    }
                    inner.next();
                }
                _ => break,
            }
        }

        arglist
    };

    let parse_ctx = ctx.parse_ctx();
    let maybe_ty = inner.next();
    let ty = match maybe_ty {
        None => Type::empty(),
        Some(t) => handle_type(&parse_ctx, t)?,
    };

    Ok(OracleSig {
        name: name.to_string(),
        ty,
        args,
    })
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum ForComp {
    Lt,
    Lte,
}

#[derive(Debug)]
pub struct ForCompError(String);

impl std::fmt::Display for ForCompError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "not a valid comparison operator for for loops: {:?}",
            self.0
        )
    }
}

impl std::error::Error for ForCompError {}

impl std::convert::TryFrom<&str> for ForComp {
    type Error = ForCompError;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        match value {
            "<=" => Ok(ForComp::Lte),
            "<" => Ok(ForComp::Lt),
            _ => Err(ForCompError(value.to_string())),
        }
    }
}

#[derive(Debug, Error, Diagnostic)]
pub enum ParseImportOraclesError {
    #[error("error parsing loop start expression: {0}")]
    ParseStartExpression(ParseExpressionError, FilePosition),
    #[error("error parsing loop end expression: {0}")]
    ParseEndExpression(ParseExpressionError, FilePosition),
    #[error("first loop comparison is invalid: {0}")]
    InvalidStartComparison(ForCompError, FilePosition),
    #[error("second loop comparison is invalid: {0}")]
    InvalidEndComparison(ForCompError, FilePosition),
    #[error("erroring declaring identifier: {0}")]
    DeclareError(crate::util::scope::Error, FilePosition),
}

pub fn handle_import_oracles_body(
    ctx: &mut ParsePackageContext,
    ast: Pair<Rule>,
) -> Result<(), ParsePackageError> {
    let pkg_name = ctx.pkg_name;
    assert_eq!(ast.as_rule(), Rule::import_oracles_body);

    for entry in ast.into_inner() {
        match entry.as_rule() {
            Rule::import_oracles_oracle_sig => {
                let span = entry.as_span();
                let source_span = SourceSpan::from(span.start()..span.end());
                let sig = handle_oracle_imports_oracle_sig(ctx, entry)?;
                if ctx
                    .imported_oracles
                    .insert(sig.name.clone(), (sig.clone(), source_span))
                    .is_some()
                {
                    return Err(OracleAlreadyImportedError {
                        source_code: NamedSource::new(ctx.file_name, ctx.file_content.to_string()),
                        at: source_span,
                        oracle_name: sig.name.clone(),
                    }
                    .into());
                }

                ctx.scope
                    .declare(
                        &sig.name,
                        Declaration::Oracle(
                            OracleContext::Package {
                                pkg_name: pkg_name.to_string(),
                            },
                            sig.clone(),
                        ),
                        // we already checked that the oracle has not yet been imported, so this
                        // shouldn't fail?
                    )
                    .unwrap();
            }

            _ => unreachable!(),
        }
    }
    Ok(())
}

pub fn handle_types_list(types: Pair<Rule>) -> Vec<String> {
    types
        .into_inner()
        .map(|entry| entry.as_str().to_string())
        .collect()
}
