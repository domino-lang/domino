use crate::{expressions::Expression, identifier::Identifier, package::OracleSig, types::Type};

use super::error::{Error, Result};
use super::{error, Rule};

use pest::iterators::Pair;

// TODO: identifier is optional
pub fn handle_arglist(arglist: Pair<Rule>) -> Vec<(String, Type)> {
    arglist
        .into_inner()
        .map(|arg| {
            let mut inner = arg.into_inner();
            let id = inner.next().unwrap().as_str();
            let tipe = handle_type(inner.next().unwrap());
            (id.to_string(), tipe)
        })
        .collect()
}

pub fn handle_oracle_sig(oracle_sig: Pair<Rule>) -> OracleSig {
    let mut inner = oracle_sig.into_inner();
    let name = inner.next().unwrap().as_str();
    let maybe_arglist = inner.next().unwrap();
    let args = if maybe_arglist.as_str() == "" {
        vec![]
    } else {
        handle_arglist(maybe_arglist.into_inner().next().unwrap())
    };

    let maybe_tipe = inner.next();
    let tipe = match maybe_tipe {
        None => Type::Empty,
        Some(t) => handle_type(t),
    };

    OracleSig {
        name: name.to_string(),
        tipe,
        args,
    }
}

pub fn handle_expression(expr: Pair<Rule>) -> Expression {
    match expr.as_rule() {
        // expr_equals | expr_not_equals | fn_call | table_access | identifier
        Rule::expr_add => {
            let mut inner = expr.into_inner();
            let lhs = handle_expression(inner.next().unwrap());
            let rhs = handle_expression(inner.next().unwrap());
            Expression::Add(Box::new(lhs), Box::new(rhs))
        }
        Rule::expr_sub => {
            let mut inner = expr.into_inner();
            let lhs = handle_expression(inner.next().unwrap());
            let rhs = handle_expression(inner.next().unwrap());
            Expression::Sub(Box::new(lhs), Box::new(rhs))
        }
        Rule::expr_mul => {
            let mut inner = expr.into_inner();
            let lhs = handle_expression(inner.next().unwrap());
            let rhs = handle_expression(inner.next().unwrap());
            Expression::Mul(Box::new(lhs), Box::new(rhs))
        }
        Rule::expr_div => {
            let mut inner = expr.into_inner();
            let lhs = handle_expression(inner.next().unwrap());
            let rhs = handle_expression(inner.next().unwrap());
            Expression::Div(Box::new(lhs), Box::new(rhs))
        }
        Rule::expr_and => Expression::And(expr.into_inner().map(handle_expression).collect()),
        Rule::expr_or => Expression::Or(expr.into_inner().map(handle_expression).collect()),
        Rule::expr_xor => Expression::Xor(expr.into_inner().map(handle_expression).collect()),
        Rule::expr_not => {
            let mut inner = expr.into_inner();
            let content = handle_expression(inner.next().unwrap());
            Expression::Not(Box::new(content))
        }
        Rule::expr_equals => Expression::Equals(expr.into_inner().map(handle_expression).collect()),
        Rule::expr_not_equals => Expression::Not(Box::new(Expression::Equals(
            expr.into_inner().map(handle_expression).collect(),
        ))),
        Rule::expr_none => {
            let tipe = handle_type(expr.into_inner().next().unwrap());
            Expression::None(tipe)
        }
        Rule::expr_some => {
            let expr = handle_expression(expr.into_inner().next().unwrap());
            Expression::Some(Box::new(expr))
        }
        Rule::expr_unwrap => {
            let expr = handle_expression(expr.into_inner().next().unwrap());
            Expression::Unwrap(Box::new(expr))
        }
        Rule::expr_newtable => {
            let mut inner = expr.into_inner();
            let idxtipe = handle_type(inner.next().unwrap());
            let valtipe = handle_type(inner.next().unwrap());
            Expression::Typed(
                Type::Table(Box::new(idxtipe), Box::new(valtipe)),
                Box::new(Expression::EmptyTable),
            )
        }
        Rule::table_access => {
            let mut inner = expr.into_inner();
            let ident = inner.next().unwrap().as_str();
            let expr = handle_expression(inner.next().unwrap());
            Expression::TableAccess(Identifier::new_scalar(ident), Box::new(expr))
        }
        Rule::fn_call => {
            let mut inner = expr.into_inner();
            let ident = inner.next().unwrap().as_str();
            let args = match inner.next() {
                None => vec![],
                Some(inner_args) => inner_args.into_inner().map(handle_expression).collect(),
            };
            Expression::FnCall(Identifier::new_scalar(ident), args)
        }
        Rule::identifier => Identifier::new_scalar(expr.as_str()).to_expression(),
        Rule::literal_boolean => {
            let litval = expr.as_str().to_string();
            Expression::BooleanLiteral(litval)
        }
        Rule::literal_integer => {
            let litval = expr.as_str().to_string();
            Expression::IntegerLiteral(litval)
        }
        Rule::literal_emptyset => {
            let tipe = handle_type(expr.into_inner().next().unwrap());
            Expression::Typed(Type::Set(Box::new(tipe)), Box::new(Expression::Set(vec![])))
        }
        Rule::expr_tuple => Expression::Tuple(expr.into_inner().map(handle_expression).collect()),
        Rule::expr_list => Expression::List(expr.into_inner().map(handle_expression).collect()),
        Rule::expr_set => Expression::Set(expr.into_inner().map(handle_expression).collect()),
        _ => unreachable!("Unhandled expression {:#?}", expr),
    }
}

pub fn handle_type(tipe: Pair<Rule>) -> Type {
    match tipe.as_rule() {
        Rule::type_empty => Type::Empty,
        Rule::type_integer => Type::Integer,
        Rule::type_bool => Type::Boolean,
        Rule::type_string => Type::String,
        Rule::type_maybe => Type::Maybe(Box::new(handle_type(tipe.into_inner().next().unwrap()))),
        Rule::type_bits => Type::Bits(tipe.into_inner().next().unwrap().as_str().to_string()),
        Rule::type_tuple => Type::Tuple(tipe.into_inner().map(handle_type).collect()),
        Rule::type_table => {
            let mut inner = tipe.into_inner();
            let indextype = handle_type(inner.next().unwrap());
            let valuetype = handle_type(inner.next().unwrap());
            Type::Table(Box::new(indextype), Box::new(valuetype))
        }
        Rule::type_fn => {
            let mut inner = tipe.into_inner();
            let argtipes = inner
                .next()
                .unwrap()
                .into_inner()
                .map(|spec| handle_type(spec.into_inner().next().unwrap()))
                .collect();
            let tipe = handle_type(inner.next().unwrap());
            Type::Fn(argtipes, Box::new(tipe))
        }
        Rule::type_userdefined => Type::UserDefined(tipe.as_str().to_string()),
        _ => {
            unreachable!("{:#?}", tipe)
        }
    }
}

pub fn handle_params_def_list(
    ast: Pair<Rule>,
    defined_consts: &[(String, Type)],
) -> Result<Vec<(String, Expression)>> {
    ast.into_inner()
        .map(|inner| {
            //let inner = inner.into_inner().next().unwrap();

            let mut inner = inner.into_inner();
            let left_ast = inner.next().unwrap();
            let left_span = left_ast.as_span();
            let left = left_ast.as_str();

            let right_ast = inner.next().unwrap();
            let right_span = right_ast.as_span();
            let right_str = right_ast.as_str();

            let right = handle_expression(right_ast);

            match &right {
                Expression::BooleanLiteral(_)
                | Expression::StringLiteral(_)
                | Expression::IntegerLiteral(_) => {}
                Expression::Identifier(Identifier::Scalar(ident)) => {
                    if !defined_consts
                        .iter()
                        .any(|(defd_name, _)| ident == defd_name)
                    {
                        return Err(Error::UndefinedIdentifer(ident.clone()).with_span(right_span));
                    }
                }
                _ => {
                    return Err(Error::IllegalExpression(right.clone()).with_span(right_span));
                }
            }

            Ok((left.to_owned(), right.clone()))
        })
        .collect()
}

pub fn handle_types_def_list(ast: Pair<Rule>, inst_name: &str) -> Result<Vec<(Type, Type)>> {
    ast.into_inner()
        .map(|def_spec| handle_types_def_spec(def_spec, inst_name))
        .collect()
}

pub fn handle_types_def_spec(ast: Pair<Rule>, inst_name: &str) -> Result<(Type, Type)> {
    println!(">>>> {}", ast.as_str());
    let mut iter = ast.into_inner();

    let fst = iter.next().unwrap();
    println!(">>>>>> {}", fst.as_str());

    let snd = iter.next().unwrap();

    let snd_span = snd.as_span();
    let snd_type = handle_type(snd);

    let place = crate::transforms::resolvetypes::Place::Types {
        inst_name: inst_name.to_string(),
        type_name: format!("{:?}", fst.as_str()),
    };

    let tf = crate::transforms::resolvetypes::ResolveTypesTypeTransform::new(place);
    use crate::transforms::TypeTransform;

    if let Err(err) = tf.transform_type(&snd_type) {
        return Err(error::Error::from(err).with_span(snd_span));
    }

    Ok((handle_type(fst), snd_type))
}

pub fn handle_const_decl(ast: Pair<Rule>) -> (String, Type) {
    let mut inner = ast.into_inner();
    let name = inner.next().unwrap().as_str().to_owned();
    let tipe = handle_type(inner.next().unwrap());

    (name, tipe)
}
