use domino_ast::{
    arena::Ref,
    ast_nodes::{
        expressions::{self, *},
        identifier::{Identifier, OracleImportIdentifier},
        list::{Comma, List},
        types, InArena, NodeType, Trivia,
    },
    source::{FileId, SourceLocation},
    State,
};

use crate::{parse_ref, Parsable, Rule};

impl<EK: expressions::ExpressionKind> Parsable for expressions::TupleExpression<EK>
where
    Identifier<EK::ValueIdentifierKind>: Parsable,
    Self: InArena + NodeType,
    expressions::ExprList<EK>: Parsable,
{
    const RULE: Rule = Rule::tuple_expr;

    fn parse_inner(file_id: FileId, state: &mut State, pair: crate::Pair) -> Self {
        expressions::TupleExpression(ExprList::parse_ref(
            file_id,
            state,
            pair.into_inner().next().unwrap(),
        ))
    }
}

impl<EK: ExpressionKind> Parsable for OracleInvocationExpression<EK>
where
    Self: InArena + NodeType,
    ExprList<EK>: Parsable,
{
    const RULE: Rule = Rule::invoke;

    fn parse_inner(
        file_id: domino_ast::source::FileId,
        state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        let mut inner = pair.into_inner();
        let _invoke = inner.next().unwrap();
        let name = OracleImportIdentifier::parse_ref(file_id, state, inner.next().unwrap());
        let trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let expr_list_pair = ExprList::parse_ref(file_id, state, inner.next().unwrap());

        OracleInvocationExpression {
            oracle_name: name,
            oracle_name_trivia: trivia,
            args: expr_list_pair,
        }
    }
}

impl<EK: ExpressionKind> Parsable for SampleExpression<EK>
where
    Self: InArena + NodeType,
    types::Type<EK::TypeKind>: Parsable,
{
    const RULE: Rule = Rule::sample;

    fn parse_inner(file_id: FileId, state: &mut State, pair: crate::Pair) -> Self {
        SampleExpression {
            ty: types::Type::parse_ref(file_id, state, pair.into_inner().next().unwrap()),
        }
    }
}

#[macro_export]
macro_rules! impl_expr {
    ($expr_kind:ty) => {
        impl crate::ListItem for domino_ast::ast_nodes::expressions::Expression<$expr_kind> {
            const LIST_RULE: crate::Rule = crate::Rule::expr_list;
        }

        impl crate::Parsable
            for domino_ast::ast_nodes::expressions::TableIndexExpression<$expr_kind>
        {
            const RULE: crate::Rule = crate::Rule::table_expr;

            fn parse_inner(
                file_id: domino_ast::source::FileId,
                state: &mut domino_ast::State,
                pair: crate::Pair,
            ) -> Self {
                crate::ast_nodes::expressions::parse_table_index_expr::<$expr_kind>(
                    file_id, state, pair,
                )
            }
        }

        impl crate::Parsable for domino_ast::ast_nodes::expressions::ParenExpression<$expr_kind> {
            const RULE: crate::Rule = crate::Rule::paren_expr;

            fn parse_inner(
                file_id: domino_ast::source::FileId,
                state: &mut domino_ast::State,
                pair: crate::Pair,
            ) -> Self {
                crate::ast_nodes::expressions::parse_paren_expression::<$expr_kind>(
                    file_id, state, pair,
                )
            }
        }

        impl crate::Parsable for domino_ast::ast_nodes::expressions::Expression<$expr_kind> {
            const RULE: crate::Rule = crate::Rule::expr;

            fn parse_inner(
                file_id: domino_ast::source::FileId,
                state: &mut domino_ast::State,
                pair: crate::Pair,
            ) -> Self {
                crate::ast_nodes::expressions::parse_pure_expression::<$expr_kind>(
                    file_id, state, pair,
                )
            }
        }
    };
}

pub(crate) use impl_expr;

fn parse_leftassoc<EK: ExpressionKind>(
    file_id: domino_ast::source::FileId,
    state: &mut crate::State,
    pair: crate::Pair,
) -> Expression<EK>
where
    Expression<EK>: Parsable,
    ExprList<EK>: Parsable,
    Identifier<EK::ValueIdentifierKind>: Parsable,
    TableIndexExpression<EK>: Parsable,
    TupleExpression<EK>: Parsable,
    ParenExpression<EK>: Parsable,
    OracleInvocationExpression<EK>: Parsable,
    SampleExpression<EK>: Parsable,
    BinOpExpression<EK>: NodeType + InArena,
    UnOpExpression<EK>: NodeType + InArena,
    CallExpression<EK>: NodeType + InArena,
{
    let mut pairs = pair.into_inner();
    let first = pairs.next().unwrap();

    let mut lhs_loc = crate::util::trimmed_loc(file_id, &first);
    let mut lhs_raw = parse_pure_expression(file_id, state, first);

    if pairs.peek().is_none() {
        return lhs_raw;
    }

    while let Some(lhs_trailing_pair) = pairs.next() {
        let op_pair = pairs.next().unwrap();
        let rhs_leading_pair = pairs.next().unwrap();
        let rhs_pair = pairs.next().unwrap();
        let rhs_loc = crate::util::trimmed_loc(file_id, &rhs_pair);

        let op = op_pair
            .as_str()
            .parse()
            .expect("grammar enforces parsability");

        let lhs = Ref::from_parsed(state, lhs_loc, lhs_raw);
        let lhs_trailing = Trivia::parse_ref(file_id, state, lhs_trailing_pair);
        let rhs_leading = Trivia::parse_ref(file_id, state, rhs_leading_pair);
        let rhs = crate::parse_ref(file_id, state, rhs_pair, parse_pure_expression);

        let binop_expr = BinOpExpression {
            lhs,
            pre_op_trivia: lhs_trailing,
            op,
            post_op_trivia: rhs_leading,
            rhs,
        };

        lhs_loc.end = rhs_loc.end;

        let binop_expr = Ref::from_parsed(state, lhs_loc, binop_expr);
        lhs_raw = Expression::BinOp(binop_expr);
    }

    lhs_raw
}

// Pulling this function out allows us to make the Parsable trait implementation on Expression
// concrete, which lets us avoid a trait bound dependency loop.
pub(crate) fn parse_pure_expression<EK: ExpressionKind>(
    file_id: FileId,
    state: &mut State,
    pair: crate::Pair,
) -> Expression<EK>
where
    Expression<EK>: Parsable,
    ExprList<EK>: Parsable,
    Identifier<EK::ValueIdentifierKind>: Parsable,
    TableIndexExpression<EK>: Parsable,
    TupleExpression<EK>: Parsable,
    ParenExpression<EK>: Parsable,
    OracleInvocationExpression<EK>: Parsable,
    SampleExpression<EK>: Parsable,
    BinOpExpression<EK>: NodeType + InArena,
    UnOpExpression<EK>: NodeType + InArena,
    CallExpression<EK>: NodeType + InArena,
{
    match pair.as_rule() {
        Rule::atom => parse_pure_expression(file_id, state, pair.into_inner().next().unwrap()),

        Rule::expr | Rule::l_and | Rule::compn | Rule::addtn | Rule::multn => {
            parse_leftassoc::<EK>(file_id, state, pair)
        }

        Rule::unary => parse_unary(file_id, state, pair),
        Rule::call => parse_call(file_id, state, pair),

        Rule::table_expr => {
            Expression::TableIndex(TableIndexExpression::parse_ref(file_id, state, pair))
        }
        Rule::paren_expr => Expression::Paren(ParenExpression::parse_ref(file_id, state, pair)),
        Rule::tuple_expr => Expression::Tuple(TupleExpression::parse_ref(file_id, state, pair)),

        Rule::string_literal => Expression::String,
        Rule::int_literal => Expression::Int,

        Rule::invoke => {
            Expression::Invoke(OracleInvocationExpression::parse_ref(file_id, state, pair))
        }
        Rule::sample => Expression::Sample(SampleExpression::parse_ref(file_id, state, pair)),

        rule => todo!("{rule:?}"),
    }
}

fn parse_unary<EK: ExpressionKind>(
    file_id: domino_ast::source::FileId,
    state: &mut crate::State,
    pair: crate::Pair,
) -> Expression<EK>
where
    Expression<EK>: Parsable,
    List<Expression<EK>, Comma>: Parsable,
    Identifier<EK::ValueIdentifierKind>: Parsable,
    TableIndexExpression<EK>: Parsable,
    TupleExpression<EK>: Parsable,
    ParenExpression<EK>: Parsable,
    OracleInvocationExpression<EK>: Parsable,
    SampleExpression<EK>: Parsable,
    BinOpExpression<EK>: NodeType + InArena,
    UnOpExpression<EK>: NodeType + InArena,
    CallExpression<EK>: NodeType + InArena,
{
    let loc = crate::util::trimmed_loc(file_id, &pair);

    let mut inner = pair.into_inner();

    match inner.peek().unwrap().as_rule() {
        Rule::atom => parse_pure_expression(file_id, state, inner.next().unwrap()),
        Rule::unary_op => {
            let unary_op_pair = inner.next().unwrap();
            let trivia_pair = inner.next().unwrap();
            let inner_unary_pair = inner.next().unwrap();

            let op = match unary_op_pair.as_str() {
                "!" => UnOp::Not,
                "-" => UnOp::Neg,
                _ => unreachable!(),
            };

            let trivia = Trivia::parse_ref(file_id, state, trivia_pair);

            let inner_unary_loc = crate::util::trimmed_loc(file_id, &inner_unary_pair);
            let inner_unary = parse_unary(file_id, state, inner_unary_pair);
            let inner_unary_ref = Ref::from_parsed(state, inner_unary_loc, inner_unary);

            let unop = UnOpExpression {
                op,
                trivia,
                expr: inner_unary_ref,
            };

            let unop = Ref::from_parsed(state, loc, unop);

            Expression::UnOp(unop)
        }
        _ => unreachable!(),
    }
}

fn parse_call<EK: ExpressionKind>(
    file_id: domino_ast::source::FileId,
    state: &mut crate::State,
    pair: crate::Pair,
) -> Expression<EK>
where
    Expression<EK>: Parsable,
    ExprList<EK>: Parsable,
    Identifier<EK::ValueIdentifierKind>: Parsable,
    CallExpression<EK>: NodeType + InArena,
{
    let span = pair.as_span();
    let start = span.start() as u32;
    let mut fun_loc = crate::util::trimmed_loc(file_id, &pair);
    let mut inner = pair.into_inner();

    let mut fun =
        Expression::Identifier(Identifier::parse_ref(file_id, state, inner.next().unwrap()));

    while let Some(trivia) = inner.next() {
        let args_pair = inner.next().unwrap();
        let end = args_pair.as_span().end() as u32;

        let trivia = Trivia::parse_ref(file_id, state, trivia);
        let args = ExprList::parse_ref(file_id, state, args_pair);

        let loc = SourceLocation {
            file_id,
            start,
            end,
        };
        let call = CallExpression {
            name: Ref::from_parsed(state, fun_loc, fun),
            trivia,
            args,
        };
        fun = Expression::Call(Ref::from_parsed(state, loc, call));
        fun_loc.end = end;
    }

    fun
}

pub(crate) fn parse_table_index_expr<EK: ExpressionKind>(
    file_id: FileId,
    state: &mut State,
    pair: crate::Pair,
) -> TableIndexExpression<EK>
where
    Expression<EK>: Parsable,
    ExprList<EK>: Parsable,
    Identifier<EK::ValueIdentifierKind>: Parsable,
    TupleExpression<EK>: Parsable,
    ParenExpression<EK>: Parsable,
    TableIndexExpression<EK>: Parsable,
    OracleInvocationExpression<EK>: Parsable,
    SampleExpression<EK>: Parsable,
    UnOpExpression<EK>: NodeType + InArena,
    CallExpression<EK>: NodeType + InArena,
    BinOpExpression<EK>: NodeType + InArena,
{
    let mut inner = pair.into_inner();
    let table_name = Identifier::parse_ref(file_id, state, inner.next().unwrap());
    let table_name_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
    let index_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
    let index = crate::parse_ref(file_id, state, inner.next().unwrap(), parse_pure_expression);
    let index_trailing_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());

    TableIndexExpression {
        table_name,
        table_name_trivia,
        index_trivia,
        index,
        index_trailing_trivia,
    }
}

pub(crate) fn parse_paren_expression<EK: ExpressionKind>(
    file_id: FileId,
    state: &mut State,
    pair: crate::Pair,
) -> ParenExpression<EK>
where
    Expression<EK>: Parsable,
    ExprList<EK>: Parsable,
    Identifier<EK::ValueIdentifierKind>: Parsable,
    TableIndexExpression<EK>: Parsable,
    TupleExpression<EK>: Parsable,
    ParenExpression<EK>: Parsable,
    ParenExpression<EK>: InArena + NodeType,
    OracleInvocationExpression<EK>: Parsable,
    SampleExpression<EK>: Parsable,
    CallExpression<EK>: NodeType + InArena,
    BinOpExpression<EK>: NodeType + InArena,
    UnOpExpression<EK>: NodeType + InArena,
{
    let mut inner = pair.into_inner();

    ParenExpression {
        expr_trivia: Trivia::parse_ref(file_id, state, inner.next().unwrap()),
        expr: parse_ref(file_id, state, inner.next().unwrap(), parse_pure_expression),
        trailing_trivia: Trivia::parse_ref(file_id, state, inner.next().unwrap()),
    }
}
