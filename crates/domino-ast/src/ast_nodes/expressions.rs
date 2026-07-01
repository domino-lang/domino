//! This module contains the types for a unified expressions type.
//! It unifies the expressions in oracle code, which may be effectful (abort, sample, invoke),
//! and those in constant positions, which may not.
//!
//! Main goals:
//!  -  Make illegal states _representable_: we want to be able to parse code where effectful
//!     expressions are used in illegal places, so we can generate nice error messges.
//!  -  A mechanism for validating and making easy to reuse type invariants that effectful expressions
//!     do not occor in illegal positions.
//!
//! Nice benefit: Less code duplication between expression types.
//!
//! Approach:
//!  -  We have a single Expression type that is generic over an ExpressionKind trait. That trait
//!     might have associated types for the respective IdentifierKinds used in the given context.
//!  -  We define resolution types for pure expressios, which then only have the variants legal in
//!     pure contexts, and have the regular expression subtype as data.

use crate::{
    arena::Ref,
    ast_nodes::{
        identifier::{Identifier, OracleIdentifier, ValueIdentifierKind},
        list::{Comma, List},
        parse_ref,
        types::{Type, TypeKind},
        InArena, Indexable, NodeType, Parsable, Trivia,
    },
    source::{FileId, SourceLocation},
    Rule, State,
};

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum UnOp {
    Not,
    Neg,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum BinOp {
    Eq,
    Neq,
    Lte,
    Lt,
    Gte,
    Gt,

    Add,
    Sub,
    Mul,
    Div,
    Mod,

    And,
    Or,
}

pub trait ExpressionKind {
    type TypeKind: TypeKind;
    type ValueIdentifierKind: ValueIdentifierKind;
}

#[derive(Debug, Clone, Copy)]
pub enum Expression<EK: ExpressionKind> {
    TableIndex(Ref<TableIndexExpression<EK>>),
    Paren(Ref<ParenExpression<EK>>),
    Tuple(Ref<TupleExpression<EK>>),
    Call(Ref<CallExpression<EK>>),
    Identifier(Ref<Identifier<EK::ValueIdentifierKind>>),
    BinOp(Ref<BinOpExpression<EK>>),
    UnOp(Ref<UnOpExpression<EK>>),

    Invoke(Ref<OracleInvocationExpression<EK>>),
    Sample(Ref<SampleExpression<EK>>),

    String,
    Int,
}

/// A list of expressions.
/// Usually comma separated and surrounded by parentheses
pub type ExprList<EK: ExpressionKind> = List<Expression<EK>, Comma>;

#[derive(Debug, Clone, Copy)]
pub struct BinOpExpression<EK: ExpressionKind> {
    pub lhs: Ref<Expression<EK>>,
    pub pre_op_trivia: Ref<Trivia>,
    pub op: BinOp,
    pub post_op_trivia: Ref<Trivia>,
    pub rhs: Ref<Expression<EK>>,
}

#[derive(Debug, Clone, Copy)]
pub struct UnOpExpression<EK: ExpressionKind> {
    pub op: UnOp,
    pub trivia: Ref<Trivia>,
    pub expr: Ref<Expression<EK>>,
}

#[derive(Debug, Clone, Copy)]
pub struct OracleInvocationExpression<EK: ExpressionKind> {
    /// The name of the invoked oracle.
    pub oracle_name: Ref<OracleIdentifier>,

    /// Trivia between name and (
    pub oracle_name_trivia: Ref<Trivia>,

    pub args: Ref<ExprList<EK>>,
}

#[derive(Debug, Clone, Copy)]
pub struct TableIndexExpression<EK: ExpressionKind> {
    pub table_name: Ref<Identifier<EK::ValueIdentifierKind>>,
    pub table_name_trivia: Ref<Trivia>,
    pub index_trivia: Ref<Trivia>,
    pub index: Ref<Expression<EK>>,
    pub index_trailing_trivia: Ref<Trivia>,
}

#[derive(Debug, Clone, Copy)]
pub struct SampleExpression<EK: ExpressionKind> {
    pub ty: Ref<Type<EK::TypeKind>>,
    // TODO: sample names
}

#[derive(Debug, Clone, Copy)]
pub struct ParenExpression<EK: ExpressionKind> {
    pub expr_trivia: Ref<Trivia>,
    pub expr: Ref<Expression<EK>>,
    pub trailing_trivia: Ref<Trivia>,
}

#[derive(Debug, Clone, Copy)]
pub struct CallExpression<EK: ExpressionKind> {
    pub name: Ref<Expression<EK>>,
    pub trivia: Ref<Trivia>,
    pub args: Ref<ExprList<EK>>,
}

#[derive(Debug, Clone, Copy)]
pub struct TupleExpression<EK: ExpressionKind>(pub Ref<ExprList<EK>>);

impl<EK: ExpressionKind> Parsable for TupleExpression<EK>
where
    Identifier<EK::ValueIdentifierKind>: Parsable,
    Self: Indexable + InArena + NodeType,
    ExprList<EK>: Parsable,
{
    const RULE: Rule = Rule::tuple_expr;

    fn parse_inner(file_id: FileId, state: &mut State, pair: crate::Pair) -> Self {
        TupleExpression(ExprList::parse_ref(
            file_id,
            state,
            pair.into_inner().next().unwrap(),
        ))
    }
}

impl<EK: ExpressionKind> Parsable for OracleInvocationExpression<EK>
where
    Self: Indexable + InArena + NodeType,
    ExprList<EK>: Parsable,
{
    const RULE: Rule = Rule::invoke;

    fn parse_inner(
        file_id: crate::source::FileId,
        state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        let mut inner = pair.into_inner();
        let _invoke = inner.next().unwrap();
        let name = OracleIdentifier::parse_ref(file_id, state, inner.next().unwrap());
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
    Self: Indexable + InArena + NodeType,
    Type<EK::TypeKind>: Parsable,
{
    const RULE: Rule = Rule::sample;

    fn parse_inner(file_id: FileId, state: &mut State, pair: crate::Pair) -> Self {
        SampleExpression {
            ty: Type::parse_ref(file_id, state, pair.into_inner().next().unwrap()),
        }
    }
}

#[macro_export]
macro_rules! impl_expr {
    ($expr_kind:ty) => {
        impl crate::ast_nodes::ListItem for crate::ast_nodes::expressions::Expression<$expr_kind> {
            const LIST_RULE: crate::Rule = crate::Rule::expr_list;
        }

        impl crate::ast_nodes::Parsable
            for crate::ast_nodes::expressions::TableIndexExpression<$expr_kind>
        {
            const RULE: crate::Rule = crate::Rule::table_expr;

            fn parse_inner(
                file_id: crate::source::FileId,
                state: &mut crate::state::State,
                pair: crate::Pair,
            ) -> Self {
                crate::ast_nodes::expressions::parse_table_index_expr::<$expr_kind>(
                    file_id, state, pair,
                )
            }
        }

        impl crate::ast_nodes::Parsable
            for crate::ast_nodes::expressions::ParenExpression<$expr_kind>
        {
            const RULE: crate::Rule = crate::Rule::paren_expr;

            fn parse_inner(
                file_id: crate::source::FileId,
                state: &mut crate::state::State,
                pair: crate::Pair,
            ) -> Self {
                crate::ast_nodes::expressions::parse_paren_expression::<$expr_kind>(
                    file_id, state, pair,
                )
            }
        }

        impl crate::ast_nodes::Parsable for crate::ast_nodes::expressions::Expression<$expr_kind> {
            const RULE: crate::Rule = crate::Rule::expr;

            fn parse_inner(
                file_id: crate::source::FileId,
                state: &mut crate::state::State,
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
    file_id: crate::source::FileId,
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
    BinOpExpression<EK>: NodeType + InArena + Indexable,
    UnOpExpression<EK>: NodeType + InArena + Indexable,
    CallExpression<EK>: NodeType + InArena + Indexable,
{
    let mut pairs = pair.into_inner();
    let first = pairs.next().unwrap();

    let mut lhs_loc = SourceLocation::from_file_and_pair(file_id, &first);
    let mut lhs_raw = parse_pure_expression(file_id, state, first);

    if pairs.peek().is_none() {
        return lhs_raw;
    }

    while let Some(lhs_trailing_pair) = pairs.next() {
        let op_pair = pairs.next().unwrap();
        let rhs_leading_pair = pairs.next().unwrap();
        let rhs_pair = pairs.next().unwrap();
        let rhs_loc = super::trimmed_loc(file_id, &rhs_pair);

        let op = binop_from_pair(&op_pair);

        let lhs = Ref::from_parsed(state, lhs_loc, lhs_raw);
        let lhs_trailing = Trivia::parse_ref(file_id, state, lhs_trailing_pair);
        let rhs_leading = Trivia::parse_ref(file_id, state, rhs_leading_pair);
        let rhs = parse_ref(file_id, state, rhs_pair, parse_pure_expression);

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
    BinOpExpression<EK>: NodeType + InArena + Indexable,
    UnOpExpression<EK>: NodeType + InArena + Indexable,
    CallExpression<EK>: NodeType + InArena + Indexable,
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
    file_id: crate::source::FileId,
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
    BinOpExpression<EK>: NodeType + InArena + Indexable,
    UnOpExpression<EK>: NodeType + InArena + Indexable,
    CallExpression<EK>: NodeType + InArena + Indexable,
{
    let loc = SourceLocation::from_file_and_pair(file_id, &pair);

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

            let inner_unary_loc = SourceLocation::from_file_and_pair(file_id, &inner_unary_pair);
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
    file_id: crate::source::FileId,
    state: &mut crate::State,
    pair: crate::Pair,
) -> Expression<EK>
where
    Expression<EK>: Parsable,
    ExprList<EK>: Parsable,
    Identifier<EK::ValueIdentifierKind>: Parsable,
    CallExpression<EK>: NodeType + InArena + Indexable,
{
    let span = pair.as_span();
    let start = span.start() as u32;
    let mut fun_loc = SourceLocation::from_file_and_pair(file_id, &pair);
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
    UnOpExpression<EK>: NodeType + InArena + Indexable,
    CallExpression<EK>: NodeType + InArena + Indexable,
    BinOpExpression<EK>: Indexable + InArena + NodeType,
{
    let mut inner = pair.into_inner();
    let table_name = Identifier::parse_ref(file_id, state, inner.next().unwrap());
    let table_name_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
    let index_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
    let index = parse_ref(file_id, state, inner.next().unwrap(), parse_pure_expression);
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
    ParenExpression<EK>: Indexable + InArena + NodeType,
    OracleInvocationExpression<EK>: Parsable,
    SampleExpression<EK>: Parsable,
    CallExpression<EK>: NodeType + InArena + Indexable,
    BinOpExpression<EK>: NodeType + InArena + Indexable,
    UnOpExpression<EK>: NodeType + InArena + Indexable,
{
    let mut inner = pair.into_inner();

    ParenExpression {
        expr_trivia: Trivia::parse_ref(file_id, state, inner.next().unwrap()),
        expr: parse_ref(file_id, state, inner.next().unwrap(), parse_pure_expression),
        trailing_trivia: Trivia::parse_ref(file_id, state, inner.next().unwrap()),
    }
}

pub(crate) fn binop_from_pair(pair: &crate::Pair) -> BinOp {
    match pair.as_str() {
        "or" => BinOp::Or,
        "and" => BinOp::And,

        "+" => BinOp::Add,
        "-" => BinOp::Sub,
        "*" => BinOp::Mul,
        "/" => BinOp::Div,
        "%" => BinOp::Mod,

        "==" => BinOp::Eq,
        "!=" => BinOp::Neq,
        ">=" => BinOp::Gte,
        ">" => BinOp::Gt,
        "<=" => BinOp::Lte,
        "<" => BinOp::Lt,

        _ => unreachable!(),
    }
}
