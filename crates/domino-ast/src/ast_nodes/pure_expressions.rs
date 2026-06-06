use crate::{
    arena::Ref,
    ast_nodes::{
        identifier::{
            GameConstValueIdentifierKind, Identifier, IdentifierKind,
            PackageConstValueIdentifierKind,
        },
        list::{Comma, List},
        InArena, Indexable, ListItem, NodeType, PaddedRef, Parsable, Trivia,
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

#[derive(Debug, Clone)]
pub enum PureExpression<IdentKind: IdentifierKind> {
    TableIndex(Ref<TableIndexExpression<IdentKind>>),
    Paren(Ref<ParenExpression<IdentKind>>),
    Tuple(Ref<TupleExpression<IdentKind>>),
    Call(Ref<CallExpression<IdentKind>>),
    Identifier(Ref<Identifier<IdentKind>>),
    BinOp(Ref<BinOpExpression<IdentKind>>),
    UnOp(Ref<UnOpExpression<IdentKind>>),

    String,
    Int,
}

impl<IK: IdentifierKind> ListItem for PureExpression<IK> {
    const LIST_RULE: Rule = Rule::expr_list;
}

#[derive(Debug, Clone)]
pub struct BinOpExpression<IdentKind: IdentifierKind> {
    pub lhs: Ref<PureExpression<IdentKind>>,
    pub pre_op_trivia: Ref<Trivia>,
    pub op: BinOp,
    pub post_op_trivia: Ref<Trivia>,
    pub rhs: Ref<PureExpression<IdentKind>>,
}

#[derive(Debug, Clone)]
pub struct UnOpExpression<IdentKind: IdentifierKind> {
    pub op: UnOp,
    pub trivia: Ref<Trivia>,
    pub expr: Ref<PureExpression<IdentKind>>,
}

/// A list of expressions, usually comma separated. Usually surrounded by parenthises
#[allow(type_alias_bounds)]
pub type ExprList<IdentKind: IdentifierKind> = List<PureExpression<IdentKind>, Comma>;

pub type PureConstPackageExpressionList = ExprList<PackageConstValueIdentifierKind>;

pub type PureConstGameExpressionList = ExprList<GameConstValueIdentifierKind>;

#[derive(Debug, Clone, Copy)]
pub struct TableIndexExpression<IK: IdentifierKind> {
    pub table_name: Ref<Identifier<IK>>,

    pub table_name_trivia: Ref<Trivia>,

    pub index: PaddedRef<PureExpression<IK>>,
}

#[derive(Debug, Clone, Copy)]
pub struct ParenExpression<IdentKind: IdentifierKind>(pub PaddedRef<Identifier<IdentKind>>);

#[derive(Debug, Clone, Copy)]
pub struct CallExpression<IdentKind: IdentifierKind> {
    pub name: Ref<PureExpression<IdentKind>>,
    pub trivia: Ref<Trivia>,
    pub args: Ref<ExprList<IdentKind>>,
}

#[derive(Debug, Clone)]
pub struct TupleExpression<IdentKind: IdentifierKind>(pub Ref<ExprList<IdentKind>>);

// crate::ast_nodes::list::impl_list!(
//     PureExpression<PackageConstValueIdentifierKind>,
//     Rule::arg_list_expr,
//     Rule::padded_expr,
//     Comma,
//     Rule::comma
// );
// crate::ast_nodes::list::impl_list!(
//     PureExpression<GameConstValueIdentifierKind>,
//     Rule::arg_list_expr,
//     Rule::padded_expr,
//     Comma,
//     Rule::comma
// );

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

fn parse_leftassoc<IK: IdentifierKind>(
    file_id: crate::source::FileId,
    state: &mut crate::State,
    pair: crate::Pair,
) -> PureExpression<IK>
where
    PureExpression<IK>: Parsable,
    BinOpExpression<IK>: NodeType + InArena + Indexable,
{
    let mut pairs = pair.into_inner();
    let first = pairs.next().unwrap();

    let mut lhs_loc = SourceLocation::from_file_and_pair(file_id, &first);
    let mut lhs_raw = PureExpression::<IK>::parse(file_id, state, first);

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
        let rhs = PureExpression::parse_ref(file_id, state, rhs_pair);

        let binop_expr = BinOpExpression {
            lhs,
            pre_op_trivia: lhs_trailing,
            op,
            post_op_trivia: rhs_leading,
            rhs,
        };

        lhs_loc.end = rhs_loc.end;

        let binop_expr = Ref::from_parsed(state, lhs_loc, binop_expr);
        lhs_raw = PureExpression::BinOp(binop_expr);
    }

    lhs_raw
}

fn parse_unary<IK: IdentifierKind>(
    file_id: crate::source::FileId,
    state: &mut crate::State,
    pair: crate::Pair,
) -> PureExpression<IK>
where
    PureExpression<IK>: Parsable,
    UnOpExpression<IK>: NodeType + InArena + Indexable,
{
    debug_assert_eq!(pair.as_rule(), Rule::unary);

    let loc = SourceLocation::from_file_and_pair(file_id, &pair);

    let mut inner = pair.into_inner();

    match inner.peek().unwrap().as_rule() {
        Rule::atom => PureExpression::parse(file_id, state, inner.next().unwrap()),
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

            PureExpression::UnOp(unop)
        }
        _ => unreachable!(),
    }
}

fn parse_call<IK: IdentifierKind>(
    file_id: crate::source::FileId,
    state: &mut crate::State,
    pair: crate::Pair,
) -> PureExpression<IK>
where
    PureExpression<IK>: Parsable,
    ExprList<IK>: Parsable,
    Identifier<IK>: Parsable,
    CallExpression<IK>: NodeType + InArena + Indexable,
{
    let span = pair.as_span();
    let start = span.start() as u32;
    let mut fun_loc = SourceLocation::from_file_and_pair(file_id, &pair);
    let mut inner = pair.into_inner();

    let mut fun =
        PureExpression::Identifier(Identifier::parse_ref(file_id, state, inner.next().unwrap()));

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
        fun = PureExpression::Call(Ref::from_parsed(state, loc, call));
        fun_loc.end = end;
    }

    fun
}

// Pulling this function out allows us to make the Parsable trait implementation on PureExpression
// concrete, which lets us avoid a trait bound dependency loop.
fn parse_pure_expression<IK: IdentifierKind>(
    file_id: FileId,
    state: &mut State,
    pair: crate::Pair,
) -> PureExpression<IK>
where
    PureExpression<IK>: Parsable,
    List<PureExpression<IK>, Comma>: Parsable,
    Identifier<IK>: Parsable,
    TableIndexExpression<IK>: Parsable,
    TupleExpression<IK>: Parsable,
    ParenExpression<IK>: Parsable,
    BinOpExpression<IK>: NodeType + InArena + Indexable,
    UnOpExpression<IK>: NodeType + InArena + Indexable,
    CallExpression<IK>: NodeType + InArena + Indexable,
{
    match pair.as_rule() {
        Rule::atom => parse_pure_expression(file_id, state, pair.into_inner().next().unwrap()),

        Rule::expr | Rule::l_and | Rule::compn | Rule::addtn | Rule::multn => {
            parse_leftassoc::<IK>(file_id, state, pair)
        }

        Rule::unary => parse_unary(file_id, state, pair),
        Rule::call => parse_call(file_id, state, pair),

        Rule::table_expr => {
            PureExpression::TableIndex(TableIndexExpression::parse_ref(file_id, state, pair))
        }
        Rule::paren_expr => PureExpression::Paren(ParenExpression::parse_ref(file_id, state, pair)),
        Rule::tuple_expr => PureExpression::Tuple(TupleExpression::parse_ref(file_id, state, pair)),

        Rule::string_literal => PureExpression::String,
        Rule::int_literal => PureExpression::Int,

        _ => todo!(),
    }
}

impl Parsable for PureExpression<PackageConstValueIdentifierKind> {
    fn parse(file_id: FileId, state: &mut State, pair: crate::Pair) -> Self {
        parse_pure_expression(file_id, state, pair)
    }
}

impl Parsable for PureExpression<GameConstValueIdentifierKind> {
    fn parse(file_id: FileId, state: &mut State, pair: crate::Pair) -> Self {
        parse_pure_expression::<GameConstValueIdentifierKind>(file_id, state, pair)
    }
}

impl<IK: IdentifierKind> Parsable for TableIndexExpression<IK>
where
    Identifier<IK>: Parsable,
    PaddedRef<PureExpression<IK>>: Parsable,
    Self: Indexable + InArena + NodeType,
{
    fn parse(file_id: FileId, state: &mut State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::table_expr);

        let mut inner = pair.into_inner();

        let ident_pair = inner.next().unwrap();
        let trivia_pair = inner.next().unwrap();
        let index_pair = inner.next().unwrap();

        let ident = Identifier::parse_ref(file_id, state, ident_pair);
        let trivia = Trivia::parse_ref(file_id, state, trivia_pair);
        let index = PaddedRef::parse(file_id, state, index_pair);

        TableIndexExpression {
            table_name: ident,
            table_name_trivia: trivia,
            index,
        }
    }
}

impl<IK: IdentifierKind> Parsable for ParenExpression<IK>
where
    PaddedRef<Identifier<IK>>: Parsable,
    Self: Indexable + InArena + NodeType,
{
    fn parse(file_id: FileId, state: &mut State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::paren_expr);

        ParenExpression(PaddedRef::parse(
            file_id,
            state,
            pair.into_inner().next().unwrap(),
        ))
    }
}

impl<IK: IdentifierKind> Parsable for TupleExpression<IK>
where
    PaddedRef<Identifier<IK>>: Parsable,
    Self: Indexable + InArena + NodeType,
    List<PureExpression<IK>, Comma>: Parsable,
{
    fn parse(file_id: FileId, state: &mut State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::tuple_expr);

        TupleExpression(ExprList::parse_ref(
            file_id,
            state,
            pair.into_inner().next().unwrap(),
        ))
    }
}

#[cfg(test)]
mod static_checks {
    use super::*;
    use crate::ast_nodes::{
        identifier::{PackageConstValueIdentifier, PackageConstValueIdentifierKind},
        PaddedRef, Parsable,
    };

    fn impls_parsable<T: Parsable>() {}
    fn impls_indexable<T: Indexable>() {}

    #[allow(dead_code)]
    fn ensure_traits_impld_for_oracle() {
        impls_parsable::<PackageConstValueIdentifier>();
        impls_parsable::<PaddedRef<PackageConstValueIdentifier>>();
        impls_parsable::<TableIndexExpression<PackageConstValueIdentifierKind>>();
        impls_parsable::<TupleExpression<PackageConstValueIdentifierKind>>();
        impls_parsable::<ExprList<PackageConstValueIdentifierKind>>();
        impls_indexable::<ExprList<PackageConstValueIdentifierKind>>();
        impls_parsable::<PureExpression<PackageConstValueIdentifierKind>>();
    }
}
