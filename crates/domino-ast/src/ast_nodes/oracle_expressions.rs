use crate::{
    arena::Ref,
    ast_nodes::{
        identifier::{
            Identifier, OracleIdentifier, OracleValueIdentifier, PackageTypeIdentifierKind,
            TypeIdentifierKind,
        },
        list::{Comma, List},
        parse_ref,
        pure_expressions::{binop_from_pair, BinOp, UnOp},
        types::Type,
        InArena, Indexable, ListItem, NodeType, Parsable, Trivia,
    },
    source::{FileId, SourceLocation},
    Rule, State,
};

#[derive(Debug, Clone)]
pub enum OracleExpression {
    Invoke(Ref<OracleInvocationExpression>),
    TableIndex(Ref<TableIndexExpression>),
    Sample(Ref<SampleExpression<PackageTypeIdentifierKind>>),
    Paren(Ref<ParenExpression>),
    Tuple(Ref<TupleExpression>),
    Call(Ref<CallExpression>),
    Identifier(Ref<OracleValueIdentifier>),
    BinOp(Ref<BinOpExpression>),
    UnOp(Ref<UnOpExpression>),

    String,
    Int,
}

impl ListItem for OracleExpression {
    const LIST_RULE: Rule = Rule::expr_list;
}

#[derive(Debug, Clone)]
pub struct BinOpExpression {
    pub lhs: Ref<OracleExpression>,
    pub pre_op_trivia: Ref<Trivia>,
    pub op: BinOp,
    pub post_op_trivia: Ref<Trivia>,
    pub rhs: Ref<OracleExpression>,
}

#[derive(Debug, Clone)]
pub struct UnOpExpression {
    pub op: UnOp,
    pub trivia: Ref<Trivia>,
    pub expr: Ref<OracleExpression>,
}

#[derive(Debug, Clone, Copy)]
pub struct OracleInvocationExpression {
    /// The name of the invoked oracle.
    pub oracle_name: Ref<OracleIdentifier>,

    /// Trivia between name and (
    pub oracle_name_trivia: Ref<Trivia>,

    pub args: Ref<ExprList>,
}

/// A list of expressions, usually comma separated. Usually surrounded by parenthises
pub type ExprList = List<OracleExpression, Comma>;

#[derive(Debug, Clone, Copy)]
pub struct TableIndexExpression {
    pub table_name: Ref<OracleValueIdentifier>,
    pub table_name_trivia: Ref<Trivia>,
    pub index_trivia: Ref<Trivia>,
    pub index: Ref<OracleExpression>,
    pub index_trailing_trivia: Ref<Trivia>,
}

#[derive(Debug, Clone, Copy)]
pub struct SampleExpression<IK: TypeIdentifierKind> {
    pub ty: Ref<Type<IK>>,
    // TODO: sample names
}

#[derive(Debug, Clone, Copy)]
pub struct ParenExpression {
    pub expr_trivia: Ref<Trivia>,
    pub expr: Ref<OracleExpression>,
    pub trailing_trivia: Ref<Trivia>,
}

#[derive(Debug, Clone, Copy)]
pub struct CallExpression {
    pub name: Ref<OracleExpression>,
    pub trivia: Ref<Trivia>,
    pub args: Ref<ExprList>,
}

#[derive(Debug, Clone)]
pub struct TupleExpression(pub Ref<ExprList>);

fn parse_leftassoc(
    file_id: crate::source::FileId,
    state: &mut crate::State,
    pair: crate::Pair,
) -> OracleExpression {
    let mut pairs = pair.into_inner();
    let first = pairs.next().unwrap();

    let mut lhs_loc = SourceLocation::from_file_and_pair(file_id, &first);
    let mut lhs_raw = parse_expression(file_id, state, first);

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
        let rhs = parse_ref(file_id, state, rhs_pair, parse_expression);

        let binop_expr = BinOpExpression {
            lhs,
            pre_op_trivia: lhs_trailing,
            op,
            post_op_trivia: rhs_leading,
            rhs,
        };

        lhs_loc.end = rhs_loc.end;

        let binop_expr = Ref::from_parsed(state, lhs_loc, binop_expr);
        lhs_raw = OracleExpression::BinOp(binop_expr);
    }

    lhs_raw
}

fn parse_unary(
    file_id: crate::source::FileId,
    state: &mut crate::State,
    pair: crate::Pair,
) -> OracleExpression {
    let loc = SourceLocation::from_file_and_pair(file_id, &pair);

    let mut inner = pair.into_inner();

    match inner.peek().unwrap().as_rule() {
        Rule::atom => parse_expression(file_id, state, inner.next().unwrap()),
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

            OracleExpression::UnOp(unop)
        }
        _ => unreachable!(),
    }
}

impl Parsable for OracleInvocationExpression {
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

impl Parsable for TableIndexExpression {
    const RULE: Rule = Rule::table_expr;

    fn parse_inner(file_id: FileId, state: &mut State, pair: crate::Pair) -> Self {
        let mut inner = pair.into_inner();
        let table_name = Identifier::parse_ref(file_id, state, inner.next().unwrap());
        let table_name_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let index_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let index = parse_ref(file_id, state, inner.next().unwrap(), parse_expression);
        let index_trailing_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());

        TableIndexExpression {
            table_name,
            table_name_trivia,
            index_trivia,
            index,
            index_trailing_trivia,
        }
    }
}

impl<IK: TypeIdentifierKind> Parsable for SampleExpression<IK>
where
    Self: Indexable + InArena + NodeType,
    Type<IK>: Parsable,
{
    const RULE: Rule = Rule::sample;

    fn parse_inner(file_id: FileId, state: &mut State, pair: crate::Pair) -> Self {
        SampleExpression {
            ty: Type::parse_ref(file_id, state, pair.into_inner().next().unwrap()),
        }
    }
}

impl Parsable for ParenExpression {
    const RULE: Rule = Rule::paren_expr;

    fn parse_inner(file_id: FileId, state: &mut State, pair: crate::Pair) -> Self {
        let mut inner = pair.into_inner();

        ParenExpression {
            expr_trivia: Trivia::parse_ref(file_id, state, inner.next().unwrap()),
            expr: parse_ref(file_id, state, inner.next().unwrap(), parse_expression),
            trailing_trivia: Trivia::parse_ref(file_id, state, inner.next().unwrap()),
        }
    }
}

impl Parsable for TupleExpression {
    const RULE: Rule = Rule::tuple_expr;

    fn parse_inner(file_id: FileId, state: &mut State, pair: crate::Pair) -> Self {
        TupleExpression(ExprList::parse_ref(
            file_id,
            state,
            pair.into_inner().next().unwrap(),
        ))
    }
}

fn parse_call(
    file_id: crate::source::FileId,
    state: &mut crate::State,
    pair: crate::Pair,
) -> OracleExpression {
    let span = pair.as_span();
    let start = span.start() as u32;
    let mut fun_loc = SourceLocation::from_file_and_pair(file_id, &pair);
    let mut inner = pair.into_inner();

    let mut fun =
        OracleExpression::Identifier(Identifier::parse_ref(file_id, state, inner.next().unwrap()));

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
        fun = OracleExpression::Call(Ref::from_parsed(state, loc, call));
        fun_loc.end = end;
    }

    fun
}

fn parse_expression(
    file_id: crate::source::FileId,
    state: &mut crate::State,
    pair: crate::Pair,
) -> OracleExpression {
    match pair.as_rule() {
        Rule::atom => parse_expression(file_id, state, pair.into_inner().next().unwrap()),

        Rule::expr | Rule::l_and | Rule::compn | Rule::addtn | Rule::multn => {
            parse_leftassoc(file_id, state, pair)
        }

        Rule::unary => parse_unary(file_id, state, pair),
        Rule::call => parse_call(file_id, state, pair),

        Rule::invoke => {
            OracleExpression::Invoke(OracleInvocationExpression::parse_ref(file_id, state, pair))
        }
        Rule::table_expr => {
            OracleExpression::TableIndex(TableIndexExpression::parse_ref(file_id, state, pair))
        }
        Rule::sample => OracleExpression::Sample(
            SampleExpression::<PackageTypeIdentifierKind>::parse_ref(file_id, state, pair),
        ),
        Rule::paren_expr => {
            OracleExpression::Paren(ParenExpression::parse_ref(file_id, state, pair))
        }
        Rule::tuple_expr => {
            OracleExpression::Tuple(TupleExpression::parse_ref(file_id, state, pair))
        }

        Rule::string_literal => OracleExpression::String,
        Rule::int_literal => OracleExpression::Int,

        _ => todo!(),
    }
}

impl Parsable for OracleExpression {
    const RULE: Rule = Rule::expr;

    fn parse_inner(
        file_id: crate::source::FileId,
        state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        parse_expression(file_id, state, pair)
    }
}
