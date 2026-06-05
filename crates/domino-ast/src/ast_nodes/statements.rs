use crate::{
    arena::Ref,
    ast_nodes::{
        identifier::OracleValueIdentifier,
        list::{impl_list, Comma, List, Semicolon},
        oracle_expressions::OracleExpression,
        PaddedRef, Parsable, Trivia,
    },
    Rule,
};

#[derive(Debug, Clone, Copy)]
pub enum Statement {
    Abort,
    Assign(Ref<AssignStatement>),
    Expression(Ref<ExpressionStatement>),
    IfThenElse(Ref<IfThenElseStatement>),
    Return(Ref<ReturnStatement>),
}

#[derive(Debug, Clone, Copy)]
pub struct AssignStatement {
    pub pat: Ref<Pattern>,
    pub pre_arrow_trivia: Ref<Trivia>,
    pub post_arrow_trivia: Ref<Trivia>,
    pub expr: Ref<OracleExpression>,
}

#[derive(Debug, Clone, Copy)]
pub struct IfThenElseStatement {
    pub cond: PaddedRef<OracleExpression>,
    pub then_block: Ref<StatementList>,
    pub else_block: Option<ElseBlock>,
}

#[derive(Debug, Clone, Copy)]
pub struct ElseBlock {
    pub pre_else_trivia: Ref<Trivia>,
    pub post_else_trivia: Ref<Trivia>,
    pub block: Ref<StatementList>,
}

#[derive(Debug, Clone, Copy)]
pub struct ReturnStatement {
    pub trivia: Ref<Trivia>,
    pub expr: Ref<OracleExpression>,
}

#[derive(Debug, Clone, Copy)]
pub struct ExpressionStatement {
    pub expr: Ref<OracleExpression>,
}

#[derive(Debug, Clone, Copy)]
pub enum Pattern {
    Identifier(Ref<OracleValueIdentifier>),
    Table(Ref<TablePattern>),
    Tuple(Ref<TuplePattern>),
}

/// Assignment to a table. The table must already be in scope. Since we require the identifier to
/// be bound, we can use Identifier<OracleExpression> instead of Identifier<AssignedIdentifier>.
#[derive(Debug, Clone, Copy)]
pub struct TablePattern {
    pub table_name: Ref<OracleValueIdentifier>,
    pub table_name_trivia: Ref<Trivia>,
    pub index: PaddedRef<OracleExpression>,
}

#[derive(Debug, Clone, Copy)]
pub struct TuplePattern {
    pub items: Ref<PatternList>,
}

pub type PatternList = List<Pattern, Comma>;

pub type StatementList = List<Statement, Semicolon>;

impl Parsable for Pattern {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::pattern);
        let pair = pair.into_inner().next().unwrap();
        match pair.as_rule() {
            Rule::table_pat => Self::Table(TablePattern::parse_ref(file_id, state, pair)),
            Rule::tuple_pat => Self::Tuple(TuplePattern::parse_ref(file_id, state, pair)),
            Rule::identifier => {
                Self::Identifier(OracleValueIdentifier::parse_ref(file_id, state, pair))
            }
            _ => unreachable!(),
        }
    }
}

impl Parsable for TablePattern {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::table_pat);

        let mut inner = pair.into_inner();
        let ident_pair = inner.next().unwrap();
        let trivia_pair = inner.next().unwrap();
        let index_pair = inner.next().unwrap();

        Self {
            table_name: OracleValueIdentifier::parse_ref(file_id, state, ident_pair),
            table_name_trivia: Trivia::parse_ref(file_id, state, trivia_pair),
            index: PaddedRef::parse(file_id, state, index_pair),
        }
    }
}

impl Parsable for TuplePattern {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::tuple_pat);

        let items_pair = pair.into_inner().next().unwrap();

        Self {
            items: PatternList::parse_ref(file_id, state, items_pair),
        }
    }
}

impl Parsable for Statement {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::statement);

        let pair = pair.into_inner().next().unwrap();

        match pair.as_rule() {
            Rule::ifthenelse => {
                Self::IfThenElse(IfThenElseStatement::parse_ref(file_id, state, pair))
            }
            Rule::abort => Self::Abort,
            Rule::assignment => Self::Assign(AssignStatement::parse_ref(file_id, state, pair)),
            Rule::r#return => Self::Return(ReturnStatement::parse_ref(file_id, state, pair)),
            Rule::expr => Self::Expression(ExpressionStatement::parse_ref(file_id, state, pair)),
            _ => unreachable!(),
        }
    }
}

impl Parsable for AssignStatement {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::assignment);

        let mut inner = pair.into_inner();
        let pattern_pair = inner.next().unwrap();
        let pre_arrow_trivia_pair = inner.next().unwrap();
        let post_arrow_trivia_pair = inner.next().unwrap();
        let expr_pair = inner.next().unwrap();

        Self {
            pat: Pattern::parse_ref(file_id, state, pattern_pair),
            pre_arrow_trivia: Trivia::parse_ref(file_id, state, pre_arrow_trivia_pair),
            post_arrow_trivia: Trivia::parse_ref(file_id, state, post_arrow_trivia_pair),
            expr: OracleExpression::parse_ref(file_id, state, expr_pair),
        }
    }
}

impl Parsable for ExpressionStatement {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::expr);

        Self {
            expr: OracleExpression::parse_ref(file_id, state, pair),
        }
    }
}

impl Parsable for ReturnStatement {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::r#return);

        let mut inner = pair.into_inner();
        let _return_pair = inner.next().unwrap();
        let trivia_pair = inner.next().unwrap();
        let expr_pair = inner.next().unwrap();

        Self {
            trivia: Trivia::parse_ref(file_id, state, trivia_pair),
            expr: OracleExpression::parse_ref(file_id, state, expr_pair),
        }
    }
}

impl Parsable for IfThenElseStatement {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::ifthenelse);

        let mut inner = pair.into_inner();
        let _if_pair = inner.next().unwrap();
        let cond_pair = inner.next().unwrap();
        let then_block_pair = inner.next().unwrap();

        let cond = PaddedRef::parse(file_id, state, cond_pair);
        let then_block = StatementList::parse_ref(file_id, state, then_block_pair);
        let else_block = inner.peek().is_some().then(|| {
            let pre_else_trivia_pair = inner.next().unwrap();
            let _else_pair = inner.next().unwrap();
            let post_else_trivia_pair = inner.next().unwrap();
            let else_block_pair = inner.next().unwrap();

            ElseBlock {
                pre_else_trivia: Trivia::parse_ref(file_id, state, pre_else_trivia_pair),
                post_else_trivia: Trivia::parse_ref(file_id, state, post_else_trivia_pair),
                block: StatementList::parse_ref(file_id, state, else_block_pair),
            }
        });

        Self {
            cond,
            then_block,
            else_block,
        }
    }
}

impl_list!(
    Pattern,
    Rule::patterns,
    Rule::padded_pattern,
    crate::ast_nodes::list::Comma,
    Rule::comma,
);
crate::ast_nodes::list::impl_list!(
    Statement,
    Rule::statements,
    Rule::padded_statement,
    Semicolon,
    Rule::semicolon
);
