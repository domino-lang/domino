use domino_ast::ast_nodes::{
    identifier::OracleValueIdentifier, list::Semicolon, oracles::OracleExpression, statements::*,
    Trivia,
};

use crate::{ListItem, Parsable, Rule};

impl ListItem for Statement {
    const LIST_RULE: Rule = Rule::statements;
}

impl ListItem for Pattern {
    const LIST_RULE: Rule = Rule::patterns;
}

impl Parsable for Pattern {
    const RULE: Rule = Rule::pattern;

    fn parse_inner(
        file_id: domino_ast::source::FileId,
        state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
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
    const RULE: Rule = Rule::table_pat;

    fn parse_inner(
        file_id: domino_ast::source::FileId,
        state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        let mut inner = pair.into_inner();
        let ident_pair = inner.next().unwrap();
        let trivia_pair = inner.next().unwrap();
        let index_trivia_pair = inner.next().unwrap();
        let index_pair = inner.next().unwrap();
        let index_trailing_trivia_pair = inner.next().unwrap();

        Self {
            table_name: OracleValueIdentifier::parse_ref(file_id, state, ident_pair),
            table_name_trivia: Trivia::parse_ref(file_id, state, trivia_pair),
            index_trivia: Trivia::parse_ref(file_id, state, index_trivia_pair),
            index: OracleExpression::parse_ref(file_id, state, index_pair),
            index_trailing_trivia: Trivia::parse_ref(file_id, state, index_trailing_trivia_pair),
        }
    }
}

impl Parsable for TuplePattern {
    const RULE: Rule = Rule::tuple_pat;

    fn parse_inner(
        file_id: domino_ast::source::FileId,
        state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        let items_pair = pair.into_inner().next().unwrap();

        Self {
            items: PatternList::parse_ref(file_id, state, items_pair),
        }
    }
}

impl Parsable for Statement {
    const RULE: Rule = Rule::statement;

    fn parse_inner(
        file_id: domino_ast::source::FileId,
        state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        let pair = pair.into_inner().next().unwrap();

        match pair.as_rule() {
            Rule::ifthenelse => {
                Self::IfThenElse(IfThenElseStatement::parse_ref(file_id, state, pair))
            }
            Rule::abort => Self::Abort,
            Rule::assert => Self::Assert(AssertStatement::parse_ref(file_id, state, pair)),
            Rule::assignment => Self::Assign(AssignStatement::parse_ref(file_id, state, pair)),
            Rule::r#return => Self::Return(ReturnStatement::parse_ref(file_id, state, pair)),
            Rule::expr_stmt => {
                Self::Expression(ExpressionStatement::parse_ref(file_id, state, pair))
            }
            _ => unreachable!(),
        }
    }
}

impl Parsable for AssertStatement {
    const RULE: Rule = Rule::assert;

    fn parse_inner(
        file_id: domino_ast::source::FileId,
        state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        let mut inner = pair.into_inner();
        let _kw_assert = inner.next().unwrap();
        let expr_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let expr = OracleExpression::parse_ref(file_id, state, inner.next().unwrap());
        let semicolon_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let _semicolon = Semicolon::parse(file_id, state, inner.next().unwrap());

        Self {
            expr_trivia,
            expr,
            semicolon_trivia,
        }
    }
}

impl Parsable for AssignStatement {
    const RULE: Rule = Rule::assignment;

    fn parse_inner(
        file_id: domino_ast::source::FileId,
        state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        let mut inner = pair.into_inner();
        let pat = Pattern::parse_ref(file_id, state, inner.next().unwrap());
        let pre_arrow_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let post_arrow_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let expr = OracleExpression::parse_ref(file_id, state, inner.next().unwrap());
        let semicolon_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let _semicolon = Semicolon::parse(file_id, state, inner.next().unwrap());

        Self {
            pat,
            pre_arrow_trivia,
            post_arrow_trivia,
            expr,
            semicolon_trivia,
        }
    }
}

impl Parsable for ExpressionStatement {
    const RULE: Rule = Rule::expr_stmt;

    fn parse_inner(
        file_id: domino_ast::source::FileId,
        state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        let mut inner = pair.into_inner();

        let expr = OracleExpression::parse_ref(file_id, state, inner.next().unwrap());
        let semicolon_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let _semicolon = Semicolon::parse(file_id, state, inner.next().unwrap());

        Self {
            expr,
            semicolon_trivia,
        }
    }
}

impl Parsable for ReturnStatement {
    const RULE: Rule = Rule::r#return;

    fn parse_inner(
        file_id: domino_ast::source::FileId,
        state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        let mut inner = pair.into_inner();
        let _return_pair = inner.next().unwrap();
        let trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let expr = OracleExpression::parse_ref(file_id, state, inner.next().unwrap());
        let semicolon_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let _semicolon = Semicolon::parse(file_id, state, inner.next().unwrap());

        Self {
            trivia,
            expr,
            semicolon_trivia,
        }
    }
}

impl Parsable for IfThenElseStatement {
    const RULE: Rule = Rule::ifthenelse;

    fn parse_inner(
        file_id: domino_ast::source::FileId,
        state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        let mut inner = pair.into_inner();
        let _if_pair = inner.next().unwrap();
        let cond_trivia_pair = inner.next().unwrap();
        let cond_pair = inner.next().unwrap();
        let cond_brace_trivia_pair = inner.next().unwrap();
        let then_block_pair = inner.next().unwrap();

        let cond_trivia = Trivia::parse_ref(file_id, state, cond_trivia_pair);
        let cond = OracleExpression::parse_ref(file_id, state, cond_pair);
        let cond_brace_trivia = Trivia::parse_ref(file_id, state, cond_brace_trivia_pair);
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
            cond_trivia,
            cond,
            cond_brace_trivia,
            then_block,
            else_block,
        }
    }
}
