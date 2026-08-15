use domino_ast::ast_nodes::{
    identifier::{Identifier, OracleIdentifierKind},
    oracles::*,
    statements::StatementList,
    types::Type,
    InArena, NodeType, Trivia,
};

use crate::{ast_nodes::expressions::impl_expr, ListItem, Parsable, Rule};

impl_expr!(OracleExpressionKind);

impl<OI: OracleIdentifierKind> ListItem for OracleSignature<OI> {
    const LIST_RULE: Rule = Rule::oracle_decl_list;
}

impl ListItem for OracleValueArgDecl {
    const LIST_RULE: Rule = Rule::expr_ident_decl_list;
}

impl<OI: OracleIdentifierKind> Parsable for OracleSignature<OI>
where
    Identifier<OI>: Parsable,
    Self: NodeType + InArena,
{
    const RULE: Rule = Rule::oracle_sig;

    fn parse_inner(
        file_id: domino_ast::source::FileId,
        state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        let mut inner = pair.into_inner();
        let name_pair = inner.next().unwrap();
        let trivia_pair = inner.next().unwrap();
        let args_pair = inner.next().unwrap();

        let name = Identifier::parse_ref(file_id, state, name_pair);
        let trivia = Trivia::parse_ref(file_id, state, trivia_pair);
        let args = OracleValueDeclList::parse_ref(file_id, state, args_pair);

        let ret_ty = inner.next().map(|pre_arrow_trivia_pair| {
            let post_arrow_trivia_pair = inner.next().unwrap();
            let ret_ty_pair = inner.next().unwrap();

            let pre_arrow_trivia = Trivia::parse_ref(file_id, state, pre_arrow_trivia_pair);
            let post_arrow_trivia = Trivia::parse_ref(file_id, state, post_arrow_trivia_pair);
            let ty = Type::parse_ref(file_id, state, ret_ty_pair);

            OracleReturnType {
                pre_arrow_trivia,
                post_arrow_trivia,
                ty,
            }
        });

        Self {
            name,
            trivia,
            args,
            ret_ty,
        }
    }
}

impl Parsable for OracleValueArgDecl {
    const RULE: Rule = Rule::expr_ident_decl;

    fn parse_inner(
        file_id: domino_ast::source::FileId,
        state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        let mut inner = pair.into_inner();
        let name_pair = inner.next().unwrap();
        let pre_colon_trivia_pair = inner.next().unwrap();
        let post_colon_trivia_pair = inner.next().unwrap();
        let ty_pair = inner.next().unwrap();

        let name = Identifier::parse_ref(file_id, state, name_pair);
        let pre_colon_trivia = Trivia::parse_ref(file_id, state, pre_colon_trivia_pair);
        let post_colon_trivia = Trivia::parse_ref(file_id, state, post_colon_trivia_pair);
        let ty = Type::parse_ref(file_id, state, ty_pair);

        Self {
            name,
            pre_colon_trivia,
            post_colon_trivia,
            ty,
        }
    }
}

impl Parsable for OracleDefinition {
    const RULE: Rule = Rule::oracle_def;

    fn parse_inner(
        file_id: domino_ast::source::FileId,
        state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        let mut inner = pair.into_inner();
        let _oracle_pair = inner.next().unwrap();
        let sig_trivia_pair = inner.next().unwrap();
        let oracle_sig_pair = inner.next().unwrap();
        let brace_trivia_pair = inner.next().unwrap();
        let statements_pair = inner.next().unwrap();

        let sig_trivia = Trivia::parse_ref(file_id, state, sig_trivia_pair);
        let oracle_sig = OracleSignature::parse_ref(file_id, state, oracle_sig_pair);
        let brace_trivia = Trivia::parse_ref(file_id, state, brace_trivia_pair);
        let statements = StatementList::parse_ref(file_id, state, statements_pair);

        Self {
            sig_trivia,
            oracle_sig,
            brace_trivia,
            statements,
        }
    }
}
