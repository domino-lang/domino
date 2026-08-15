use domino_ast::ast_nodes::{
    common::{self, ValueDecl},
    expressions::{self, ExpressionKind},
    identifier, types, InArena, NodeType, Trivia,
};

use crate::{ListItem, Parsable, Rule};

pub fn parse_value_decl<EK>(
    file_id: domino_ast::source::FileId,
    state: &mut crate::State,
    pair: crate::Pair,
) -> common::ValueDecl<EK>
where
    EK: expressions::ExpressionKind,
    identifier::Identifier<EK::ValueIdentifierKind>: Parsable,
    types::Type<EK::TypeKind>: Parsable,
    common::ValueDecl<EK>: InArena + NodeType,
{
    let mut inner = pair.into_inner();

    common::ValueDecl {
        name: identifier::Identifier::<EK::ValueIdentifierKind>::parse_ref(
            file_id,
            state,
            inner.next().unwrap(),
        ),
        colon_trivia: Trivia::parse_ref(file_id, state, inner.next().unwrap()),
        ty_trivia: Trivia::parse_ref(file_id, state, inner.next().unwrap()),
        ty: types::Type::parse_ref(file_id, state, inner.next().unwrap()),
    }
}

impl<EK: ExpressionKind> ListItem for ValueDecl<EK> {
    const LIST_RULE: Rule = Rule::expr_ident_decl_list;
}
