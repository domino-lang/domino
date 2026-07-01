use crate::{
    arena::Ref,
    ast_nodes::{
        expressions::ExpressionKind,
        identifier::{Identifier, TypeIdentifierKind},
        list::{Comma, List},
        types::Type,
        InArena, Indexable, ListItem, NodeType, Parsable, Trivia,
    },
    Rule,
};

#[derive(Debug, Copy, Clone)]
// identifier ~ gap ~ ":" ~ gap ~ ty
pub struct ValueDecl<EK: ExpressionKind> {
    pub name: Ref<Identifier<EK::ValueIdentifierKind>>,
    pub colon_trivia: Ref<Trivia>,
    pub ty_trivia: Ref<Trivia>,
    pub ty: Ref<Type<EK::TypeKind>>,
}

impl<EK: ExpressionKind> ListItem for ValueDecl<EK> {
    const LIST_RULE: Rule = Rule::expr_ident_decl_list;
}

pub type TypeDeclList<IK: TypeIdentifierKind> = List<Identifier<IK>, Comma>;
pub type ConstDeclList<EK: ExpressionKind> = List<ValueDecl<EK>, Comma>;

pub fn parse_value_decl<EK>(
    file_id: crate::source::FileId,
    state: &mut crate::State,
    pair: crate::Pair,
) -> ValueDecl<EK>
where
    EK: ExpressionKind,
    Identifier<EK::ValueIdentifierKind>: Parsable,
    Type<EK::TypeKind>: Parsable,
    ValueDecl<EK>: Indexable + InArena + NodeType,
{
    let mut inner = pair.into_inner();

    ValueDecl {
        name: Identifier::<EK::ValueIdentifierKind>::parse_ref(
            file_id,
            state,
            inner.next().unwrap(),
        ),
        colon_trivia: Trivia::parse_ref(file_id, state, inner.next().unwrap()),
        ty_trivia: Trivia::parse_ref(file_id, state, inner.next().unwrap()),
        ty: Type::parse_ref(file_id, state, inner.next().unwrap()),
    }
}
