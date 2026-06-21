use crate::{
    arena::Ref,
    ast_nodes::{
        identifier::{Identifier, TypeIdentifierKind, ValueIdentifierKind},
        list::{Comma, List},
        types::Type,
        InArena, Indexable, ListItem, NodeType, Parsable, Trivia,
    },
    Rule,
};

#[derive(Debug)]
// identifier ~ gap ~ ":" ~ gap ~ ty
pub struct ValueDecl<IK: ValueIdentifierKind> {
    pub name: Ref<Identifier<IK>>,
    pub colon_trivia: Ref<Trivia>,
    pub ty_trivia: Ref<Trivia>,
    pub ty: Ref<Type<IK::TypeIdentifierKind>>,
}

impl<IK: ValueIdentifierKind> ListItem for ValueDecl<IK> {
    const LIST_RULE: Rule = Rule::expr_ident_decl_list;
}

pub type TypeDeclList<IK: TypeIdentifierKind> = List<Identifier<IK>, Comma>;
pub type ConstDeclList<IK: ValueIdentifierKind> = List<ValueDecl<IK>, Comma>;

pub fn parse_value_decl<IK>(
    file_id: crate::source::FileId,
    state: &mut crate::State,
    pair: crate::Pair,
) -> ValueDecl<IK>
where
    IK: ValueIdentifierKind,
    Identifier<IK>: Parsable,
    Type<IK::TypeIdentifierKind>: Parsable,
    ValueDecl<IK>: Indexable + InArena + NodeType,
{
    debug_assert_eq!(pair.as_rule(), Rule::expr_ident_decl);

    let mut inner = pair.into_inner();

    ValueDecl {
        name: Identifier::<IK>::parse_ref(file_id, state, inner.next().unwrap()),
        colon_trivia: Trivia::parse_ref(file_id, state, inner.next().unwrap()),
        ty_trivia: Trivia::parse_ref(file_id, state, inner.next().unwrap()),
        ty: Type::parse_ref(file_id, state, inner.next().unwrap()),
    }
}
