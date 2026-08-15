use crate::{
    arena::Ref,
    ast_nodes::{
        expressions::ExpressionKind,
        identifier::{Identifier, TypeIdentifierKind},
        list::{Comma, List},
        types::Type,
        Trivia,
    },
};

#[derive(Debug, Copy, Clone)]
// identifier ~ gap ~ ":" ~ gap ~ ty
pub struct ValueDecl<EK: ExpressionKind> {
    pub name: Ref<Identifier<EK::ValueIdentifierKind>>,
    pub colon_trivia: Ref<Trivia>,
    pub ty_trivia: Ref<Trivia>,
    pub ty: Ref<Type<EK::TypeKind>>,
}

pub type TypeDeclList<IK: TypeIdentifierKind> = List<Identifier<IK>, Comma>;
pub type ConstDeclList<EK: ExpressionKind> = List<ValueDecl<EK>, Comma>;
