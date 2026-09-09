use domino_collections::arena::Ref;

use crate::ast_nodes::{
    common::{ConstDeclList, TypeDeclList},
    expressions,
    identifier::IdentifierKind,
    Trivia,
};

#[derive(Debug)]
pub struct TypeParamBlock<IK: IdentifierKind> {
    pub trivia: Ref<Trivia>,
    pub decls: Ref<TypeDeclList<IK>>,
}

#[derive(Debug)]
pub struct ConstParamBlock<EK: expressions::ExpressionKind> {
    pub trivia: Ref<Trivia>,
    pub decls: Ref<ConstDeclList<EK>>,
}
