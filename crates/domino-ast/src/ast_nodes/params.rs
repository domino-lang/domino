use domino_collections::arena::Ref;

use crate::ast_nodes::{
    common::{TypeDeclList, ValueDeclList},
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
    pub decls: Ref<ValueDeclList<EK>>,
}
