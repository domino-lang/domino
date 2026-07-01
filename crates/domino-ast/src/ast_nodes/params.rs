use crate::{
    arena::Ref,
    ast_nodes::{
        common::{ConstDeclList, TypeDeclList},
        expressions,
        identifier::IdentifierKind,
        Trivia,
    },
};

#[derive(Debug, Clone, Copy)]
pub struct TypeParamBlock<IK: IdentifierKind> {
    pub trivia: Ref<Trivia>,
    pub decls: Ref<TypeDeclList<IK>>,
}

#[derive(Debug, Clone, Copy)]
pub struct ConstParamBlock<EK: expressions::ExpressionKind> {
    pub trivia: Ref<Trivia>,
    pub decls: Ref<ConstDeclList<EK>>,
}
