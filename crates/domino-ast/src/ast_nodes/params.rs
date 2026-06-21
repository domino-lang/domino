use crate::{
    arena::Ref,
    ast_nodes::{
        common::{ConstDeclList, TypeDeclList},
        identifier::{IdentifierKind, ValueIdentifierKind},
        Trivia,
    },
};

#[derive(Debug, Clone, Copy)]
pub struct TypeParamBlock<IK: IdentifierKind> {
    pub trivia: Ref<Trivia>,
    pub decls: Ref<TypeDeclList<IK>>,
}

#[derive(Debug, Clone, Copy)]
pub struct ConstParamBlock<IK: ValueIdentifierKind> {
    pub trivia: Ref<Trivia>,
    pub decls: Ref<ConstDeclList<IK>>,
}
