use domino_ast::{
    ast_nodes::{expressions, identifier, types},
    Arenas,
};
use domino_collections::arena::Ref;

use crate::{diag, BuiltinType, BuiltinValue};

pub trait ValueResolution<EK: expressions::ExpressionKind> {
    fn kind(&self, arenas: &Arenas) -> ValueResolutionKind<EK>;
}

pub enum ValueResolutionKind<EK: expressions::ExpressionKind> {
    Declaration(Ref<types::Type<EK::TypeKind>>),
    Assignment(Ref<expressions::Expression<EK>>),
    Builtin(BuiltinValue),
    Error(Ref<diag::Diagnostic>),
}
pub enum ConstValueResolutionKind<EK: expressions::ExpressionKind> {
    Declaration(Ref<types::Type<EK::TypeKind>>),
    Assigrment(Ref<expressions::Expression<EK>>),
    Builtin(BuiltinValue),
    Error(Ref<diag::Diagnostic>),
}

pub trait TypeResolution<TK: types::TypeKind> {
    fn kind(&self, arenas: &Arenas) -> TypeResolutionKind<TK>;
}

pub enum TypeResolutionKind<TK: types::TypeKind> {
    /// the type param
    Declaration(Ref<identifier::Identifier<TK::TypeIdentifierKind>>),
    Builtin(BuiltinType),
    Error(Ref<diag::Diagnostic>),
}

pub trait TypeArgResolution<TK: types::TypeKind> {
    fn kind(&self, arenas: &Arenas) -> TypeArgResolutionKind<TK>;
}

pub enum TypeArgResolutionKind<TK: types::TypeKind> {
    /// the type param
    Type(TypeResolutionKind<TK>),
    Value(ValueResolutionKind<TK::ExpressionKind>),
    Error(Ref<diag::Diagnostic>),
}

pub trait HasValueResolution<EK: expressions::ExpressionKind> {
    type Resolution: ValueResolution<EK>;

    fn get(&self, id: Ref<identifier::Identifier<EK::ValueIdentifierKind>>) -> &Self::Resolution;
}

pub trait HasTypeResolution<TK: types::TypeKind> {
    type Resolution: TypeResolution<TK>;

    fn type_resolution(
        &self,
        id: Ref<identifier::Identifier<TK::TypeIdentifierKind>>,
    ) -> &Self::Resolution;
}

pub trait HasTypeArgResolution<TK: types::TypeKind> {
    type Resolution: TypeArgResolution<TK>;

    fn type_arg_resolution(
        &self,
        id: Ref<identifier::Identifier<TK::TypeArgIdentifierKind>>,
    ) -> &Self::Resolution;
}
