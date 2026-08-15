use crate::{
    arena::Ref,
    ast_nodes::{
        expressions, game,
        identifier::{self, Identifier},
        list::{Comma, List},
        package, theorem, Trivia,
    },
};

pub trait TypeKind {
    type ExpressionKind: expressions::ExpressionKind<TypeKind = Self>;

    type TypeArgIdentifierKind: identifier::TypeArgIdentifierKind;
    type TypeIdentifierKind: identifier::TypeIdentifierKind;
}

#[derive(Debug, Clone, Copy)]
pub struct PackageTypeKind;

impl TypeKind for PackageTypeKind {
    type ExpressionKind = package::PurePackageExpressionKind;

    type TypeArgIdentifierKind = identifier::PackageTypeArgumentIdentifierKind;

    type TypeIdentifierKind = identifier::PackageTypeIdentifierKind;
}

#[derive(Debug, Clone, Copy)]
pub struct GameTypeKind;

impl TypeKind for GameTypeKind {
    type ExpressionKind = game::PureGameExpressionKind;

    type TypeArgIdentifierKind = identifier::GameTypeArgumentIdentifierKind;

    type TypeIdentifierKind = identifier::GameTypeIdentifierKind;
}

#[derive(Debug, Clone, Copy)]
pub struct TheoremTypeKind;

impl TypeKind for TheoremTypeKind {
    type ExpressionKind = theorem::PureTheoremExpressionKind;

    type TypeArgIdentifierKind = identifier::TheoremTypeArgumentIdentifierKind;

    type TypeIdentifierKind = identifier::TheoremTypeIdentifierKind;
}

#[derive(Debug, Clone, Copy)]
pub enum Type<TK: TypeKind> {
    Identifier(Ref<Identifier<TK::TypeIdentifierKind>>),
    Tuple(Ref<TupleType<TK>>),
    Argumented(Ref<ArgumentedType<TK>>),
    Fn(Ref<FnType<TK>>),
}

#[derive(Debug, Clone, Copy)]
pub struct TupleType<TK: TypeKind>(pub Ref<TypeList<TK>>);

#[derive(Debug, Clone, Copy)]
pub struct ArgumentedType<TK: TypeKind> {
    pub name: Ref<identifier::Identifier<TK::TypeIdentifierKind>>,
    pub post_name: Ref<Trivia>,
    pub args: Ref<TypeArgList<TK>>,
}

#[derive(Debug, Clone, Copy)]
pub enum TypeArgument<TK: TypeKind> {
    Identifier(Ref<Identifier<TK::TypeArgIdentifierKind>>),
    Tuple(Ref<TypeArgList<TK>>),
    Application(Ref<ArgumentedType<TK>>),
    Type(Ref<Type<TK>>),
    Expr(Ref<expressions::Expression<TK::ExpressionKind>>),
}

#[derive(Debug, Clone, Copy)]
pub struct FnType<TK: TypeKind> {
    pub args_trivia: Ref<Trivia>,
    pub args: Ref<TypeList<TK>>,
    pub arrow_trivia: Ref<Trivia>,
    pub ret_trivia: Ref<Trivia>,
    pub ret_ty: Ref<Type<TK>>,
}

/// A list of types, usually comma separated. Usually surrounded by parenthises
pub type TypeArgList<TK: TypeKind> = List<TypeArgument<TK>, Comma>;

/// A list of types, usually comma separated. Usually surrounded by parenthises
pub type TypeList<TK: TypeKind> = List<Type<TK>, Comma>;
//pub type TypeList<TK: TypeKind> = List<Type<TK>, Comma>;

// crate::ast_nodes::list::impl_list!(
//     TypeArgument<PackageTypeArgumentIdentifierKind>,
//     Rule::appl_ty_arg_list,
//     Rule::appl_ty_arg_padded,
//     crate::ast_nodes::list::Comma,
//     Rule::comma,
// );
//
// crate::ast_nodes::list::impl_list!(
//     TypeArgument<GameTypeArgumentIdentifierKind>,
//     Rule::appl_ty_arg_list,
//     Rule::appl_ty_arg_padded,
//     crate::ast_nodes::list::Comma,
//     Rule::comma,
// );
