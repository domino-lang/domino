use crate::{
    arena::Ref,
    ast_nodes::{
        identifier::{
            GameTypeArgumentIdentifierKind, GameTypeIdentifierKind, Identifier,
            PackageTypeArgumentIdentifier, PackageTypeArgumentIdentifierKind,
            PackageTypeIdentifierKind, TheoremTypeArgumentIdentifierKind,
            TheoremTypeIdentifierKind, TypeArgIdentifierKind, TypeIdentifierKind,
        },
        list::{Comma, List},
        pure_expressions::PureExpression,
        InArena, Indexable, ListItem, NodeType, Parsable, Trivia,
    },
    source::FileId,
    Rule, State,
};

#[derive(Debug, Clone, Copy)]
pub enum Type<IK: TypeIdentifierKind> {
    Identifier(Ref<PackageTypeArgumentIdentifier>),
    Tuple(Ref<TupleType<IK>>),
    Argumented(Ref<ArgumentedType<IK::ArgIdentifierKind>>),
    Fn(Ref<FnType<IK>>),
}

impl<IK: TypeIdentifierKind> ListItem for Type<IK> {
    const LIST_RULE: Rule = Rule::ty_list;
}

#[derive(Debug, Clone, Copy)]
pub struct TupleType<IK: TypeIdentifierKind>(pub Ref<TypeList<IK>>);

#[derive(Debug, Clone, Copy)]
pub struct ArgumentedType<IK: TypeArgIdentifierKind> {
    pub name: Ref<Identifier<IK::ArgTypeIdentifierKind>>,
    pub post_name: Ref<Trivia>,
    pub args: Ref<TypeArgList<IK>>,
}

#[derive(Debug, Clone, Copy)]
pub enum TypeArgument<IK: TypeArgIdentifierKind> {
    Identifier(Ref<PackageTypeArgumentIdentifier>),
    Tuple(Ref<TypeArgList<IK>>),
    Application(Ref<ArgumentedType<IK>>),
    Type(Ref<Type<IK::ArgTypeIdentifierKind>>),
    Expr(Ref<PureExpression<IK::ArgValueIdentifierKind>>),
}

#[derive(Debug, Clone, Copy)]
pub struct FnType<IK: TypeIdentifierKind> {
    pub args_trivia: Ref<Trivia>,
    pub args: Ref<TypeList<IK>>,
    pub arrow_trivia: Ref<Trivia>,
    pub ret_trivia: Ref<Trivia>,
    pub ret_ty: Ref<Type<IK>>,
}

impl<IK: TypeArgIdentifierKind> ListItem for TypeArgument<IK> {
    const LIST_RULE: Rule = Rule::appl_ty_arg_list;
}

/// A list of types, usually comma separated. Usually surrounded by parenthises
pub type TypeArgList<IK: TypeArgIdentifierKind> = List<TypeArgument<IK>, Comma>;

/// A list of types, usually comma separated. Usually surrounded by parenthises
pub type TypeList<IK: TypeIdentifierKind> = List<Type<IK>, Comma>;
//pub type TypeList<IK: TypeIdentifierKind> = List<Type<IK>, Comma>;

fn parse_type<IK: TypeIdentifierKind>(
    file_id: FileId,
    state: &mut State,
    pair: crate::Pair,
) -> Type<IK>
where
    Type<IK>: Indexable + InArena,
    ArgumentedType<IK::ArgIdentifierKind>: Parsable,
    TupleType<IK>: Parsable,
    FnType<IK>: Parsable,
    TypeArgList<IK::ArgIdentifierKind>: Parsable,
{
    let inner = pair.into_inner().next().unwrap();
    match inner.as_rule() {
        Rule::identifier => Type::Identifier(Identifier::parse_ref(file_id, state, inner)),
        Rule::appl_ty => {
            let argd_ty = ArgumentedType::parse_ref(file_id, state, inner);
            Type::Argumented(argd_ty)
        }
        Rule::tuple_ty => Type::Tuple(TupleType::parse_ref(file_id, state, inner)),
        Rule::fn_ty => Type::Fn(FnType::parse_ref(file_id, state, inner)),
        _ => unreachable!(),
    }
}

impl Parsable for Type<PackageTypeIdentifierKind> {
    const RULE: Rule = Rule::ty;

    fn parse_inner(file_id: FileId, state: &mut State, pair: crate::Pair) -> Self {
        parse_type::<PackageTypeIdentifierKind>(file_id, state, pair)
    }
}

impl Parsable for Type<GameTypeIdentifierKind> {
    const RULE: Rule = Rule::ty;

    fn parse_inner(file_id: FileId, state: &mut State, pair: crate::Pair) -> Self {
        parse_type::<GameTypeIdentifierKind>(file_id, state, pair)
    }
}

impl Parsable for Type<TheoremTypeIdentifierKind> {
    const RULE: Rule = Rule::ty;

    fn parse_inner(file_id: FileId, state: &mut State, pair: crate::Pair) -> Self {
        parse_type::<TheoremTypeIdentifierKind>(file_id, state, pair)
    }
}

impl Parsable for TypeArgument<PackageTypeArgumentIdentifierKind> {
    const RULE: Rule = Rule::appl_ty_arg;

    fn parse_inner(file_id: FileId, state: &mut State, pair: crate::Pair) -> Self {
        parse_type_arg(file_id, state, pair)
    }
}

impl Parsable for TypeArgument<GameTypeArgumentIdentifierKind> {
    const RULE: Rule = Rule::appl_ty_arg;

    fn parse_inner(file_id: FileId, state: &mut State, pair: crate::Pair) -> Self {
        parse_type_arg(file_id, state, pair)
    }
}

impl Parsable for TypeArgument<TheoremTypeArgumentIdentifierKind> {
    const RULE: Rule = Rule::appl_ty_arg;

    fn parse_inner(file_id: FileId, state: &mut State, pair: crate::Pair) -> Self {
        parse_type_arg(file_id, state, pair)
    }
}

fn parse_type_arg<IK: TypeArgIdentifierKind>(
    file_id: FileId,
    state: &mut State,
    pair: crate::Pair,
) -> TypeArgument<IK>
where
    TypeArgument<IK>: Indexable + InArena + NodeType,
    ArgumentedType<IK>: Parsable,
    TypeArgList<IK>: Parsable,
    Type<IK::ArgTypeIdentifierKind>: Parsable,
    PureExpression<IK::ArgValueIdentifierKind>: Parsable,
{
    let inner = pair.into_inner().next().unwrap();
    match inner.as_rule() {
        Rule::appl_ty => {
            TypeArgument::Application(ArgumentedType::parse_ref(file_id, state, inner))
        }
        Rule::tuple_appl_ty_arg => TypeArgument::Tuple(TypeArgList::parse_ref(
            file_id,
            state,
            inner.into_inner().next().unwrap(),
        )),
        Rule::identifier => TypeArgument::Identifier(Identifier::parse_ref(file_id, state, inner)),
        Rule::ty => TypeArgument::Type(Type::parse_ref(file_id, state, inner)),
        Rule::expr => TypeArgument::Expr(PureExpression::parse_ref(file_id, state, inner)),
        _ => unreachable!(),
    }
}

impl<IK: TypeArgIdentifierKind> Parsable for ArgumentedType<IK>
where
    Self: Indexable + InArena + NodeType,
    TypeArgList<IK>: Parsable,
    Identifier<IK::ArgTypeIdentifierKind>: Parsable,
{
    const RULE: Rule = Rule::appl_ty;

    fn parse_inner(file_id: FileId, state: &mut State, pair: crate::Pair) -> Self {
        let mut inner = pair.into_inner();
        let name = Identifier::parse_ref(file_id, state, inner.next().unwrap());
        let post_name = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let args = TypeArgList::parse_ref(file_id, state, inner.next().unwrap());

        ArgumentedType {
            name,
            post_name,
            args,
        }
    }
}

impl<IK: TypeIdentifierKind> Parsable for FnType<IK>
where
    Self: Indexable + InArena + NodeType,
    TypeList<IK>: Parsable,
    Type<IK>: Parsable,
{
    const RULE: Rule = Rule::fn_ty;

    fn parse_inner(file_id: FileId, state: &mut State, pair: crate::Pair) -> Self {
        let mut inner = pair.into_inner();
        let _fn_kw = inner.next().unwrap();
        let args_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let args = TypeList::parse_ref(file_id, state, inner.next().unwrap());
        let arrow_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let ret_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let ret_ty = Type::parse_ref(file_id, state, inner.next().unwrap());

        Self {
            args_trivia,
            args,
            arrow_trivia,
            ret_trivia,
            ret_ty,
        }
    }
}

impl<IK: TypeIdentifierKind> Parsable for TupleType<IK>
where
    Self: Indexable + InArena + NodeType,
    TypeList<IK>: Parsable,
{
    const RULE: Rule = Rule::tuple_ty;

    fn parse_inner(file_id: FileId, state: &mut State, pair: crate::Pair) -> Self {
        let pair = pair.into_inner().next().unwrap();
        TupleType(TypeList::parse_ref(file_id, state, pair))
    }
}

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

#[cfg(debug_assertions)]
#[allow(dead_code)]
mod static_checks {
    use super::*;
    use crate::ast_nodes::Parsable;

    fn impls_parsable<T: Parsable>() {}

    fn check_impls_parsable() {
        impls_parsable::<Type<PackageTypeIdentifierKind>>();
        impls_parsable::<List<Type<PackageTypeIdentifierKind>, Comma>>();
        impls_parsable::<TypeArgList<PackageTypeArgumentIdentifierKind>>();
        impls_parsable::<List<TypeArgument<PackageTypeArgumentIdentifierKind>, Comma>>();
        impls_parsable::<TypeArgument<PackageTypeArgumentIdentifierKind>>();

        impls_parsable::<TupleType<PackageTypeIdentifierKind>>();
    }
}
