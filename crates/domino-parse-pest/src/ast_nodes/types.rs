use domino_ast::{
    ast_nodes::{
        expressions,
        identifier::{self, Identifier},
        list::{Comma, List},
        types::*,
        InArena, NodeType, Trivia,
    },
    source::FileId,
    State,
};

use crate::{ListItem, Parsable, Rule};

impl<TK: TypeKind> ListItem for Type<TK> {
    const LIST_RULE: Rule = Rule::ty_list;
}

impl<TK: TypeKind> ListItem for TypeArgument<TK> {
    const LIST_RULE: Rule = Rule::appl_ty_arg_list;
}

fn parse_type<TK: TypeKind>(file_id: FileId, state: &mut State, pair: crate::Pair) -> Type<TK>
where
    Type<TK>: InArena,
    ArgumentedType<TK>: Parsable,
    TupleType<TK>: Parsable,
    FnType<TK>: Parsable,
    TypeArgList<TK>: Parsable,
    Identifier<TK::TypeIdentifierKind>: Parsable,
{
    let inner = pair.into_inner().next().unwrap();
    match inner.as_rule() {
        Rule::identifier => {
            Type::Identifier(identifier::Identifier::parse_ref(file_id, state, inner))
        }
        Rule::appl_ty => {
            let argd_ty = ArgumentedType::parse_ref(file_id, state, inner);
            Type::Argumented(argd_ty)
        }
        Rule::tuple_ty => Type::Tuple(TupleType::parse_ref(file_id, state, inner)),
        Rule::fn_ty => Type::Fn(FnType::parse_ref(file_id, state, inner)),
        _ => unreachable!(),
    }
}

impl Parsable for Type<PackageTypeKind> {
    const RULE: Rule = Rule::ty;

    fn parse_inner(file_id: FileId, state: &mut State, pair: crate::Pair) -> Self {
        parse_type::<PackageTypeKind>(file_id, state, pair)
    }
}

impl Parsable for Type<GameTypeKind> {
    const RULE: Rule = Rule::ty;

    fn parse_inner(file_id: FileId, state: &mut State, pair: crate::Pair) -> Self {
        parse_type::<GameTypeKind>(file_id, state, pair)
    }
}

impl Parsable for Type<TheoremTypeKind> {
    const RULE: Rule = Rule::ty;

    fn parse_inner(file_id: FileId, state: &mut State, pair: crate::Pair) -> Self {
        parse_type::<TheoremTypeKind>(file_id, state, pair)
    }
}

impl Parsable for TypeArgument<PackageTypeKind> {
    const RULE: Rule = Rule::appl_ty_arg;

    fn parse_inner(file_id: FileId, state: &mut State, pair: crate::Pair) -> Self {
        parse_type_arg(file_id, state, pair)
    }
}

impl Parsable for TypeArgument<GameTypeKind> {
    const RULE: Rule = Rule::appl_ty_arg;

    fn parse_inner(file_id: FileId, state: &mut State, pair: crate::Pair) -> Self {
        parse_type_arg(file_id, state, pair)
    }
}

impl Parsable for TypeArgument<TheoremTypeKind> {
    const RULE: Rule = Rule::appl_ty_arg;

    fn parse_inner(file_id: FileId, state: &mut State, pair: crate::Pair) -> Self {
        parse_type_arg(file_id, state, pair)
    }
}

fn parse_type_arg<TK: TypeKind>(
    file_id: FileId,
    state: &mut State,
    pair: crate::Pair,
) -> TypeArgument<TK>
where
    TypeArgument<TK>: InArena + NodeType,
    ArgumentedType<TK>: Parsable,
    TypeArgList<TK>: Parsable,
    Type<TK>: Parsable,
    expressions::Expression<TK::ExpressionKind>: Parsable,
    Identifier<TK::TypeArgIdentifierKind>: Parsable,
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
        Rule::identifier => {
            let ident = identifier::Identifier::<TK::TypeArgIdentifierKind>::parse_ref(
                file_id, state, inner,
            );
            TypeArgument::Identifier(ident)
        }
        Rule::ty => TypeArgument::Type(Type::parse_ref(file_id, state, inner)),
        Rule::expr => TypeArgument::Expr(expressions::Expression::parse_ref(file_id, state, inner)),
        _ => unreachable!(),
    }
}

impl<TK: TypeKind> Parsable for ArgumentedType<TK>
where
    Self: InArena + NodeType,
    TypeArgList<TK>: Parsable,
    identifier::Identifier<TK::TypeIdentifierKind>: Parsable,
    identifier::Identifier<TK::TypeArgIdentifierKind>: Parsable,
{
    const RULE: Rule = Rule::appl_ty;

    fn parse_inner(file_id: FileId, state: &mut State, pair: crate::Pair) -> Self {
        let mut inner = pair.into_inner();
        let name = identifier::Identifier::<TK::TypeIdentifierKind>::parse_ref(
            file_id,
            state,
            inner.next().unwrap(),
        );
        let post_name = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let args = TypeArgList::parse_ref(file_id, state, inner.next().unwrap());

        ArgumentedType {
            name,
            post_name,
            args,
        }
    }
}

impl<TK: TypeKind> Parsable for FnType<TK>
where
    Self: InArena + NodeType,
    TypeList<TK>: Parsable,
    Type<TK>: Parsable,
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

impl<TK: TypeKind> Parsable for TupleType<TK>
where
    Self: InArena + NodeType,
    TypeList<TK>: Parsable,
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
    use crate::Parsable;

    fn impls_parsable<T: Parsable>() {}

    fn check_impls_parsable() {
        impls_parsable::<Type<PackageTypeKind>>();
        impls_parsable::<List<Type<PackageTypeKind>, Comma>>();
        impls_parsable::<TypeArgList<PackageTypeKind>>();
        impls_parsable::<List<TypeArgument<PackageTypeKind>, Comma>>();
        impls_parsable::<TypeArgument<PackageTypeKind>>();

        impls_parsable::<TupleType<PackageTypeKind>>();
    }
}
