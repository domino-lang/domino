use crate::{
    arena::{Ref, Slice},
    ast_nodes::{
        identifier::{
            Identifier, OracleConstValueIdentifierKind, TypeArgumentIdentifier, TypeIdentifier,
        },
        list::{Comma, List},
        pure_expressions::PureExpression,
        PaddedRef, Parsable, Trivia,
    },
    source::{FileId, SourceLocation},
    Rule, State,
};

#[derive(Debug, Clone, Copy)]
pub enum Type {
    Identifier(Ref<TypeArgumentIdentifier>),
    Tuple(Ref<TupleType>),
    Argumented(Ref<ArgumentedType>),
}

#[derive(Debug, Clone, Copy)]
pub struct TupleType(pub Ref<TypeList>);

#[derive(Debug, Clone, Copy)]
pub struct ArgumentedType {
    pub name: Ref<TypeIdentifier>,
    pub post_name: Slice<Trivia>,
    pub args: Ref<TypeList>,
}

#[derive(Debug, Clone, Copy)]
pub enum TypeArgument {
    Identifier(Ref<TypeArgumentIdentifier>),
    Type(Ref<Type>),
    Expr(Ref<PureExpression<OracleConstValueIdentifierKind>>),
}

/// A list of types, usually comma separated. Usually surrounded by parenthises
pub type TypeArgList = List<TypeArgument, Comma>;

/// A list of types, usually comma separated. Usually surrounded by parenthises
pub type TypeList = List<Type, Comma>;

impl Parsable for Type {
    fn parse(file_id: FileId, state: &mut State, pair: crate::Pair) -> Self {
        let loc = SourceLocation::from_file_and_pair(file_id, &pair);
        debug_assert_eq!(pair.as_rule(), Rule::ty, "at {loc:?}");

        let pair = pair.into_inner().next().unwrap();
        match pair.as_rule() {
            Rule::identifier => Type::Identifier(Identifier::parse_ref(file_id, state, pair)),
            Rule::argd_ty => {
                let argd_ty = ArgumentedType::parse_ref(file_id, state, pair);
                Type::Argumented(argd_ty)
            }
            Rule::tuple_ty => Type::Tuple(TupleType::parse_ref(file_id, state, pair)),
            _ => unreachable!(),
        }
    }
}

impl Parsable for ArgumentedType {
    fn parse(file_id: FileId, state: &mut State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::argd_ty);

        let mut inner = pair.into_inner();
        let name = Identifier::parse_ref(file_id, state, inner.next().unwrap());
        let post_name = Slice::from_pair(file_id, state, inner.next().unwrap());
        let args = TypeList::parse_ref(file_id, state, inner.next().unwrap());

        ArgumentedType {
            name,
            post_name,
            args,
        }
    }
}

impl Parsable for TupleType {
    fn parse(file_id: FileId, state: &mut State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::tuple_ty);
        let pair = pair.into_inner().next().unwrap();
        TupleType(TypeList::parse_ref(file_id, state, pair))
    }
}

crate::ast_nodes::list::impl_comma_list!(Type, Rule::arg_list_ty, Rule::padded_ty);

super::impl_node_type!(0x10, Type, noop_index);
super::impl_node_type!(0x11, TupleType, noop_index);
super::impl_node_type!(0x12, ArgumentedType, noop_index);
super::impl_node_type!(0x13, TypeList, noop_index);
