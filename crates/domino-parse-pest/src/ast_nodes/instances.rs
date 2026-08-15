use domino_ast::{
    ast_nodes::{
        expressions::{Expression, ExpressionKind},
        identifier::{Identifier, TypeIdentifierKind, ValueIdentifierKind},
        instances::*,
        list::Colon,
        types::{Type, TypeKind},
        InArena, NodeType, Trivia,
    },
    source::FileId,
    State,
};

use crate::{Pair, Parsable};

pub fn parse_instance_block<IK: InstanceIdentifierKind>(
    file_id: FileId,
    state: &mut State,
    pair: Pair,
) -> InstanceBlock<IK>
where
    InstanceBlock<IK>: InArena + NodeType,
    InstanceItemList<IK>: Parsable,
    Identifier<IK>: Parsable,
    Identifier<IK::InstanceIdentifierKind>: Parsable,
    Identifier<IK::InstantiatedIdentifierKind>: Parsable,
{
    let mut inner = pair.into_inner();
    let _kw_instance = inner.next().unwrap();
    let instance_name_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
    let instance_name = Identifier::parse_ref(file_id, state, inner.next().unwrap());
    let eq_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
    let instantiated_name_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
    let instantiated_name = Identifier::parse_ref(file_id, state, inner.next().unwrap());
    let brace_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
    let items = InstanceItemList::parse_ref(file_id, state, inner.next().unwrap());

    InstanceBlock {
        instance_name_trivia,
        instance_name,
        eq_trivia,
        instantiated_name_trivia,
        instantiated_name,
        brace_trivia,
        items,
    }
}

pub fn parse_instance_const_assignment_item<LhsIK, RhsEK>(
    file_id: FileId,
    state: &mut State,
    pair: Pair,
) -> InstanceConstAssignmentItem<LhsIK, RhsEK>
where
    LhsIK: ValueIdentifierKind + InstanceAssignmentLhsKind<RhsKind = RhsEK>,
    RhsEK: ExpressionKind,
    Identifier<LhsIK>: Parsable,
    Expression<RhsEK>: Parsable,
{
    let mut inner = pair.into_inner();
    let ident = Identifier::parse_ref(file_id, state, inner.next().unwrap());
    let colon_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
    let _colon = Colon::parse_ref(file_id, state, inner.next().unwrap());
    let expr_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
    let expr = Expression::<RhsEK>::parse_ref(file_id, state, inner.next().unwrap());

    InstanceConstAssignmentItem {
        ident,
        colon_trivia,
        expr_trivia,
        expr,
    }
}

pub fn parse_instance_type_assignment_item<LhsIK, RhsTK>(
    file_id: FileId,
    state: &mut State,
    pair: Pair,
) -> InstanceTypeAssignmentItem<LhsIK, RhsTK>
where
    LhsIK: TypeIdentifierKind + InstanceAssignmentLhsKind<RhsKind = RhsTK>,
    RhsTK: TypeKind,
    Identifier<LhsIK>: Parsable,
    Type<RhsTK>: Parsable,
{
    let mut inner = pair.into_inner();
    let ident = Identifier::parse_ref(file_id, state, inner.next().unwrap());
    let colon_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
    let _colon = Colon::parse_ref(file_id, state, inner.next().unwrap());
    let ty_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
    let ty = Type::<RhsTK>::parse_ref(file_id, state, inner.next().unwrap());

    InstanceTypeAssignmentItem {
        ident,
        colon_trivia,
        ty_trivia,
        ty,
    }
}
