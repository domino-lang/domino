use crate::{
    arena::Ref,
    ast_nodes::{
        identifier::{
            Identifier, InstanceAssignmentLhsKind, InstanceIdentifierKind, TypeIdentifierKind,
            ValueIdentifierKind,
        },
        list::{Colon, Comma, List, ListNoDelim},
        pure_expressions::PureExpression,
        types::Type,
        InArena, Indexable, NodeType, Parsable, Trivia,
    },
    source::FileId,
    Pair, Rule, State,
};

#[derive(Debug, Clone, Copy)]
pub struct InstanceConstAssignmentItem<LhsIK, RhsIK>
where
    LhsIK: ValueIdentifierKind + InstanceAssignmentLhsKind<RhsIdentifierKind = RhsIK>,
    RhsIK: ValueIdentifierKind,
{
    pub ident: Ref<Identifier<LhsIK>>,
    pub colon_trivia: Ref<Trivia>,
    pub expr_trivia: Ref<Trivia>,
    pub expr: Ref<PureExpression<RhsIK>>,
}

pub type InstanceConstAssignmentList<LhsIK, RhsIK>
where
    LhsIK: ValueIdentifierKind + InstanceAssignmentLhsKind<RhsIdentifierKind = RhsIK>,
    RhsIK: ValueIdentifierKind,
= List<InstanceConstAssignmentItem<LhsIK, RhsIK>, Comma>;

#[derive(Debug, Clone, Copy)]
pub struct InstanceConstBlock<LhsIK, RhsIK>
where
    LhsIK: ValueIdentifierKind + InstanceAssignmentLhsKind<RhsIdentifierKind = RhsIK>,
    RhsIK: ValueIdentifierKind,
{
    pub trivia: Ref<Trivia>,
    pub list: Ref<InstanceConstAssignmentList<LhsIK, RhsIK>>,
}

#[derive(Debug, Clone, Copy)]
pub struct InstanceTypeAssignmentItem<LhsIK, RhsIK>
where
    LhsIK: TypeIdentifierKind + InstanceAssignmentLhsKind,
    RhsIK: TypeIdentifierKind,
{
    pub ident: Ref<Identifier<LhsIK>>,
    pub colon_trivia: Ref<Trivia>,
    pub ty_trivia: Ref<Trivia>,
    pub ty: Ref<Type<RhsIK>>,
}

pub type InstanceTypeAssignmentList<LhsIK, RhsIK>
where
    LhsIK: TypeIdentifierKind + InstanceAssignmentLhsKind,
    RhsIK: TypeIdentifierKind,
= List<InstanceTypeAssignmentItem<LhsIK, RhsIK>, Comma>;

#[derive(Debug, Clone, Copy)]
pub struct InstanceTypeBlock<LhsIK, RhsIK>
where
    LhsIK: TypeIdentifierKind + InstanceAssignmentLhsKind,
    RhsIK: TypeIdentifierKind,
{
    pub trivia: Ref<Trivia>,
    pub list: Ref<InstanceTypeAssignmentList<LhsIK, RhsIK>>,
}

#[derive(Debug, Clone, Copy)]
pub enum InstanceItem<IK: InstanceIdentifierKind> {
    InstanceConst(Ref<InstanceConstBlock<IK::LhsValueIdentifierKind, IK::RhsValueIdentifierKind>>),
    InstanceType(Ref<InstanceTypeBlock<IK::LhsTypeIdentifierKind, IK::RhsTypeIdentifierKind>>),
}

pub type InstanceItemList<IK: ValueIdentifierKind> = ListNoDelim<InstanceItem<IK>>;

#[derive(Debug, Clone, Copy)]
pub struct InstanceBlock<IK: InstanceIdentifierKind> {
    pub name_trivia: Ref<Trivia>,
    pub name: Ref<Identifier<IK>>,
    pub brace_trivia: Ref<Trivia>,
    pub items: Ref<InstanceItemList<IK>>,
}

pub fn parse_instance_block<IK: InstanceIdentifierKind>(
    file_id: FileId,
    state: &mut State,
    pair: Pair,
) -> InstanceBlock<IK>
where
    InstanceBlock<IK>: InArena + NodeType + Indexable,
    InstanceItemList<IK>: Parsable,
    Identifier<IK>: Parsable,
{
    debug_assert_eq!(pair.as_rule(), Rule::inst_block);

    let mut inner = pair.into_inner();
    let _kw_instance = inner.next().unwrap();
    let name_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
    let name = Identifier::parse_ref(file_id, state, inner.next().unwrap());
    let brace_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
    let items = InstanceItemList::parse_ref(file_id, state, inner.next().unwrap());

    InstanceBlock {
        name_trivia,
        name,
        brace_trivia,
        items,
    }
}

pub fn parse_instance_const_assignment_item<LhsIK, RhsIK>(
    file_id: FileId,
    state: &mut State,
    pair: Pair,
) -> InstanceConstAssignmentItem<LhsIK, RhsIK>
where
    LhsIK: ValueIdentifierKind + InstanceAssignmentLhsKind<RhsIdentifierKind = RhsIK>,
    RhsIK: ValueIdentifierKind,
    Identifier<LhsIK>: Parsable,
    PureExpression<RhsIK>: Parsable,
{
    debug_assert_eq!(pair.as_rule(), Rule::inst_const_assignment_item);

    let mut inner = pair.into_inner();
    let ident = Identifier::parse_ref(file_id, state, inner.next().unwrap());
    let colon_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
    let _colon = Colon::parse_ref(file_id, state, inner.next().unwrap());
    let expr_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
    let expr = PureExpression::<RhsIK>::parse_ref(file_id, state, inner.next().unwrap());

    InstanceConstAssignmentItem {
        ident,
        colon_trivia,
        expr_trivia,
        expr,
    }
}

pub fn parse_instance_type_assignment_item<LhsIK, RhsIK>(
    file_id: FileId,
    state: &mut State,
    pair: Pair,
) -> InstanceTypeAssignmentItem<LhsIK, RhsIK>
where
    LhsIK: TypeIdentifierKind + InstanceAssignmentLhsKind<RhsIdentifierKind = RhsIK>,
    RhsIK: TypeIdentifierKind,
    Identifier<LhsIK>: Parsable,
    Type<RhsIK>: Parsable,
{
    debug_assert_eq!(pair.as_rule(), Rule::inst_type_assignment_item);

    let mut inner = pair.into_inner();
    let ident = Identifier::parse_ref(file_id, state, inner.next().unwrap());
    let colon_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
    let _colon = Colon::parse_ref(file_id, state, inner.next().unwrap());
    let ty_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
    let ty = Type::<RhsIK>::parse_ref(file_id, state, inner.next().unwrap());

    InstanceTypeAssignmentItem {
        ident,
        colon_trivia,
        ty_trivia,
        ty,
    }
}
