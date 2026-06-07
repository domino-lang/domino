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
        Padded, PaddedRef, Trivia,
    },
};

#[derive(Debug, Clone, Copy)]
pub struct InstanceConstAssignmentItem<LhsIK, RhsIK>
where
    LhsIK: ValueIdentifierKind + InstanceAssignmentLhsKind<RhsIdentifierKind = RhsIK>,
    RhsIK: ValueIdentifierKind,
{
    pub ident: Ref<Identifier<LhsIK>>,
    pub colon: Padded<Colon>,
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
    pub colon: Padded<Colon>,
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
    pub name: PaddedRef<Identifier<IK>>,
    pub items: Ref<InstanceItemList<IK>>,
}
