use crate::{
    arena::Ref,
    ast_nodes::{
        expressions::{self, ExpressionKind},
        game,
        identifier::{self, Identifier, IdentifierKind, TypeIdentifierKind, ValueIdentifierKind},
        list::{Colon, Comma, List, ListNoDelim},
        theorem,
        types::{self, Type},
        InArena, NodeType, Parsable, Trivia,
    },
    source::FileId,
    Pair, State,
};

/// This is implemented on the Kind that contains the assignments.
/// For example, the impl for PackageInstanceIdentifierKind contains the assignment of
/// GameExpressionKind to PackageConstValueIdentifierKind.
pub trait InstanceIdentifierKind: IdentifierKind {
    type InstanceIdentifierKind: IdentifierKind;
    type InstantiatedIdentifierKind: IdentifierKind;

    type LhsValueIdentifierKind: ValueIdentifierKind
        + InstanceAssignmentLhsKind<RhsKind = Self::RhsExpressionKind>;
    type RhsExpressionKind: expressions::ExpressionKind;

    type LhsTypeIdentifierKind: TypeIdentifierKind
        + InstanceAssignmentLhsKind<RhsKind = Self::RhsTypeKind>;
    type RhsTypeKind: types::TypeKind;
}

/// This indicates that an identifier is can be a left hand side in an assignment. The assigned kind
/// is the RhsKind. Depending on the context, it can be an ExpressionKind or a TypeKind.
pub trait InstanceAssignmentLhsKind {
    type RhsKind;
}

// impl for assignments in package instantiations
impl InstanceIdentifierKind for identifier::PackageInstanceIdentifierKind {
    type InstanceIdentifierKind = identifier::PackageInstanceIdentifierKind;

    type InstantiatedIdentifierKind = identifier::PackageIdentifierKind;

    type LhsValueIdentifierKind = identifier::PackageConstValueIdentifierKind;

    type RhsExpressionKind = game::PureGameExpressionKind;

    type LhsTypeIdentifierKind = identifier::PackageTypeIdentifierKind;

    type RhsTypeKind = types::GameTypeKind;
}

// impl for assignments in game instantiations
impl InstanceIdentifierKind for identifier::GameInstanceIdentifierKind {
    type InstanceIdentifierKind = identifier::GameInstanceIdentifierKind;

    type InstantiatedIdentifierKind = identifier::GameIdentifierKind;

    type LhsValueIdentifierKind = identifier::GameConstValueIdentifierKind;

    type RhsExpressionKind = theorem::PureTheoremExpressionKind;

    type LhsTypeIdentifierKind = identifier::GameTypeIdentifierKind;

    type RhsTypeKind = types::TheoremTypeKind;
}

// impl for const assignments in package instantiations
impl InstanceAssignmentLhsKind for identifier::PackageConstValueIdentifierKind {
    type RhsKind = game::PureGameExpressionKind;
}

// impl for type assignments in package instantiations
impl InstanceAssignmentLhsKind for identifier::PackageTypeIdentifierKind {
    type RhsKind = types::GameTypeKind;
}

// impl for const assignments in game instantiations
impl InstanceAssignmentLhsKind for identifier::GameConstValueIdentifierKind {
    type RhsKind = theorem::PureTheoremExpressionKind;
}

// impl for type assignments in game instantiations
impl InstanceAssignmentLhsKind for identifier::GameTypeIdentifierKind {
    type RhsKind = types::TheoremTypeKind;
}

#[derive(Debug, Clone, Copy)]
pub struct InstanceConstAssignmentItem<LhsIK, RhsEK>
where
    LhsIK: ValueIdentifierKind + InstanceAssignmentLhsKind,
    RhsEK: ExpressionKind,
{
    pub ident: Ref<Identifier<LhsIK>>,
    pub colon_trivia: Ref<Trivia>,
    pub expr_trivia: Ref<Trivia>,
    pub expr: Ref<expressions::Expression<RhsEK>>,
}

pub type InstanceConstAssignmentList<LhsIK, RhsIK>
where
    LhsIK: ValueIdentifierKind + InstanceAssignmentLhsKind<RhsKind = RhsIK>,
    RhsIK: ValueIdentifierKind,
= List<InstanceConstAssignmentItem<LhsIK, RhsIK>, Comma>;

#[derive(Debug, Clone, Copy)]
pub struct InstanceConstBlock<LhsIK, RhsEK>
where
    LhsIK: ValueIdentifierKind + InstanceAssignmentLhsKind<RhsKind = RhsEK>,
    RhsEK: ExpressionKind,
{
    pub trivia: Ref<Trivia>,
    pub list: Ref<InstanceConstAssignmentList<LhsIK, RhsEK>>,
}

#[derive(Debug, Clone, Copy)]
pub struct InstanceTypeAssignmentItem<LhsIK, RhsTK>
where
    LhsIK: TypeIdentifierKind + InstanceAssignmentLhsKind<RhsKind = RhsTK>,
    RhsTK: types::TypeKind,
{
    pub ident: Ref<Identifier<LhsIK>>,
    pub colon_trivia: Ref<Trivia>,
    pub ty_trivia: Ref<Trivia>,
    pub ty: Ref<Type<RhsTK>>,
}

pub type InstanceTypeAssignmentList<LhsIK, RhsTK>
where
    LhsIK: TypeIdentifierKind + InstanceAssignmentLhsKind<RhsKind = RhsTK>,
    RhsTK: types::TypeKind,
= List<InstanceTypeAssignmentItem<LhsIK, RhsTK>, Comma>;

#[derive(Debug, Clone, Copy)]
pub struct InstanceTypeBlock<LhsIK, RhsTK>
where
    LhsIK: TypeIdentifierKind + InstanceAssignmentLhsKind<RhsKind = RhsTK>,
    RhsTK: types::TypeKind,
{
    pub trivia: Ref<Trivia>,
    pub list: Ref<InstanceTypeAssignmentList<LhsIK, RhsTK>>,
}

#[derive(Debug, Clone, Copy)]
pub enum InstanceItem<IK: InstanceIdentifierKind> {
    InstanceConst(Ref<InstanceConstBlock<IK::LhsValueIdentifierKind, IK::RhsExpressionKind>>),
    InstanceType(Ref<InstanceTypeBlock<IK::LhsTypeIdentifierKind, IK::RhsTypeKind>>),
}

pub type InstanceItemList<IK: ValueIdentifierKind> = ListNoDelim<InstanceItem<IK>>;

#[derive(Debug, Clone, Copy)]
pub struct InstanceBlock<IK: InstanceIdentifierKind> {
    pub instance_name_trivia: Ref<Trivia>,
    pub instance_name: Ref<Identifier<IK::InstanceIdentifierKind>>,
    pub eq_trivia: Ref<Trivia>,
    pub instantiated_name_trivia: Ref<Trivia>,
    pub instantiated_name: Ref<Identifier<IK::InstantiatedIdentifierKind>>,
    pub brace_trivia: Ref<Trivia>,
    pub items: Ref<InstanceItemList<IK>>,
}

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
    RhsEK: expressions::ExpressionKind,
    Identifier<LhsIK>: Parsable,
    expressions::Expression<RhsEK>: Parsable,
{
    let mut inner = pair.into_inner();
    let ident = Identifier::parse_ref(file_id, state, inner.next().unwrap());
    let colon_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
    let _colon = Colon::parse_ref(file_id, state, inner.next().unwrap());
    let expr_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
    let expr = expressions::Expression::<RhsEK>::parse_ref(file_id, state, inner.next().unwrap());

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
    RhsTK: types::TypeKind,
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
