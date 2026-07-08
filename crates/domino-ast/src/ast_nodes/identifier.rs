use std::marker::PhantomData;

use crate::{
    ast_nodes::{InArena, NodeType, Parsable},
    Rule,
};

/// Describes what the identifier refers to. We do this along two axes:
///
/// 1. Are you referring to a type? a value? a package?
/// 2. For types and values: is the thing you refer to defined in a package? a game? a theorem?
///
/// Doing (2) on the type level allows us to use per-kind side tables to store resolved types, which
/// then allows us to have infallible looksups (by checking first that all are set).
pub trait IdentifierKind {}

impl<IK: IdentifierKind + ?Sized> IdentifierKind for Box<IK> {}

pub trait ValueIdentifierKind: IdentifierKind {}
pub trait TypeArgIdentifierKind: IdentifierKind {}
pub trait TypeIdentifierKind: IdentifierKind {}

/// An identifier. The span is in the side table, and from there we can get the string.
/// Once we intern we might hve that in here (or in another side table).
pub struct Identifier<IK: IdentifierKind>(PhantomData<IK>);

impl<T: IdentifierKind> Clone for Identifier<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: IdentifierKind> core::fmt::Debug for Identifier<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("Identifier").field(&self.0).finish()
    }
}

impl<T: IdentifierKind> Copy for Identifier<T> {}

impl<T: IdentifierKind> Default for Identifier<T> {
    fn default() -> Self {
        Self(PhantomData)
    }
}

macro_rules! define_value_ident_kind {
    ($kind_name:ident, $ident_name:ident, $ty_ty:ty $(,)?) => {
        #[derive(Debug, Clone, Copy)]
        pub struct $kind_name;
        impl IdentifierKind for $kind_name {}
        impl ValueIdentifierKind for $kind_name {}

        pub type $ident_name = Identifier<$kind_name>;
    };
}

macro_rules! define_type_ident_kind {
    ($kind_name:ident, $ident_name:ident, $arg_kind:ty, $value_kind:ty $(,)?) => {
        #[derive(Debug, Clone, Copy)]
        pub struct $kind_name;
        impl IdentifierKind for $kind_name {}
        impl TypeIdentifierKind for $kind_name {}

        pub type $ident_name = Identifier<$kind_name>;

        impl crate::ast_nodes::ListItem for $ident_name {
            const LIST_RULE: Rule = Rule::ident_list;
        }
    };
}

macro_rules! define_type_arg_ident_kind {
    ($kind_name:ident, $ident_name:ident, $type_kind:ty, $value_kind:ty $(,)?) => {
        #[derive(Debug, Clone, Copy)]
        pub struct $kind_name;
        impl IdentifierKind for $kind_name {}
        impl TypeArgIdentifierKind for $kind_name {}

        pub type $ident_name = Identifier<$kind_name>;
    };
}

macro_rules! define_instance_ident_kind {
    ($kind_name:ident, $ident_name:ident, $lhs_ty_ty:ty = $rhs_ty_ty:ty, $lhs_val_ty:ty = $rhs_val_ty:ty $(,)?) => {
        #[derive(Debug, Clone, Copy)]
        pub struct $kind_name;
        impl IdentifierKind for $kind_name {}

        pub type $ident_name = Identifier<$kind_name>;
    };
}

macro_rules! define_ident_kind {
    ($kind_name:ident, $ident_name:ident $(,)?) => {
        #[derive(Debug, Clone, Copy)]
        pub struct $kind_name;
        impl IdentifierKind for $kind_name {}

        pub type $ident_name = Identifier<$kind_name>;
    };
}

impl<IK: IdentifierKind> Parsable for Identifier<IK>
where
    Identifier<IK>: NodeType + InArena,
{
    const RULE: Rule = Rule::identifier;

    fn parse_inner(
        _file_id: crate::source::FileId,
        _state: &mut crate::State,
        _pair: crate::Pair,
    ) -> Self {
        Identifier::default()
    }
}
impl<IK: IdentifierKind> crate::ast_nodes::Indexable for Identifier<IK> {}

define_type_ident_kind!(
    PackageTypeIdentifierKind,
    PackageTypeIdentifier,
    PackageTypeArgumentIdentifierKind,
    PackageConstValueIdentifierKind
);

define_type_ident_kind!(
    GameTypeIdentifierKind,
    GameTypeIdentifier,
    GameTypeArgumentIdentifierKind,
    GameConstValueIdentifierKind
);
define_type_ident_kind!(
    TheoremTypeIdentifierKind,
    TheoremTypeIdentifier,
    TheoremTypeArgumentIdentifierKind,
    TheoremConstValueIdentifierKind
);

define_type_arg_ident_kind!(
    PackageTypeArgumentIdentifierKind,
    PackageTypeArgumentIdentifier,
    PackageTypeIdentifierKind,
    PackageConstValueIdentifierKind
);
define_type_arg_ident_kind!(
    GameTypeArgumentIdentifierKind,
    GameTypeArgumentIdentifier,
    GameTypeIdentifierKind,
    GameConstValueIdentifierKind
);
define_type_arg_ident_kind!(
    TheoremTypeArgumentIdentifierKind,
    TheoremTypeArgumentIdentifier,
    TheoremTypeIdentifierKind,
    TheoremConstValueIdentifierKind
);

define_value_ident_kind!(
    OracleValueIdentifierKind,
    OracleValueIdentifier,
    PackageTypeIdentifierKind,
);
define_value_ident_kind!(
    PackageConstValueIdentifierKind,
    PackageConstValueIdentifier,
    PackageTypeIdentifierKind,
);
define_value_ident_kind!(
    GameConstValueIdentifierKind,
    GameConstValueIdentifier,
    GameTypeIdentifierKind,
);
define_value_ident_kind!(
    TheoremConstValueIdentifierKind,
    TheoremConstValueIdentifier,
    TheoremTypeIdentifierKind,
);

define_instance_ident_kind!(
    PackageInstanceIdentifierKind,
    PackageInstanceIdentifier,
    PackageTypeIdentifierKind = GameTypeIdentifierKind,
    PackageConstValueIdentifierKind = GameConstValueIdentifierKind,
);
define_instance_ident_kind!(
    GameInstanceIdentifierKind,
    GameInstanceIdentifier,
    GameTypeIdentifierKind = TheoremTypeIdentifierKind,
    GameConstValueIdentifierKind = TheoremConstValueIdentifierKind,
);

define_ident_kind!(OracleIdentifierKind, OracleIdentifier);
define_ident_kind!(PackageIdentifierKind, PackageIdentifier);

define_ident_kind!(GameIdentifierKind, GameIdentifier);
define_ident_kind!(AssumptionIdentifierKind, AssumptionIdentifier);
define_ident_kind!(LemmaIdentifierKind, LemmaIdentifier);
define_ident_kind!(TheoremIdentifierKind, TheoremIdentifier);
