use std::marker::PhantomData;

use crate::{ast_nodes::Parsable, Rule};

pub trait IdentifierKind {}
pub trait ValueIdentifierKind: IdentifierKind {
    type TypeIdentifierKind: TypeIdentifierKind;
}

pub trait TypeArgIdentifierKind: IdentifierKind {
    type ArgValueIdentifierKind: ValueIdentifierKind;
    type ArgTypeIdentifierKind: TypeIdentifierKind<ArgIdentifierKind = Self>;
}
pub trait TypeIdentifierKind: IdentifierKind {
    type ArgValueIdentifierKind: ValueIdentifierKind;
    type ArgIdentifierKind: TypeArgIdentifierKind<ArgTypeIdentifierKind = Self>;
}

pub trait InstanceIdentifierKind: IdentifierKind {
    type LhsValueIdentifierKind: ValueIdentifierKind
        + InstanceAssignmentLhsKind<RhsIdentifierKind = Self::RhsValueIdentifierKind>;
    type RhsValueIdentifierKind: ValueIdentifierKind;

    type LhsTypeIdentifierKind: TypeIdentifierKind
        + InstanceAssignmentLhsKind<RhsIdentifierKind = Self::RhsTypeIdentifierKind>;
    type RhsTypeIdentifierKind: TypeIdentifierKind;
}

pub trait InstanceAssignmentLhsKind: IdentifierKind {
    type RhsIdentifierKind: IdentifierKind;
}

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
        impl ValueIdentifierKind for $kind_name {
            type TypeIdentifierKind = $ty_ty;
        }

        pub type $ident_name = Identifier<$kind_name>;

        impl Parsable for $ident_name {
            const RULE: Rule = Rule::identifier;

            fn parse_inner(
                _file_id: crate::source::FileId,
                _state: &mut crate::State,
                _pair: crate::Pair,
            ) -> Self {
                Identifier::default()
            }
        }

        impl crate::ast_nodes::Indexable for $ident_name {}
    };
}

macro_rules! define_type_ident_kind {
    ($kind_name:ident, $ident_name:ident, $arg_kind:ty, $value_kind:ty $(,)?) => {
        #[derive(Debug, Clone, Copy)]
        pub struct $kind_name;
        impl IdentifierKind for $kind_name {}
        impl TypeIdentifierKind for $kind_name {
            type ArgIdentifierKind = $arg_kind;
            type ArgValueIdentifierKind = $value_kind;
        }

        pub type $ident_name = Identifier<$kind_name>;

        impl Parsable for $ident_name {
            const RULE: Rule = Rule::identifier;

            fn parse_inner(
                _file_id: crate::source::FileId,
                _state: &mut crate::State,
                _pair: crate::Pair,
            ) -> Self {
                Identifier::default()
            }
        }

        impl crate::ast_nodes::Indexable for $ident_name {}

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
        impl TypeArgIdentifierKind for $kind_name {
            type ArgValueIdentifierKind = $value_kind;
            type ArgTypeIdentifierKind = $type_kind;
        }

        pub type $ident_name = Identifier<$kind_name>;

        impl Parsable for $ident_name {
            const RULE: Rule = Rule::identifier;

            fn parse_inner(
                _file_id: crate::source::FileId,
                _state: &mut crate::State,
                _pair: crate::Pair,
            ) -> Self {
                Identifier::default()
            }
        }

        impl crate::ast_nodes::Indexable for $ident_name {}
    };
}

macro_rules! define_instance_ident_kind {
    ($kind_name:ident, $ident_name:ident, $lhs_ty_ty:ty = $rhs_ty_ty:ty, $lhs_val_ty:ty = $rhs_val_ty:ty $(,)?) => {
        #[derive(Debug, Clone, Copy)]
        pub struct $kind_name;
        impl IdentifierKind for $kind_name {}

        pub type $ident_name = Identifier<$kind_name>;

        impl InstanceIdentifierKind for $kind_name {
            type LhsTypeIdentifierKind = $lhs_ty_ty;
            type RhsTypeIdentifierKind = $rhs_ty_ty;
            type LhsValueIdentifierKind = $lhs_val_ty;
            type RhsValueIdentifierKind = $rhs_val_ty;
        }

        impl InstanceAssignmentLhsKind for $lhs_ty_ty {
            type RhsIdentifierKind = $rhs_ty_ty;
        }

        impl InstanceAssignmentLhsKind for $lhs_val_ty {
            type RhsIdentifierKind = $rhs_val_ty;
        }

        impl Parsable for $ident_name {
            const RULE: Rule = Rule::identifier;

            fn parse_inner(
                _file_id: crate::source::FileId,
                _state: &mut crate::State,
                _pair: crate::Pair,
            ) -> Self {
                Identifier::default()
            }
        }

        impl crate::ast_nodes::Indexable for $ident_name {}
    };
}

macro_rules! define_ident_kind {
    ($kind_name:ident, $ident_name:ident $(,)?) => {
        #[derive(Debug, Clone, Copy)]
        pub struct $kind_name;
        impl IdentifierKind for $kind_name {}

        pub type $ident_name = Identifier<$kind_name>;

        impl Parsable for $ident_name {
            const RULE: Rule = Rule::identifier;

            fn parse_inner(
                _file_id: crate::source::FileId,
                _state: &mut crate::State,
                _pair: crate::Pair,
            ) -> Self {
                Identifier::default()
            }
        }

        impl crate::ast_nodes::Indexable for $ident_name {}
    };
}

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
