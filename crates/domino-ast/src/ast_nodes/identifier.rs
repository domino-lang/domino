use std::marker::PhantomData;

use crate::{
    ast_nodes::{ListItem, Parsable},
    Rule,
};

pub trait IdentifierKind {}
pub trait ValueIdentifierKind: IdentifierKind {}

pub trait TypeArgIdentifierKind: IdentifierKind {
    type ArgValueIdentifierKind: ValueIdentifierKind;
    type ArgTypeIdentifierKind: TypeIdentifierKind<ArgIdentifierKind = Self>;
}
pub trait TypeIdentifierKind: IdentifierKind {
    type ArgValueIdentifierKind: ValueIdentifierKind;
    type ArgIdentifierKind: TypeArgIdentifierKind<ArgTypeIdentifierKind = Self>;
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
    ($kind_name:ident, $ident_name:ident $(,)?) => {
        #[derive(Debug)]
        pub struct $kind_name;
        impl IdentifierKind for $kind_name {}
        impl ValueIdentifierKind for $kind_name {}

        pub type $ident_name = Identifier<$kind_name>;

        impl Parsable for $ident_name {
            fn parse(
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
        #[derive(Debug)]
        pub struct $kind_name;
        impl IdentifierKind for $kind_name {}
        impl TypeIdentifierKind for $kind_name {
            type ArgIdentifierKind = $arg_kind;
            type ArgValueIdentifierKind = $value_kind;
        }

        pub type $ident_name = Identifier<$kind_name>;

        impl Parsable for $ident_name {
            fn parse(
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

macro_rules! define_type_arg_ident_kind {
    ($kind_name:ident, $ident_name:ident, $type_kind:ty, $value_kind:ty $(,)?) => {
        #[derive(Debug)]
        pub struct $kind_name;
        impl IdentifierKind for $kind_name {}
        impl TypeArgIdentifierKind for $kind_name {
            type ArgValueIdentifierKind = $value_kind;
            type ArgTypeIdentifierKind = $type_kind;
        }

        pub type $ident_name = Identifier<$kind_name>;

        impl Parsable for $ident_name {
            fn parse(
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
        #[derive(Debug)]
        pub struct $kind_name;
        impl IdentifierKind for $kind_name {}

        pub type $ident_name = Identifier<$kind_name>;

        impl Parsable for $ident_name {
            fn parse(
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

impl ListItem for PackageTypeIdentifier {
    const LIST_RULE: crate::Rule = Rule::ident_list;
}

define_type_ident_kind!(
    GameTypeIdentifierKind,
    GameTypeIdentifier,
    GameTypeArgumentIdentifierKind,
    GameConstValueIdentifierKind
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

define_value_ident_kind!(OracleValueIdentifierKind, OracleValueIdentifier);
define_value_ident_kind!(PackageConstValueIdentifierKind, PackageConstValueIdentifier,);
define_value_ident_kind!(GameConstValueIdentifierKind, GameConstValueIdentifier,);

define_ident_kind!(OracleIdentifierKind, OracleIdentifier);
define_ident_kind!(PackageIdentifierKind, PackageIdentifier);

define_ident_kind!(GameIdentifierKind, GameIdentifier);
define_ident_kind!(PackageInstanceIdentifierKind, PackageInstanceIdentifier);
