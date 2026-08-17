use std::marker::PhantomData;

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
pub trait OracleIdentifierKind: IdentifierKind {}

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
        #[derive(Debug, Clone, Copy)]
        pub struct $kind_name;
        impl IdentifierKind for $kind_name {}
        impl ValueIdentifierKind for $kind_name {}

        pub type $ident_name = Identifier<$kind_name>;
    };
}

macro_rules! define_type_ident_kind {
    ($kind_name:ident, $ident_name:ident $(,)?) => {
        #[derive(Debug, Clone, Copy)]
        pub struct $kind_name;
        impl IdentifierKind for $kind_name {}
        impl TypeIdentifierKind for $kind_name {}

        pub type $ident_name = Identifier<$kind_name>;
    };
}

macro_rules! define_type_arg_ident_kind {
    ($kind_name:ident, $ident_name:ident $(,)?) => {
        #[derive(Debug, Clone, Copy)]
        pub struct $kind_name;
        impl IdentifierKind for $kind_name {}
        impl TypeArgIdentifierKind for $kind_name {}

        pub type $ident_name = Identifier<$kind_name>;
    };
}

macro_rules! define_oracle_ident_kind {
    ($kind_name:ident, $ident_name:ident $(,)?) => {
        #[derive(Debug, Clone, Copy)]
        pub struct $kind_name;
        impl IdentifierKind for $kind_name {}
        impl OracleIdentifierKind for $kind_name {}

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

define_type_ident_kind!(PackageTypeIdentifierKind, PackageTypeIdentifier);
define_type_ident_kind!(GameTypeIdentifierKind, GameTypeIdentifier);
define_type_ident_kind!(TheoremTypeIdentifierKind, TheoremTypeIdentifier);

define_type_arg_ident_kind!(
    PackageTypeArgumentIdentifierKind,
    PackageTypeArgumentIdentifier
);
define_type_arg_ident_kind!(GameTypeArgumentIdentifierKind, GameTypeArgumentIdentifier);
define_type_arg_ident_kind!(
    TheoremTypeArgumentIdentifierKind,
    TheoremTypeArgumentIdentifier
);

define_value_ident_kind!(OracleValueIdentifierKind, OracleValueIdentifier);
define_value_ident_kind!(PackageConstValueIdentifierKind, PackageConstValueIdentifier);
define_value_ident_kind!(GameConstValueIdentifierKind, GameConstValueIdentifier);
define_value_ident_kind!(TheoremConstValueIdentifierKind, TheoremConstValueIdentifier);

define_oracle_ident_kind!(OracleImportIdentifierKind, OracleImportIdentifier);
define_oracle_ident_kind!(OracleDefinitionIdentifierKind, OracleDefinitionIdentifier);
define_oracle_ident_kind!(OracleCompositionIdentifierKind, OracleCompositionIdentifier);

define_ident_kind!(PackageIdentifierKind, PackageIdentifier);

define_ident_kind!(GameIdentifierKind, GameIdentifier);
define_ident_kind!(PackageInstanceIdentifierKind, PackageInstanceIdentifier);

define_ident_kind!(TheoremIdentifierKind, TheoremIdentifier);
define_ident_kind!(GameInstanceIdentifierKind, GameInstanceIdentifier);
define_ident_kind!(AssumptionIdentifierKind, AssumptionIdentifier);
define_ident_kind!(LemmaIdentifierKind, LemmaIdentifier);
