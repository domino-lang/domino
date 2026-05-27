use std::marker::PhantomData;

use crate::ast_nodes::{PaddedRef, Parsable};

use super::impl_node_type;

pub trait IdentifierKind {}

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

macro_rules! define_ident_kind {
    ($id_code:literal, $padded_id_code:literal, $kind_name:ident, $ident_name:ident $(,)?) => {
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

        impl_node_type!($id_code, Identifier<$kind_name>, noop_index);

        // indexing done by blanket impl
        impl_node_type!($padded_id_code, PaddedRef<Identifier<$kind_name>>);
    };
}

define_ident_kind!(0x08, 0xf8, OracleIdentifierKind, OracleIdentifier);
define_ident_kind!(0x09, 0xf9, TypeIdentifierKind, TypeIdentifier);
define_ident_kind!(
    0x0a,
    0xfa,
    TypeArgumentIdentifierKind,
    TypeArgumentIdentifier
);
define_ident_kind!(0x0b, 0xfb, OracleValueIdentifierKind, OracleValueIdentifier);
define_ident_kind!(
    0x0c,
    0xfc,
    OracleConstValueIdentifierKind,
    OracleConstValueIdentifier,
);

define_ident_kind!(0x0d, 0xfd, PackageIdentifierKind, PackageIdentifier);
