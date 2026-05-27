use crate::{
    arena::{Ref, Slice},
    ast_nodes::{
        identifier::{Identifier, PackageIdentifier, TypeIdentifierKind},
        list::{Comma, List, Newlines, Semicolon},
        oracles::{DeclList, OracleDefinition, OracleSignature},
        PaddedRef, Parsable, Trivia,
    },
    Rule,
};

#[derive(Debug, Clone, Copy)]
pub struct Package {
    pub name: PaddedRef<PackageIdentifier>,
    pub items: Ref<List<PackageItem, Newlines>>,
}

#[derive(Debug, Clone, Copy)]
pub enum PackageItem {
    TypeParams(Ref<TypeParamBlock>),
    ConstParams(Ref<ConstParamBlock>),
    State(Ref<StateBlock>),
    ImportOracles(Ref<ImportOraclesBlock>),
    OracleDefinition(Ref<OracleDefinition>),
}

#[derive(Debug, Clone, Copy)]
pub struct TypeParamBlock {
    pub trivia: Slice<Trivia>,
    pub decls: Ref<TypeDeclList>,
}

#[derive(Debug, Clone, Copy)]
pub struct ConstParamBlock {
    pub trivia: Slice<Trivia>,
    pub decls: Ref<DeclList>,
}

#[derive(Debug, Clone, Copy)]
pub struct StateBlock {
    pub trivia: Slice<Trivia>,
    pub decls: Ref<DeclList>,
}

#[derive(Debug, Clone, Copy)]
pub struct ImportOraclesBlock {
    pub trivia: Slice<Trivia>,
    pub decls: Ref<OracleDeclList>,
}

pub type OracleDeclList = List<OracleSignature, Semicolon>;
pub type TypeDeclList = List<Identifier<TypeIdentifierKind>, Comma>;
pub type PackageItemList = List<PackageItem, Newlines>;

super::impl_node_type!(0x80, OracleDeclList, noop_index);
super::impl_node_type!(0x81, ImportOraclesBlock, noop_index);
super::impl_node_type!(0x84, StateBlock, noop_index);
super::impl_node_type!(0x85, ConstParamBlock, noop_index);
super::impl_node_type!(0x86, TypeDeclList, noop_index);
super::impl_node_type!(0x87, TypeParamBlock, noop_index);
super::impl_node_type!(0x88, PackageItem, noop_index);
super::impl_node_type!(0x89, PaddedRef<PackageItem>);
super::impl_node_type!(0x8a, Package, noop_index);
super::impl_node_type!(0x8b, PackageItemList, noop_index);

super::list::impl_comma_list!(
    OracleSignature,
    Rule::oracle_decl_list,
    Rule::padded_oracle_sig,
    Semicolon,
    Rule::semicolon
);

super::list::impl_comma_list!(
    Identifier<TypeIdentifierKind>,
    Rule::padded_ident_list,
    Rule::padded_ident
);

super::list::impl_comma_list!(
    PackageItem,
    Rule::package_item_list,
    Rule::padded_package_item,
    Newlines,
    Rule::newline
);

impl Parsable for Package {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::package);

        let mut inner = pair.into_inner();

        let _kw_pair = inner.next().unwrap();
        let name_pair = inner.next().unwrap();
        let items_pair = inner.next().unwrap();

        let name = PaddedRef::<Identifier<_>>::parse(file_id, state, name_pair);
        let items = PackageItemList::parse_ref(file_id, state, items_pair);

        Self { name, items }
    }
}

impl Parsable for PackageItem {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        let inner_pair = pair.into_inner().next().unwrap();
        match inner_pair.as_rule() {
            Rule::types_param_block => {
                PackageItem::TypeParams(TypeParamBlock::parse_ref(file_id, state, inner_pair))
            }
            Rule::consts_param_block => {
                PackageItem::ConstParams(ConstParamBlock::parse_ref(file_id, state, inner_pair))
            }
            Rule::state_block => {
                PackageItem::State(StateBlock::parse_ref(file_id, state, inner_pair))
            }
            Rule::import_oracles_block => PackageItem::ImportOracles(
                ImportOraclesBlock::parse_ref(file_id, state, inner_pair),
            ),
            Rule::oracle_def => PackageItem::OracleDefinition(OracleDefinition::parse_ref(
                file_id, state, inner_pair,
            )),

            _ => unreachable!(),
        }
    }
}

impl Parsable for StateBlock {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::state_block);

        let mut inner = pair.into_inner();

        let _kw_pair = inner.next().unwrap();
        let trivia_pair = inner.next().unwrap();
        let decls_pair = inner.next().unwrap();

        let trivia = Slice::<Trivia>::from_pair(file_id, state, trivia_pair);
        let decls = DeclList::parse_ref(file_id, state, decls_pair);

        Self { trivia, decls }
    }
}

impl Parsable for ImportOraclesBlock {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::import_oracles_block);

        let mut inner = pair.into_inner();

        let _kw_pair = inner.next().unwrap();
        let trivia_pair = inner.next().unwrap();
        let decls_pair = inner.next().unwrap();

        let trivia = Slice::<Trivia>::from_pair(file_id, state, trivia_pair);
        let decls = OracleDeclList::parse_ref(file_id, state, decls_pair);

        Self { trivia, decls }
    }
}

impl Parsable for TypeParamBlock {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::types_param_block);

        let mut inner = pair.into_inner();

        let _kw_pair = inner.next().unwrap();
        let trivia_pair = inner.next().unwrap();
        let decls_pair = inner.next().unwrap();

        let trivia = Slice::<Trivia>::from_pair(file_id, state, trivia_pair);
        let decls = TypeDeclList::parse_ref(file_id, state, decls_pair);

        Self { trivia, decls }
    }
}

impl Parsable for ConstParamBlock {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::consts_param_block);

        let mut inner = pair.into_inner();

        let _kw_pair = inner.next().unwrap();
        let trivia_pair = inner.next().unwrap();
        let decls_pair = inner.next().unwrap();

        let trivia = Slice::<Trivia>::from_pair(file_id, state, trivia_pair);
        let decls = DeclList::parse_ref(file_id, state, decls_pair);

        Self { trivia, decls }
    }
}
