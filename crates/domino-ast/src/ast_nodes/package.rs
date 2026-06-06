use crate::{
    arena::Ref,
    ast_nodes::{
        identifier::{
            Identifier, IdentifierKind, PackageIdentifier, PackageTypeArgumentIdentifierKind,
            PackageTypeIdentifier, PackageTypeIdentifierKind,
        },
        list::{Comma, List, ListNoDelim, Semicolon},
        oracles::{OracleDefinition, OracleSignature, OracleValueDeclList},
        types, ListItem, PaddedRef, Parsable, Trivia,
    },
    Rule,
};

#[derive(Debug, Clone, Copy)]
pub struct Package {
    pub name: PaddedRef<PackageIdentifier>,
    pub items: Ref<PackageItemList>,
}

#[derive(Debug, Clone, Copy)]
pub enum PackageItem {
    TypeParams(Ref<PackageTypeParamBlock>),
    ConstParams(Ref<ConstParamBlock>),
    State(Ref<StateBlock>),
    ImportOracles(Ref<ImportOraclesBlock>),
    OracleDefinition(Ref<OracleDefinition>),
}

impl ListItem for PackageItem {
    const LIST_RULE: Rule = Rule::package_item_list;
}

#[derive(Debug, Clone, Copy)]
pub struct TypeParamBlock<IK: IdentifierKind> {
    pub trivia: Ref<Trivia>,
    pub decls: Ref<TypeDeclList<IK>>,
}

pub type PackageTypeParamBlock = TypeParamBlock<PackageTypeIdentifierKind>;

#[derive(Debug, Clone, Copy)]
pub struct ConstParamBlock {
    pub trivia: Ref<Trivia>,
    pub decls: Ref<OracleValueDeclList>,
}

#[derive(Debug, Clone, Copy)]
pub struct StateBlock {
    pub trivia: Ref<Trivia>,
    pub decls: Ref<OracleValueDeclList>,
}

#[derive(Debug, Clone, Copy)]
pub struct ImportOraclesBlock {
    pub trivia: Ref<Trivia>,
    pub decls: Ref<OracleDeclList>,
}

pub type OracleDeclList = List<OracleSignature, Semicolon>;
pub type TypeDeclList<IK: IdentifierKind> = List<Identifier<IK>, Comma>;
pub type PackageTypeDeclList = TypeDeclList<PackageTypeIdentifierKind>;
pub type PackageItemList = ListNoDelim<PackageItem>;

pub type PackageType = types::Type<PackageTypeIdentifierKind>;
pub type PackageArgumentedType = types::ArgumentedType<PackageTypeArgumentIdentifierKind>;
pub type PackageTypeArgument = types::TypeArgument<PackageTypeArgumentIdentifierKind>;

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
            Rule::types_param_block => PackageItem::TypeParams(PackageTypeParamBlock::parse_ref(
                file_id, state, inner_pair,
            )),
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

        let trivia = Trivia::parse_ref(file_id, state, trivia_pair);
        let decls = OracleValueDeclList::parse_ref(file_id, state, decls_pair);

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

        let trivia = Trivia::parse_ref(file_id, state, trivia_pair);
        let decls = OracleDeclList::parse_ref(file_id, state, decls_pair);

        Self { trivia, decls }
    }
}

impl Parsable for PackageTypeParamBlock {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::types_param_block);

        let mut inner = pair.into_inner();

        let _kw_pair = inner.next().unwrap();
        let trivia_pair = inner.next().unwrap();
        let decls_pair = inner.next().unwrap();

        let trivia = Trivia::parse_ref(file_id, state, trivia_pair);
        let decls = List::<PackageTypeIdentifier, Comma>::parse_ref(file_id, state, decls_pair);

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

        let trivia = Trivia::parse_ref(file_id, state, trivia_pair);
        let decls = OracleValueDeclList::parse_ref(file_id, state, decls_pair);

        Self { trivia, decls }
    }
}

#[cfg(debug_assertions)]
#[allow(dead_code)]
mod static_asserts {
    use super::*;

    fn is_parsable<T: Parsable>() {}

    fn ensure_are_parsable() {
        is_parsable::<PackageTypeDeclList>();
    }
}
