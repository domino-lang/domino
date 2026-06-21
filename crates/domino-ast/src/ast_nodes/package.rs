use crate::{
    arena::Ref,
    ast_nodes::{
        common,
        identifier::{
            Identifier, PackageConstValueIdentifierKind, PackageIdentifier,
            PackageTypeArgumentIdentifierKind, PackageTypeIdentifier, PackageTypeIdentifierKind,
        },
        list::{Comma, List, ListNoDelim, Semicolon},
        oracles::{OracleDefinition, OracleSignature},
        params::{self, ConstParamBlock},
        types, ListItem, Parsable, Trivia,
    },
    Rule,
};

#[derive(Debug, Clone, Copy)]
pub struct Package {
    pub name_trivia: Ref<Trivia>,
    pub name: Ref<PackageIdentifier>,
    pub brace_trivia: Ref<Trivia>,
    pub items: Ref<PackageItemList>,
}

#[derive(Debug, Clone, Copy)]
pub enum PackageItem {
    TypeParams(Ref<PackageTypeParamBlock>),
    ConstParams(Ref<PackageConstParamBlock>),
    State(Ref<StateBlock>),
    ImportOracles(Ref<ImportOraclesBlock>),
    OracleDefinition(Ref<OracleDefinition>),
}

impl ListItem for PackageItem {
    const LIST_RULE: Rule = Rule::package_item_list;
}

pub type PackageTypeDeclList = common::TypeDeclList<PackageTypeIdentifierKind>;
pub type PackageTypeParamBlock = params::TypeParamBlock<PackageTypeIdentifierKind>;

pub type PackageConstDecl = common::ValueDecl<PackageConstValueIdentifierKind>;
pub type PackageConstDeclList = common::ConstDeclList<PackageConstValueIdentifierKind>;
pub type PackageConstParamBlock = params::ConstParamBlock<PackageConstValueIdentifierKind>;

#[derive(Debug, Clone, Copy)]
pub struct StateBlock {
    pub trivia: Ref<Trivia>,
    pub decls: Ref<PackageConstDeclList>,
}

#[derive(Debug, Clone, Copy)]
pub struct ImportOraclesBlock {
    pub trivia: Ref<Trivia>,
    pub decls: Ref<OracleDeclList>,
}

pub type OracleDeclList = List<OracleSignature, Semicolon>;
pub type PackageItemList = ListNoDelim<PackageItem>;

pub type PackageType = types::Type<PackageTypeIdentifierKind>;
pub type PackageArgumentedType = types::ArgumentedType<PackageTypeArgumentIdentifierKind>;
pub type PackageTypeArgument = types::TypeArgument<PackageTypeArgumentIdentifierKind>;

impl Parsable for Package {
    const RULE: Rule = Rule::package;

    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::package);

        let mut inner = pair.into_inner();

        let _kw_pair = inner.next().unwrap();
        let name_trivia_pair = inner.next().unwrap();
        let name_pair = inner.next().unwrap();
        let brace_trivia_pair = inner.next().unwrap();
        let items_pair = inner.next().unwrap();

        let name_trivia = Trivia::parse_ref(file_id, state, name_trivia_pair);
        let name = Identifier::parse_ref(file_id, state, name_pair);
        let brace_trivia = Trivia::parse_ref(file_id, state, brace_trivia_pair);
        let items = PackageItemList::parse_ref(file_id, state, items_pair);

        Self {
            name_trivia,
            name,
            brace_trivia,
            items,
        }
    }
}

impl Parsable for PackageItem {
    const RULE: Rule = Rule::package_item;

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
    const RULE: Rule = Rule::state_block;

    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::state_block);

        let mut inner = pair.into_inner();

        let _kw_pair = inner.next().unwrap();
        let trivia_pair = inner.next().unwrap();
        let decls_pair = inner.next().unwrap();

        let trivia = Trivia::parse_ref(file_id, state, trivia_pair);
        let decls = PackageConstDeclList::parse_ref(file_id, state, decls_pair);

        Self { trivia, decls }
    }
}

impl Parsable for ImportOraclesBlock {
    const RULE: Rule = Rule::import_oracles_block;

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
    const RULE: Rule = Rule::types_param_block;

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

impl Parsable for PackageConstDecl {
    const RULE: Rule = Rule::expr_ident_decl;

    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        common::parse_value_decl(file_id, state, pair)
    }
}

impl Parsable for PackageConstParamBlock {
    const RULE: Rule = Rule::consts_param_block;

    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::consts_param_block);

        let mut inner = pair.into_inner();

        let _kw_pair = inner.next().unwrap();
        let trivia_pair = inner.next().unwrap();
        let decls_pair = inner.next().unwrap();

        let trivia = Trivia::parse_ref(file_id, state, trivia_pair);
        let decls = PackageConstDeclList::parse_ref(file_id, state, decls_pair);

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
