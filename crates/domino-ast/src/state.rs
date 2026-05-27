use crate::ast_nodes::{NodeTypeId, PaddedRef};

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct GlobalRefId(pub NodeTypeId, pub u32);

#[derive(Default, Debug)]
pub struct State {
    pub arenas: Arenas,
    pub tables: crate::side_tables::Tables,
    pub parse_context: ParseContext,
}

#[derive(Default, Debug)]
pub struct ParseContext {
    pub trivia: TriviaParseContext,
}

#[derive(Default, Debug)]
pub struct TriviaParseContext {
    pub newlines_span_start: Option<u32>,
}

define_arenas! {
    source: crate::source::SourceFile,

    trivia: crate::ast_nodes::Trivia,

    type_idents: crate::ast_nodes::identifier::TypeIdentifier,
    type_argument_idents: crate::ast_nodes::identifier::TypeArgumentIdentifier,
    oracle_value_idents: crate::ast_nodes::identifier::OracleValueIdentifier,
    oracle_const_value_idents: crate::ast_nodes::identifier::OracleConstValueIdentifier,
    oracle_idents: crate::ast_nodes::identifier::OracleIdentifier,
    padded_oracle_const_value_idents: PaddedRef<crate::ast_nodes::identifier::OracleConstValueIdentifier>,
    padded_type_idents: PaddedRef<crate::ast_nodes::identifier::TypeIdentifier>,
    package_idents: crate::ast_nodes::identifier::PackageIdentifier,
    padded_package_idents: PaddedRef<crate::ast_nodes::identifier::PackageIdentifier>,

    type_lists: crate::ast_nodes::types::TypeList,
    oracle_expression_arglist: crate::ast_nodes::oracle_expressions::ExprList,
    statement_lists: crate::ast_nodes::statements::StatementList,
    pattern_lists: crate::ast_nodes::statements::PatternList,
    arg_decl_lists: crate::ast_nodes::oracles::DeclList,
    pure_const_oracle_expression_lists: crate::ast_nodes::pure_expressions::PureConstOracleExpressionList,
    padded_pure_const_oracle_expression_lists: PaddedRef<crate::ast_nodes::pure_expressions::PureConstOracleExpressionList>,

    types: crate::ast_nodes::types::Type,
    padded_types: PaddedRef<crate::ast_nodes::types::Type>,
    argd_types: crate::ast_nodes::types::ArgumentedType,
    tuple_types: crate::ast_nodes::types::TupleType,
    padded_type_ident_list: crate::ast_nodes::package::TypeDeclList,

    // pure/const expressions in oracles. can only reference package const.
    // used mostly in types, e.g. Bits(n)
    // TODO: maybe no need to distinguish from "used in state"?
    pure_expressions_oracle: crate::ast_nodes::pure_expressions::PureExpression<crate::ast_nodes::identifier::OracleConstValueIdentifierKind>,
    pure_expressions_oracle_table_index: crate::ast_nodes::pure_expressions::TableIndexExpression<crate::ast_nodes::identifier::OracleConstValueIdentifierKind>,
    pure_expressions_oracle_tuple: crate::ast_nodes::pure_expressions::TupleExpression<crate::ast_nodes::identifier::OracleConstValueIdentifierKind>,
    pure_expressions_oracle_binop: crate::ast_nodes::pure_expressions::BinOpExpression<crate::ast_nodes::identifier::OracleConstValueIdentifierKind>,
    pure_expressions_oracle_unop: crate::ast_nodes::pure_expressions::UnOpExpression<crate::ast_nodes::identifier::OracleConstValueIdentifierKind>,
    pure_expressions_oracle_call: crate::ast_nodes::pure_expressions::CallExpression<crate::ast_nodes::identifier::OracleConstValueIdentifierKind>,
    pure_expressions_oracle_paren: crate::ast_nodes::pure_expressions::ParenExpression<crate::ast_nodes::identifier::OracleConstValueIdentifierKind>,
    padded_pure_expressions_oracle: PaddedRef<crate::ast_nodes::pure_expressions::PureExpression<crate::ast_nodes::identifier::OracleConstValueIdentifierKind>>,

    // expressions in oracles that can have side-effects
    oracle_expressions: crate::ast_nodes::oracle_expressions::OracleExpression,
    oracle_binop_expressions: crate::ast_nodes::oracle_expressions::BinOpExpression,
    oracle_unop_expressions: crate::ast_nodes::oracle_expressions::UnOpExpression,
    oracle_invocation_expressions: crate::ast_nodes::oracle_expressions::OracleInvocationExpression,
    table_index_expressions: crate::ast_nodes::oracle_expressions::TableIndexExpression,
    sample_expressions: crate::ast_nodes::oracle_expressions::SampleExpression,
    paren_expressions: crate::ast_nodes::oracle_expressions::ParenExpression,
    tuple_expressions: crate::ast_nodes::oracle_expressions::TupleExpression,
    call_expressions: crate::ast_nodes::oracle_expressions::CallExpression,
    padded_oracle_expressions: PaddedRef<crate::ast_nodes::oracle_expressions::OracleExpression>,

    statements: crate::ast_nodes::statements::Statement,
    assign_statements: crate::ast_nodes::statements::AssignStatement,
    return_statements: crate::ast_nodes::statements::ReturnStatement,
    expression_statements: crate::ast_nodes::statements::ExpressionStatement,
    ifthenelse_statements: crate::ast_nodes::statements::IfThenElseStatement,
    padded_statements: PaddedRef<crate::ast_nodes::statements::Statement>,

    patterns: crate::ast_nodes::statements::Pattern,
    tuple_patterns: crate::ast_nodes::statements::TuplePattern,
    table_patterns: crate::ast_nodes::statements::TablePattern,
    padded_patterns: PaddedRef<crate::ast_nodes::statements::Pattern>,

    oracle_definitions: crate::ast_nodes::oracles::OracleDefinition,
    oracle_signatures: crate::ast_nodes::oracles::OracleSignature,
    arg_decls: crate::ast_nodes::oracles::ArgDecl,
    padded_arg_decls: PaddedRef<crate::ast_nodes::oracles::ArgDecl>,
    padded_oracle_sigs: PaddedRef<crate::ast_nodes::oracles::OracleSignature>,

    oracle_decl_lists: crate::ast_nodes::package::OracleDeclList,
    import_oracles_block: crate::ast_nodes::package::ImportOraclesBlock,

    state_block: crate::ast_nodes::package::StateBlock,
    const_block: crate::ast_nodes::package::ConstParamBlock,
    type_block: crate::ast_nodes::package::TypeParamBlock,
    package_items: crate::ast_nodes::package::PackageItem,
    padded_package_items: PaddedRef<crate::ast_nodes::package::PackageItem>,
    package_item_lists: crate::ast_nodes::package::PackageItemList,
    packages: crate::ast_nodes::package::Package,

}

macro_rules! define_arenas {
    ($($name:ident: $ty:path),* $(,)?) => {
        #[derive(Default, Debug)]
        pub struct Arenas {
            $(pub $name : crate::arena::Arena<$ty>),*
        }

        $(
            impl crate::ast_nodes::ArenaNode for $ty {
                fn arena(arenas: &crate::state::Arenas) -> &crate::arena::Arena<Self> {
                    &arenas.$name
                }

                fn arena_mut(arenas: &mut crate::state::Arenas) -> &mut crate::arena::Arena<Self> {
                    &mut arenas.$name
                }
            }
        )*
    };
}
use define_arenas;
