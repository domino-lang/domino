use crate::ast_nodes::{
    game,
    identifier::{self, PackageTypeIdentifierKind},
    list, oracle_expressions, oracles, package, pure_expressions, statements, types, NodeTypeEnum,
    Padded, PaddedRef, Trivia, Trivium,
};

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct GlobalRefId(pub NodeTypeEnum, pub u32);

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

    trivium: Trivium,
    trivia: Trivia,
    colons: list::Colon,
    padded_colons: Padded<list::Colon>,

    oracle_value_idents: identifier::OracleValueIdentifier,
    pkg_type_argument_idents: identifier::PackageTypeArgumentIdentifier,
    game_type_argument_idents: identifier::GameTypeArgumentIdentifier,

    pkg_type_idents: identifier::PackageTypeIdentifier,
    game_type_idents: identifier::GameTypeIdentifier,
    oracle_idents: identifier::OracleIdentifier,
    package_const_value_idents: identifier::PackageConstValueIdentifier,
    game_const_value_idents: identifier::GameConstValueIdentifier,
    package_idents: identifier::PackageIdentifier,
    game_idents: identifier::GameIdentifier,
    package_instance_ident: identifier::PackageInstanceIdentifier,

    padded_type_idents: PaddedRef<identifier::PackageTypeIdentifier>,
    padded_oracle_idents: PaddedRef<identifier::OracleIdentifier>,
    padded_oracle_const_value_idents: PaddedRef<identifier::PackageConstValueIdentifier>,
    padded_game_const_value_idents: PaddedRef<identifier::GameConstValueIdentifier>,
    padded_package_idents: PaddedRef<identifier::PackageIdentifier>,
    padded_game_idents: PaddedRef<identifier::GameIdentifier>,
    padded_package_instance_ident: PaddedRef<identifier::PackageInstanceIdentifier>,

    oracle_expression_arglist: oracle_expressions::ExprList,
    statement_lists: statements::StatementList,
    pattern_lists: statements::PatternList,
    arg_decl_lists: oracles::OracleValueDeclList,
    pure_const_package_expression_lists: pure_expressions::PureConstPackageExpressionList,
    pure_const_game_expression_lists: pure_expressions::PureConstGameExpressionList,
    padded_pure_const_oracle_expression_lists: PaddedRef<pure_expressions::PureConstPackageExpressionList>,

    pkg_type_ident_lists: package::PackageTypeIdentifierList,
    pkg_types: types::Type<identifier::PackageTypeIdentifierKind>,
    pkg_padded_types: PaddedRef<types::Type<identifier::PackageTypeIdentifierKind>>,
    pkg_argd_types: types::ArgumentedType<identifier::PackageTypeArgumentIdentifierKind>,
    pkg_tuple_types: types::TupleType<identifier::PackageTypeIdentifierKind>,
    pkg_type_arg: types::TypeArgument<identifier::PackageTypeArgumentIdentifierKind>,
    pkg_padded_type_arg: PaddedRef<types::TypeArgument<identifier::PackageTypeArgumentIdentifierKind>>,
    pkg_type_arg_lists: types::TypeArgList<identifier::PackageTypeArgumentIdentifierKind>,
    pkg_type_lists: types::TypeList<identifier::PackageTypeIdentifierKind>,

    game_types: types::Type<identifier::GameTypeIdentifierKind>,
    game_padded_types: PaddedRef<types::Type<identifier::GameTypeIdentifierKind>>,
    game_argd_types: types::ArgumentedType<identifier::GameTypeArgumentIdentifierKind>,
    game_tuple_types: types::TupleType<identifier::GameTypeIdentifierKind>,
    game_type_arg: types::TypeArgument<identifier::GameTypeArgumentIdentifierKind>,
    game_padded_type_arg: PaddedRef<types::TypeArgument<identifier::GameTypeArgumentIdentifierKind>>,
    game_type_arg_lists: types::TypeArgList<identifier::GameTypeArgumentIdentifierKind>,
    game_type_lists: types::TypeList<identifier::GameTypeIdentifierKind>,

    // pure/const expressions in oracles. can only reference package const.
    // used mostly in types, e.g. Bits(n)
    // TODO: maybe no need to distinguish from "used in state"?
    pure_expressions_package: pure_expressions::PureExpression<identifier::PackageConstValueIdentifierKind>,
    pure_expressions_package_table_index: pure_expressions::TableIndexExpression<identifier::PackageConstValueIdentifierKind>,
    pure_expressions_package_tuple: pure_expressions::TupleExpression<identifier::PackageConstValueIdentifierKind>,
    pure_expressions_package_binop: pure_expressions::BinOpExpression<identifier::PackageConstValueIdentifierKind>,
    pure_expressions_package_unop: pure_expressions::UnOpExpression<identifier::PackageConstValueIdentifierKind>,
    pure_expressions_package_call: pure_expressions::CallExpression<identifier::PackageConstValueIdentifierKind>,
    pure_expressions_package_paren: pure_expressions::ParenExpression<identifier::PackageConstValueIdentifierKind>,
    padded_pure_expressions_package: PaddedRef<pure_expressions::PureExpression<identifier::PackageConstValueIdentifierKind>>,

    pure_expressions_game: pure_expressions::PureExpression<identifier::GameConstValueIdentifierKind>,
    pure_expressions_game_table_index: pure_expressions::TableIndexExpression<identifier::GameConstValueIdentifierKind>,
    pure_expressions_game_tuple: pure_expressions::TupleExpression<identifier::GameConstValueIdentifierKind>,
    pure_expressions_game_binop: pure_expressions::BinOpExpression<identifier::GameConstValueIdentifierKind>,
    pure_expressions_game_unop: pure_expressions::UnOpExpression<identifier::GameConstValueIdentifierKind>,
    pure_expressions_game_call: pure_expressions::CallExpression<identifier::GameConstValueIdentifierKind>,
    pure_expressions_game_paren: pure_expressions::ParenExpression<identifier::GameConstValueIdentifierKind>,
    padded_pure_expressions_game: PaddedRef<pure_expressions::PureExpression<identifier::GameConstValueIdentifierKind>>,

    // expressions in oracles that can have side-effects
    oracle_expressions: oracle_expressions::OracleExpression,
    oracle_binop_expressions: oracle_expressions::BinOpExpression,
    oracle_unop_expressions: oracle_expressions::UnOpExpression,
    oracle_invocation_expressions: oracle_expressions::OracleInvocationExpression,
    table_index_expressions: oracle_expressions::TableIndexExpression,
    sample_expressions: oracle_expressions::SampleExpression<PackageTypeIdentifierKind>,
    paren_expressions: oracle_expressions::ParenExpression,
    tuple_expressions: oracle_expressions::TupleExpression,
    call_expressions: oracle_expressions::CallExpression,
    padded_oracle_expressions: PaddedRef<oracle_expressions::OracleExpression>,

    statements: statements::Statement,
    assign_statements: statements::AssignStatement,
    return_statements: statements::ReturnStatement,
    expression_statements: statements::ExpressionStatement,
    ifthenelse_statements: statements::IfThenElseStatement,
    padded_statements: PaddedRef<statements::Statement>,

    patterns: statements::Pattern,
    tuple_patterns: statements::TuplePattern,
    table_patterns: statements::TablePattern,
    padded_patterns: PaddedRef<statements::Pattern>,

    oracle_definitions: oracles::OracleDefinition,
    oracle_signatures: oracles::OracleSignature,
    arg_decls: oracles::OracleValueArgDecl,
    padded_arg_decls: PaddedRef<oracles::OracleValueArgDecl>,
    padded_oracle_sigs: PaddedRef<oracles::OracleSignature>,

    oracle_decl_lists: package::OracleDeclList,
    import_oracles_block: package::ImportOraclesBlock,

    state_block: package::StateBlock,
    const_block: package::ConstParamBlock,
    type_block: package::PackageTypeParamBlock,
    package_items: package::PackageItem,
    padded_package_items: PaddedRef<package::PackageItem>,
    package_item_lists: package::PackageItemList,
    packages: package::Package,

    package_instance_const_assign_items: game::InstanceConstAssignmentItem,
    padded_package_instance_const_assign_items: PaddedRef<game::InstanceConstAssignmentItem>,
    package_instance_const_assign_lists: game::InstanceConstAssignmentList,
    package_instance_const_blocks: game::InstanceConstBlock,

    package_instance_type_assign_items: game::InstanceTypeAssignmentItem,
    padded_package_instance_type_assign_items: PaddedRef<game::InstanceTypeAssignmentItem>,
    package_instance_type_assign_lists: game::InstanceTypeAssignmentList,
    package_instance_type_blocks: game::InstanceTypeBlock,

    package_instance_item: game::InstanceItem,
    padded_package_instance_item: PaddedRef<game::InstanceItem>,
    package_instance_item_list: game::InstanceItemList,
    package_instance_blocks: game::InstanceBlock,

    compose_oracle_assignment_item: game::ComposeOracleAssignmentItem,
    padded_compose_oracle_assignment_item: PaddedRef<game::ComposeOracleAssignmentItem>,
    compose_oracle_assignment_list: game::ComposeOracleAssignmentList,

    compose_package_instance_item: game::ComposePackageInstanceItem,
    padded_compose_package_instance_item: PaddedRef<game::ComposePackageInstanceItem>,
    compose_package_instance_list: game::ComposePackageInstanceList,
    compose_blocks: game::ComposeBlock,

    game_items: game::GameItem,
    padded_game_items: PaddedRef<game::GameItem>,
    game_item_lists: game::GameItemList,
    games: game::Game,
}

macro_rules! define_arenas {
    ($($name:ident: $ty:path),* $(,)?) => {
        #[derive(Default, Debug)]
        pub struct Arenas {
            $(pub $name : crate::arena::Arena<$ty>),*
        }

        $(
            impl crate::ast_nodes::InArena for $ty {
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
