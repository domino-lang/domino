use crate::ast_nodes::{
    game,
    identifier::{self, PackageTypeIdentifierKind},
    list, oracle_expressions, oracles, package, pure_expressions, statements, theorem, types,
    NodeTypeEnum, Trivia, Trivium,
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

    pkg_type_idents: identifier::PackageTypeIdentifier,
    game_type_idents: identifier::GameTypeIdentifier,
    theorem_type_idents: identifier::TheoremTypeIdentifier,

    pkg_type_argument_idents: identifier::PackageTypeArgumentIdentifier,
    game_type_argument_idents: identifier::GameTypeArgumentIdentifier,
    theorem_type_argument_idents: identifier::TheoremTypeArgumentIdentifier,

    oracle_value_idents: identifier::OracleValueIdentifier,
    package_const_value_idents: identifier::PackageConstValueIdentifier,
    game_const_value_idents: identifier::GameConstValueIdentifier,
    theorem_const_value_idents: identifier::TheoremConstValueIdentifier,

    oracle_idents: identifier::OracleIdentifier,
    package_idents: identifier::PackageIdentifier,
    game_idents: identifier::GameIdentifier,
    package_instance_ident: identifier::PackageInstanceIdentifier,
    game_instance_idents: identifier::GameInstanceIdentifier,
    assumption_idents: identifier::AssumptionIdentifier,
    lemma_ident: identifier::LemmaIdentifier,
    theorem_ident: identifier::TheoremIdentifier,


    oracle_expression_arglist: oracle_expressions::ExprList,
    statement_lists: statements::StatementList,
    pattern_lists: statements::PatternList,
    arg_decl_lists: oracles::OracleValueDeclList,
    pure_const_package_expression_lists: pure_expressions::PureConstPackageExpressionList,
    pure_const_game_expression_lists: pure_expressions::PureConstGameExpressionList,
    pure_const_theorem_expression_lists: pure_expressions::PureConstTheoremExpressionList,

    pkg_types: types::Type<identifier::PackageTypeIdentifierKind>,
    pkg_argd_types: types::ArgumentedType<identifier::PackageTypeArgumentIdentifierKind>,
    pkg_tuple_types: types::TupleType<identifier::PackageTypeIdentifierKind>,
    pkg_fn_types: types::FnType<identifier::PackageTypeIdentifierKind>,
    pkg_type_arg: types::TypeArgument<identifier::PackageTypeArgumentIdentifierKind>,
    pkg_type_arg_lists: types::TypeArgList<identifier::PackageTypeArgumentIdentifierKind>,
    pkg_type_lists: types::TypeList<identifier::PackageTypeIdentifierKind>,

    game_types: types::Type<identifier::GameTypeIdentifierKind>,
    game_argd_types: types::ArgumentedType<identifier::GameTypeArgumentIdentifierKind>,
    game_tuple_types: types::TupleType<identifier::GameTypeIdentifierKind>,
    game_fn_types: types::FnType<identifier::GameTypeIdentifierKind>,
    game_type_arg: types::TypeArgument<identifier::GameTypeArgumentIdentifierKind>,
    game_type_arg_lists: types::TypeArgList<identifier::GameTypeArgumentIdentifierKind>,
    game_type_lists: types::TypeList<identifier::GameTypeIdentifierKind>,

    theorem_types: types::Type<identifier::TheoremTypeIdentifierKind>,
    theorem_argd_types: types::ArgumentedType<identifier::TheoremTypeArgumentIdentifierKind>,
    theorem_tuple_types: types::TupleType<identifier::TheoremTypeIdentifierKind>,
    theorem_fn_types: types::FnType<identifier::TheoremTypeIdentifierKind>,
    theorem_type_arg: types::TypeArgument<identifier::TheoremTypeArgumentIdentifierKind>,
    theorem_type_arg_lists: types::TypeArgList<identifier::TheoremTypeArgumentIdentifierKind>,
    theorem_type_lists: types::TypeList<identifier::TheoremTypeIdentifierKind>,

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

    pure_expressions_game: pure_expressions::PureExpression<identifier::GameConstValueIdentifierKind>,
    pure_expressions_game_table_index: pure_expressions::TableIndexExpression<identifier::GameConstValueIdentifierKind>,
    pure_expressions_game_tuple: pure_expressions::TupleExpression<identifier::GameConstValueIdentifierKind>,
    pure_expressions_game_binop: pure_expressions::BinOpExpression<identifier::GameConstValueIdentifierKind>,
    pure_expressions_game_unop: pure_expressions::UnOpExpression<identifier::GameConstValueIdentifierKind>,
    pure_expressions_game_call: pure_expressions::CallExpression<identifier::GameConstValueIdentifierKind>,
    pure_expressions_game_paren: pure_expressions::ParenExpression<identifier::GameConstValueIdentifierKind>,

    pure_expressions_theorem: pure_expressions::PureExpression<identifier::TheoremConstValueIdentifierKind>,
    pure_expressions_theorem_table_index: pure_expressions::TableIndexExpression<identifier::TheoremConstValueIdentifierKind>,
    pure_expressions_theorem_tuple: pure_expressions::TupleExpression<identifier::TheoremConstValueIdentifierKind>,
    pure_expressions_theorem_binop: pure_expressions::BinOpExpression<identifier::TheoremConstValueIdentifierKind>,
    pure_expressions_theorem_unop: pure_expressions::UnOpExpression<identifier::TheoremConstValueIdentifierKind>,
    pure_expressions_theorem_call: pure_expressions::CallExpression<identifier::TheoremConstValueIdentifierKind>,
    pure_expressions_theorem_paren: pure_expressions::ParenExpression<identifier::TheoremConstValueIdentifierKind>,

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

    statements: statements::Statement,
    assign_statements: statements::AssignStatement,
    return_statements: statements::ReturnStatement,
    expression_statements: statements::ExpressionStatement,
    ifthenelse_statements: statements::IfThenElseStatement,

    patterns: statements::Pattern,
    tuple_patterns: statements::TuplePattern,
    table_patterns: statements::TablePattern,

    oracle_definitions: oracles::OracleDefinition,
    oracle_signatures: oracles::OracleSignature,
    arg_decls: oracles::OracleValueArgDecl,

    oracle_decl_lists: package::OracleDeclList,
    import_oracles_block: package::ImportOraclesBlock,

    package_const_decls: package::PackageConstDecl,
    package_const_decl_lists: package::PackageConstDeclList,

    state_block: package::StateBlock,
    package_const_block: package::PackageConstParamBlock,
    package_type_param_list: package::PackageTypeDeclList,
    type_block: package::PackageTypeParamBlock,
    package_items: package::PackageItem,
    package_item_lists: package::PackageItemList,
    packages: package::Package,

    package_instance_const_assign_items: game::InstanceConstAssignmentItem,
    package_instance_const_assign_lists: game::InstanceConstAssignmentList,
    package_instance_const_blocks: game::InstanceConstBlock,

    package_instance_type_assign_items: game::InstanceTypeAssignmentItem,
    package_instance_type_assign_lists: game::InstanceTypeAssignmentList,
    package_instance_type_blocks: game::InstanceTypeBlock,

    package_instance_item: game::InstanceItem,
    package_instance_item_list: game::InstanceItemList,
    package_instance_blocks: game::InstanceBlock,

    compose_oracle_assignment_item: game::ComposeOracleAssignmentItem,
    compose_oracle_assignment_list: game::ComposeOracleAssignmentList,

    compose_package_instance_item: game::ComposePackageInstanceItem,
    compose_package_instance_list: game::ComposePackageInstanceList,
    compose_blocks: game::ComposeBlock,

    game_const_decls: game::GameConstDecl,
    game_const_decl_lists: game::GameConstDeclList,
    game_const_param_blocks: game::GameConstParamBlock,

    game_type_decl_lists:game::GameTypeDeclList,
    game_type_param_blocks: game::GameTypeParamBlock,

    game_items: game::GameItem,
    game_item_lists: game::GameItemList,
    games: game::Game,

    //// instances
    game_const_assignment_items: theorem::InstanceConstAssignmentItem,
    game_const_assignment_item_lists: theorem::InstanceConstAssignmentList,
    game_const_assignment_blocks: theorem::InstanceConstBlock,

    game_type_assignment_items: theorem::InstanceTypeAssignmentItem,
    game_type_assignment_item_lists: theorem::InstanceTypeAssignmentList,
    game_type_assignment_blocks: theorem::InstanceTypeBlock,

    game_instance_items: theorem::InstanceItem,
    game_instance_item_lists: theorem::InstanceItemList,

    game_instance_block: theorem::InstanceBlock,

    //// hybrid instances
    // theorem_hybrid_instance_ones: theorem::HybridInstanceBlockOne,
    // theorem_hybrid_instance_twos: theorem::HybridInstanceBlockTwo,
    // theorem_hybrid_instances: theorem::HybridInstanceBlock,
    theorem_const_decls: theorem::TheoremConstDecl,
    theorem_const_decl_lists: theorem::TheoremConstDeclList,
    theorem_const_param_blocks: theorem::TheoremConstParamBlock,

    paths: theorem::Path,
    path_lists: theorem::PathList,
    invariant_specs: theorem::InvariantSpec,

    smt_identifiers: theorem::SmtIdentifier,
    smt_identifier_lists: theorem::SmtIdentifierList,
    lemma_items: theorem::LemmaItem,
    lemma_item_lists: theorem::LemmaItemList,
    lemma_blocks: theorem::LemmaBlock,
    equivalence_oracle_items: theorem::EquivalenceOracleItem,
    equivalence_oracle_item_lists: theorem::EquivalenceOracleItemList,
    equivalence_oracle_blocks: theorem::EquivalenceOracleBlock,
    equivalence_oracle_block_lists: theorem::EquivalenceOracleBlockList,
    equivalence_blocks: theorem::Equivalence,

    bounds: theorem::Bound,
    assumptions_item: theorem::AssumptionsItem,
    assumptions_item_list: theorem::AssumptionsItemList,
    assumptions_block: theorem::AssumptionsBlock,

    conjectures: theorem::Conjecture,

    reduction_assumption_lines: theorem::ReductionAssumptionLine,
    reduction_map_items: theorem::ReductionMapItem,
    reduction_map_item_lists: theorem::ReductionMapItemList,
    reduction_maps: theorem::ReductionMap,
    reduction_items: theorem::ReductionItem,
    reduction_item_lists: theorem::ReductionItemList,
    reductions: theorem::Reduction,

    game_hop_items: theorem::GameHopItem,
    game_hop_item_lists: theorem::GameHopItemList,
    game_hopss: theorem::GameHops,

    theorem_items: theorem::TheoremItem,
    theorem_item_lists: theorem::TheoremItemList,
    theorems: theorem::Theorem,

    commas: list::Comma,
    semicolons: list::Semicolon,
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
