use crate::ast_nodes::{
    game, identifier, list, oracles, package, statements, theorem, types, NodeTypeEnum, Trivia,
    Trivium,
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


    oracle_expression_arglist: oracles::ExprList,
    statement_lists: statements::StatementList,
    pattern_lists: statements::PatternList,
    arg_decl_lists: oracles::OracleValueDeclList,

    pkg_types: types::Type<types::PackageTypeKind>,
    pkg_tuple_types:types::TupleType<types::PackageTypeKind>,
    pkg_fn_types:types::FnType<types::PackageTypeKind>,
    pkg_appl_types: types::ArgumentedType<types::PackageTypeKind>,
    pkg_type_args:types::TypeArgument<types::PackageTypeKind>,
    pkg_type_lists: types::TypeList<types::PackageTypeKind>,
    pkg_type_arg_lists: types::TypeArgList<types::PackageTypeKind>,

    game_types: types::Type<types::GameTypeKind>,
    game_tuple_types:types::TupleType<types::GameTypeKind>,
    game_fn_types:types::FnType<types::GameTypeKind>,
    game_appl_types: types::ArgumentedType<types::GameTypeKind>,
    game_type_args:types::TypeArgument<types::GameTypeKind>,
    game_type_lists: types::TypeList<types::GameTypeKind>,
    game_type_arg_lists: types::TypeArgList<types::GameTypeKind>,

    theorem_types: types::Type<types::TheoremTypeKind>,
    theorem_tuple_types:types::TupleType<types::TheoremTypeKind>,
    theorem_fn_types:types::FnType<types::TheoremTypeKind>,
    theorem_appl_types: types::ArgumentedType<types::TheoremTypeKind>,
    theorem_type_args:types::TypeArgument<types::TheoremTypeKind>,
    theorem_type_lists: types::TypeList<types::TheoremTypeKind>,
    theorem_type_arg_lists: types::TypeArgList<types::TheoremTypeKind>,


    // pure/const expressions in oracles. can only reference package const.
    // used mostly in types, e.g. Bits(n)
    pure_expressions_package: package::Expression,
    pure_expressions_package_table_index: package::TableIndexExpression,
    pure_expressions_package_tuple: package::TupleExpression,
    pure_expressions_package_paren: package::ParenExpression,
    pure_expressions_package_binop: package::BinOpExpression,
    pure_expressions_package_unop: package::UnOpExpression,
    pure_expressions_package_call: package::CallExpression,
    pure_expressions_package_list: package::ExprList,
    pure_expressions_package_invoke: package::OracleInvocationExpression,
    pure_expressions_package_sample: package::SampleExpression,

    pure_expressions_game: game::Expression,
    pure_expressions_game_table_index: game::TableIndexExpression,
    pure_expressions_game_tuple: game::TupleExpression,
    pure_expressions_game_paren: game::ParenExpression,
    pure_expressions_game_binop: game::BinOpExpression,
    pure_expressions_game_unop: game::UnOpExpression,
    pure_expressions_game_call: game::CallExpression,
    pure_expressions_game_list: game::ExprList,
    pure_expressions_game_invoke: game::OracleInvocationExpression,
    pure_expressions_game_sample: game::SampleExpression,

    pure_expressions_theorem: theorem::Expression,
    pure_expressions_theorem_table_index: theorem::TableIndexExpression,
    pure_expressions_theorem_tuple: theorem::TupleExpression,
    pure_expressions_theorem_paren: theorem::ParenExpression,
    pure_expressions_theorem_binop: theorem::BinOpExpression,
    pure_expressions_theorem_unop: theorem::UnOpExpression,
    pure_expressions_theorem_call: theorem::CallExpression,
    pure_expressions_theorem_list: theorem::ExprList,
    pure_expressions_theorem_invoke: theorem::OracleInvocationExpression,
    pure_expressions_theorem_sample: theorem::SampleExpression,

    // expressions in oracles that can have side-effects
    oracle_expressions: oracles::OracleExpression,
    oracle_binop_expressions: oracles::BinOpExpression,
    oracle_unop_expressions: oracles::UnOpExpression,
    oracle_invocation_expressions: oracles::OracleInvocationExpression,
    oracle_table_index_expressions: oracles::TableIndexExpression,
    oracle_sample_expressions: oracles::SampleExpression,
    oracle_paren_expressions: oracles::ParenExpression,
    oracle_tuple_expressions: oracles::TupleExpression,
    oracle_call_expressions: oracles::CallExpression,

    statements: statements::Statement,
    assign_statements: statements::AssignStatement,
    assert_statements: statements::AssertStatement,
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
