pub mod common;
pub mod expressions;
pub mod game;
pub mod identifier;
pub mod instances;
pub mod list;
pub mod oracles;
pub mod package;
pub mod params;
pub mod statements;
pub mod theorem;
pub mod types;

use crate::{
    arena::{Ref, Slice},
    source::{FileId, SourceLocation},
    util::trimmed_loc,
    Rule, State,
};

pub trait ListItem {
    const LIST_RULE: Rule;
}

pub trait NodeType {
    const NODE_TYPE: NodeTypeEnum;
}

pub trait InArena: Sized {
    fn arena(arenas: &Arenas) -> &crate::arena::Arena<Self>;
    fn arena_mut(arenas: &mut Arenas) -> &mut crate::arena::Arena<Self>;
}

pub trait Indexable: Sized {
    #[allow(unused_variables)]
    fn index(reference: Ref<Self>, state: &mut State) {}
}

pub trait Parsable: NodeType + InArena + Indexable {
    const RULE: Rule;

    fn parse_inner(file_id: FileId, state: &mut State, pair: crate::Pair) -> Self;

    fn parse(file_id: FileId, state: &mut State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Self::RULE);

        Self::parse_inner(file_id, state, pair)
    }

    fn parse_ref(file_id: FileId, state: &mut State, pair: crate::Pair) -> Ref<Self> {
        // NOTE: We need to trim trailing whitespace from the span here.
        let loc = trimmed_loc(file_id, &pair);

        let node = Self::parse(file_id, state, pair);

        Ref::<Self>::from_parsed(state, loc, node)
    }
}

pub trait ParsableArenaNode: Parsable + InArena + Indexable {}

impl<T: NodeType + InArena + Indexable> Ref<T> {
    pub fn from_parsed(state: &mut State, loc: SourceLocation, node: T) -> Self {
        let arena = T::arena_mut(&mut state.arenas);
        let id = arena.alloc(node);

        state.tables.locations.insert(id.global_ref_id(), loc);
        T::index(id, state);

        id
    }
}

impl<T: Parsable> Slice<T> {
    pub fn from_iter<'src>(
        file_id: FileId,
        state: &mut State,
        iter: impl IntoIterator<Item = crate::Pair<'src>>,
    ) -> Self {
        let parsed: Vec<(T, _)> = iter
            .into_iter()
            .map(|pair: crate::Pair| {
                let loc = SourceLocation::from_file_and_pair(file_id, &pair);
                let node = T::parse(file_id, state, pair);
                (node, loc)
            })
            .collect();

        Self::from_parsed(state, parsed)
    }

    pub fn from_parsed(
        state: &mut State,
        parsed: impl IntoIterator<Item = (T, SourceLocation)>,
    ) -> Self {
        let mut allocator = T::arena_mut(&mut state.arenas).slice_allocator();
        let allocated: Vec<(Ref<T>, _)> = parsed
            .into_iter()
            .map(|(node, loc)| {
                let id = allocator.push(node);
                (id, loc)
            })
            .collect();

        let slice = allocator.finish();

        for (id, loc) in allocated {
            state.tables.locations.insert(id.global_ref_id(), loc);
            T::index(id, state);
        }

        slice
    }
}

#[derive(Debug, Clone, Copy)]
pub enum Trivium {
    BlockComment,
    LineComment,
    NewLine,
}

#[derive(Debug, Clone, Copy)]
pub struct Trivia {
    pub trivia: Slice<Trivium>,
}

impl Parsable for Trivium {
    const RULE: Rule = Rule::trivium;

    fn parse_inner(_file_id: FileId, _state: &mut State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::trivium);

        match pair.into_inner().next().unwrap().as_rule() {
            Rule::newline => Trivium::NewLine,
            Rule::block_comment => Trivium::BlockComment,
            Rule::line_comment => Trivium::LineComment,
            _ => unreachable!(),
        }
    }
}

impl Parsable for Trivia {
    const RULE: Rule = Rule::gap;

    fn parse_inner(file_id: FileId, state: &mut State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::gap);

        let mut trivia = vec![];
        trivia.extend(
            pair.into_inner()
                .map(|trivium_pair| Trivium::parse(file_id, state, trivium_pair)),
        );

        let mut allocator = state.arenas.trivium.slice_allocator();
        allocator.extend(trivia);

        Self {
            trivia: allocator.finish(),
        }
    }
}

macro_rules! define_arenas {
    ($($name:ident: $ty:path),* $(,)?) => {
        #[derive(Default, Debug)]
        pub struct Arenas {
            $(pub $name : crate::arena::Arena<$ty>),*
        }

        $(
            impl crate::ast_nodes::InArena for $ty {
                fn arena(arenas: &crate::Arenas) -> &crate::arena::Arena<Self> {
                    &arenas.$name
                }

                fn arena_mut(arenas: &mut crate::Arenas) -> &mut crate::arena::Arena<Self> {
                    &mut arenas.$name
                }
            }
        )*
    };
}

macro_rules! define_visitor_trait {
  ($( fn $fn_name:ident( ... , node: $node_type:ty) );*) => {
    /// A helper trait for browsing the AST.
    ///
    /// Methods have the form `fn {ast_node_field_name}(&mut self, arenas: &Arenas, node: Ref<{ast_node_ty}>)`.
    pub trait Visitor {
      $(
        #[allow(unused_variables)]
        fn $fn_name(&mut self, arenas: &$crate::Arenas, node: $crate::arena::Ref<$node_type>) {}
      )*
    }
  }
}

macro_rules! define_node_type_enum {
    ($($variant_name:ident : $node_type:ty),* $(,)?) => {
        #[repr(u8)]
        #[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
        pub enum NodeTypeEnum {
            $($variant_name),*
        }

        $(
            impl NodeType for $node_type {
                const NODE_TYPE: NodeTypeEnum = NodeTypeEnum::$variant_name;
            }
        )*
    }
}

macro_rules! define_node_types {
    (  $( $variant_name:ident { $field_name:ident : $node_type:ty } )* ) => {
        define_node_type_enum! {
          $(
            $variant_name: $node_type,
          )*
        }


        define_arenas! {
          // We need an arena for the sources, but they are not AST nodes
          source: crate::source::SourceFile,

          $(
            $field_name: $node_type,
          )*
        }

        define_visitor_trait! {
          $( fn $field_name( ... , node: $node_type) );*
        }
    };
}

define_node_types! {
    Trivium { trivium: Trivium }
    Trivia { trivia: Trivia }

    // Delimiters

    Comma { comma: list::Comma }
    Semicolon { semicolon: list::Semicolon }
    Colon { colon: list::Colon }

    // Types
    //
    // ## In Packages
    PackageType { package_type: types::Type<types::PackageTypeKind> }
    PackageTupleType { package_type_tuple: types::TupleType<types::PackageTypeKind> }
    PackageFnType { package_type_fn: types::FnType<types::PackageTypeKind> }
    PackageApplicationType { package_type_app: types::ArgumentedType<types::PackageTypeKind> }
    PackageTypeArg { package_type_arg: types::TypeArgument<types::PackageTypeKind> }
    PackageTypeArgList { package_type_applist: types::TypeArgList<types::PackageTypeKind> }
    PackageTypeList { package_type_list: types::TypeList<types::PackageTypeKind> }

    // ## In Games
    GameType { game_type: types::Type<types::GameTypeKind> }
    GameTupleType { game_type_tuple: types::TupleType<types::GameTypeKind> }
    GameFnType { game_type_fn: types::FnType<types::GameTypeKind> }
    GameApplicationType { game_type_app: types::ArgumentedType<types::GameTypeKind> }
    GameTypeArg { game_type_arg: types::TypeArgument<types::GameTypeKind> }
    GameTypeArgList { game_type_applist: types::TypeArgList<types::GameTypeKind> }
    GameTypeList { game_type_list: types::TypeList<types::GameTypeKind> }

    // ## In Theorems
    TheoremType { theorem_type: types::Type<types::TheoremTypeKind> }
    TheoremTupleType { theorem_type_tuple: types::TupleType<types::TheoremTypeKind> }
    TheoremFnType { theorem_type_fn: types::FnType<types::TheoremTypeKind> }
    TheoremApplicationType { theorem_type_app: types::ArgumentedType<types::TheoremTypeKind> }
    TheoremTypeArg { theorem_type_arg: types::TypeArgument<types::TheoremTypeKind> }
    TheoremTypeArgList { theorem_type_applist: types::TypeArgList<types::TheoremTypeKind> }
    TheoremTypeList { theorem_type_list: types::TypeList<types::TheoremTypeKind> }

    // Expressions
    //
    // ## In Packages
    PurePackageConstValueExpression { pkg_expr: package::Expression }
    PurePackageConstValueTableIndexExpression { pkg_expr_tableidx: package::TableIndexExpression }
    PurePackageConstValueTupleExpression { pkg_expr_tuple: package::TupleExpression }
    PurePackageConstValueParenExpression { pkg_expr_paren: package::ParenExpression }
    PurePackageConstValueBinOnExpression { pkg_expr_binop: package::BinOpExpression }
    PurePackageConstValueUnOnExpression { pkg_expr_unop: package::UnOpExpression }
    PurePackageConstValueCallExpression { pkg_expr_call: package::CallExpression }
    PurePackageConstValueOracleInvocationExpression { pkg_expr_invoc: package::OracleInvocationExpression }
    PurePackageConstValueSampleExpression { pkg_expr_sample: package::SampleExpression }
    PurePackageConstPackageExpressionList { pkg_expr_list: package::ExprList }

    // ## In Games
    PureGameConstValueExpression { game_expr: game::Expression }
    PureGameConstValueTableIndexExpression { game_expr_tableidx: game::TableIndexExpression }
    PureGameConstValueTupleExpression { game_expr_tuple: game::TupleExpression }
    PureGameConstValueParenExpression { game_expr_paren: game::ParenExpression }
    PureGameConstValueBinOnExpression { game_expr_binop: game::BinOpExpression }
    PureGameConstValueUnOnExpression { game_expr_unop: game::UnOpExpression }
    PureGameConstValueCallExpression { game_expr_call: game::CallExpression }
    PureGameConstValueOracleInvocationExpression { game_expr_invoc: game::OracleInvocationExpression }
    PureGameConstValueSampleExpression { game_expr_sample: game::SampleExpression }
    PureGameConstPackageExpressionList {game_expr_list: game::ExprList}

    // ## In Theorems
    PureTheoremConstValueExpression { thm_expr: theorem::Expression }
    PureTheoremConstValueTableIndexExpression { thm_expr_tableidx: theorem::TableIndexExpression }
    PureTheoremConstValueTupleExpression { thm_expr_tuple: theorem::TupleExpression }
    PureTheoremConstValueParenExpression { thm_expr_paren: theorem::ParenExpression }
    PureTheoremConstValueBinOnExpression { thm_expr_binop: theorem::BinOpExpression }
    PureTheoremConstValueUnOnExpression { thm_expr_unop: theorem::UnOpExpression }
    PureTheoremConstValueCallExpression { thm_expr_call: theorem::CallExpression }
    PureTheoremConstValueOracleInvocationExpression { thm_expr_invoc: theorem::OracleInvocationExpression }
    PureTheoremConstValueSampleExpression { thm_expr_sample: theorem::SampleExpression }
    PureTheoremConstTheoremExpressionList { thm_expr_list: theorem::ExprList }

    // ## In Oracles
    OracleExpression { oracle_expr: oracles::OracleExpression }
    OracleTableIndexExpression { oracle_expr_tableidx: oracles::TableIndexExpression }
    OracleTupleExpression { oracle_expr_tuple: oracles::TupleExpression }
    OracleParenExpression { oracle_expr_paren: oracles::ParenExpression }
    OracleBinOpExpression { oracle_expr_binop: oracles::BinOpExpression }
    OracleUnOpExpression { oracle_expr_unop: oracles::UnOpExpression }
    OracleCallExpression { oracle_expr_call: oracles::CallExpression }
    OracleInvocationExpression { oracle_expr_invoc: oracles::OracleInvocationExpression }
    OracleSampleExpression { oracle_expr_sample: oracles::SampleExpression }
    OracleExprList { oracle_expr_list: oracles::ExprList }

    // Statements and Patterns
    Statement { stmt: statements::Statement }
    AssignStatement { stmt_assign: statements::AssignStatement }
    AssertStatement { stmt_assert: statements::AssertStatement }
    IfThenElseStatement { stmt_ite: statements::IfThenElseStatement }
    ReturnStatement { stmt_ret: statements::ReturnStatement }
    ExpressionStatement { stmt_expr: statements::ExpressionStatement }
    StatementList { stmt_list: statements::StatementList }
    Pattern { pat: statements::Pattern }
    TablePattern { pat_table: statements::TablePattern }
    TuplePattern { pat_tuple: statements::TuplePattern }
    PatternList { pat_list: statements::PatternList }

    OracleSignature { oracle_sig: oracles::OracleSignature }
    OracleValueDeclList { oracle_value_decl_list: oracles::OracleValueDeclList }
    OracleValueArgDecl { oracle_value_arg_decl: oracles::OracleValueArgDecl }
    OracleDefinition { oracle_def: oracles::OracleDefinition }

    OracleDeclList { oracle_decl_list: package::OracleDeclList }
    ImportOraclesBlock { import_oracle_block: package::ImportOraclesBlock }
    StateBlock { state_block: package::StateBlock }

    PackageConstDecl { pkg_const_decl: package::PackageConstDecl }
    PackageConstDeclList { pkg_const_decl_list: package::PackageConstDeclList }
    PackageConstParamBlock { pkg_const_param_block: package::PackageConstParamBlock }

    PackageTypeDeclList { pkg_type_decl_list: package::PackageTypeDeclList }
    PackageTypeParamBlock { pkg_type_param_block: package::PackageTypeParamBlock }
    PackageItem { pkg_item: package::PackageItem }
    PackageItemList { pkg_item_list: package::PackageItemList }
    Package { package: package::Package }

    PackageTypeIdentifier { pkg_type_ident: identifier::PackageTypeIdentifier }
    GameTypeIdentifier { game_type_ident: identifier::GameTypeIdentifier }
    TheoremTypeIdentifier { thm_type_ident: identifier::TheoremTypeIdentifier }

    PackageTypeArgumentIdentifier { pkg_type_arg_ident: identifier::PackageTypeArgumentIdentifier }
    GameTypeArgumentIdentifier { game_type_arg_ident: identifier::GameTypeArgumentIdentifier }
    TheoremTypeArgumentIdentifier { thm_type_arg_ident: identifier::TheoremTypeArgumentIdentifier }

    OracleIdentifier { oracle_ident: identifier::OracleIdentifier }
    PackageIdentifier { pkg_ident: identifier::PackageIdentifier }
    GameIdentifier { game_ident: identifier::GameIdentifier }
    PackageInstanceIdentifier { pkg_inst_ident: identifier::PackageInstanceIdentifier }
    GameInstanceIdentifier { game_inst_ident: identifier::GameInstanceIdentifier }

    OracleValueIdentifier { oracle_value_ident: identifier::OracleValueIdentifier }
    PackageConstValueIdentifier { pkg_const_value_ident: identifier::PackageConstValueIdentifier }
    GameConstValueIdentifier { game_const_value_ident: identifier::GameConstValueIdentifier }
    TheoremConstValueIdentifier { thm_const_value_ident: identifier::TheoremConstValueIdentifier }

    AssumptionIdentifier { assumption_ident: identifier::AssumptionIdentifier }
    LemmaIdentifier { lemma_ident: identifier::LemmaIdentifier }
    TheoremIdentifier { thm_ident: identifier::TheoremIdentifier }

    GameInstanceConstItem { game_inst_const_item: game::InstanceConstAssignmentItem }
    GameInstanceConstItemList { game_inst_const_item_list: game::InstanceConstAssignmentList }
    GameInstanceConstBlock { game_inst_const_block: game::InstanceConstBlock }

    GameInstanceTypeItem { game_inst_type_item: game::InstanceTypeAssignmentItem }
    GameInstanceTypeItemList { game_inst_type_item_list: game::InstanceTypeAssignmentList }
    GameInstanceTypeBlock { game_inst_type_block: game::InstanceTypeBlock }

    GameInstanceItem { game_inst_item: game::InstanceItem }
    GameInstanceItemList { game_inst_item_list: game::InstanceItemList }
    GameInstanceBlock { game_inst_block: game::InstanceBlock }

    ComposeOracleItem { componse_oracle_item: game::ComposeOracleAssignmentItem }
    ComposeOracleItemList { componse_oracle_item_list: game::ComposeOracleAssignmentList }

    ComposePackageInstanceItem { compose_pkg_inst_item: game::ComposePackageInstanceItem }
    ComposePackageInstanceItemList { compose_pkg_inst_item_list: game::ComposePackageInstanceList }

    ComposeBlock { compose_block: game::ComposeBlock }

    GameConstDecl { game_const_decl: game::GameConstDecl }
    GameConstDeclList { game_const_decl_list: game::GameConstDeclList }
    GameConstParamBlock { game_const_param_block: game::GameConstParamBlock }

    GameTypeDeclList { game_type_decl_list: game::GameTypeDeclList }
    GameTypeParamBlock { game_type_param_block: game::GameTypeParamBlock }

    GameItem { game_item: game::GameItem }
    GameItemList { game_item_list: game::GameItemList }
    Game { game: game::Game }

    // theorems

    //// instances

    TheoremInstanceConstItem { thm_inst_const_item: theorem::InstanceConstAssignmentItem }
    TheoremInstanceConstItemList { thm_inst_const_item_list: theorem::InstanceConstAssignmentList }
    TheoremInstanceConstBlock { thm_inst_const_block: theorem::InstanceConstBlock }

    TheoremInstanceTypeItem { thm_inst_type_item: theorem::InstanceTypeAssignmentItem }
    TheoremInstanceTypeItemList { thm_inst_type_item_list: theorem::InstanceTypeAssignmentList }
    TheoremInstanceTypeBlock { thm_inst_type_block: theorem::InstanceTypeBlock }

    TheoremInstanceItem { thm_inst_item: theorem::InstanceItem }
    TheoremInstanceItemList { thm_inst_item_list: theorem::InstanceItemList }
    TheoremInstanceBlock { thm_inst_block: theorem::InstanceBlock }

    //// hybrid instances

    // HybridInstanceBlockOne: theorem::HybridInstanceBlockOne,
    // HybridInstanceBlockTwo: theorem::HybridInstanceBlockTwo,
    // HybridInstanceBlock: theorem::HybridInstanceBlock,

    TheoremConstDecl { thm_const_decl: theorem::TheoremConstDecl }
    TheoremConstDeclList { thm_const_decl_list: theorem::TheoremConstDeclList }
    TheoremConstParamBlock { thm_const_param_block: theorem::TheoremConstParamBlock }

    Path { path: theorem::Path }
    PathList { path_list: theorem::PathList }
    InvariantSpec { invnt_spec: theorem::InvariantSpec }

    SmtIdentifier { smt_ident: theorem::SmtIdentifier }
    SmtIdentifierList { smt_ident_list: theorem::SmtIdentifierList }
    LemmaItem { lemma_item: theorem::LemmaItem }
    LemmaItemList { lemma_item_list: theorem::LemmaItemList }
    LemmaBlock { lemma_block: theorem::LemmaBlock }
    EquivalenceOracleItem { eqv_oracle_item: theorem::EquivalenceOracleItem }
    EquivalenceOracleItemList { eqv_oracle_item_list: theorem::EquivalenceOracleItemList }
    EquivalenceOracleBlock { eqv_oracle_block: theorem::EquivalenceOracleBlock }
    EquivalenceOracleBlockList { eqv_oracle_block_list: theorem::EquivalenceOracleBlockList }
    Equivalence { eqv: theorem::Equivalence }

    Bound { bound: theorem::Bound }
    AssumptionsItem { assumption_item: theorem::AssumptionsItem }
    AssumptionsItemList { assumption_item_list: theorem::AssumptionsItemList }
    AssumptionsBlock { assumption_block: theorem::AssumptionsBlock }

    Conjecture { conjecture: theorem::Conjecture }

    ReductionAssumptionLine { red_assumption_line: theorem::ReductionAssumptionLine }
    ReductionMapItem { red_map_item: theorem::ReductionMapItem }
    ReductionMapItemList { red_map_item_list: theorem::ReductionMapItemList }
    ReductionMap { red_map: theorem::ReductionMap }
    ReductionItem { red_item: theorem::ReductionItem }
    ReductionItemList { red_item_list: theorem::ReductionItemList }
    Reduction { red: theorem::Reduction }

    GameHopItem { gamehop_item: theorem::GameHopItem }
    GameHopItemList { gamehop_item_list: theorem::GameHopItemList }
    GameHops { gamehops: theorem::GameHops }

    TheoremItem { thm_item: theorem::TheoremItem }
    TheoremItemList { thm_item_list: theorem::TheoremItemList }
    Theorem { thm: theorem::Theorem }
}

pub fn parse_ref<T: Parsable>(
    file_id: crate::source::FileId,
    state: &mut crate::State,
    pair: crate::Pair,
    f: fn(crate::source::FileId, &mut crate::State, crate::Pair) -> T,
) -> Ref<T> {
    // NOTE: We need to trim trailing whitespace from the span here.
    let loc = trimmed_loc(file_id, &pair);
    let node = f(file_id, state, pair);
    Ref::<T>::from_parsed(state, loc, node)
}

macro_rules! impl_noop_index {
    ($($node_type:ty),* $(,)?) => {
        $(
            impl Indexable for $node_type {}
        )*

    };
}

impl_noop_index! {
    Trivium,
    Trivia,

    // pure expressions

    //// package const
    package::Expression,
    package::TupleExpression,
    package::TableIndexExpression,
    package::ParenExpression,
    package::BinOpExpression,
    package::UnOpExpression,
    package::CallExpression,
    package::OracleInvocationExpression,
    package::SampleExpression,

    //// game const
    game::Expression,
    game::TupleExpression,
    game::TableIndexExpression,
    game::ParenExpression,
    game::BinOpExpression,
    game::UnOpExpression,
    game::CallExpression,
    game::OracleInvocationExpression,
    game::SampleExpression,

    //// theorem const
    theorem::Expression,
    theorem::TupleExpression,
    theorem::TableIndexExpression,
    theorem::ParenExpression,
    theorem::BinOpExpression,
    theorem::UnOpExpression,
    theorem::CallExpression,
    theorem::OracleInvocationExpression,
    theorem::SampleExpression,

    // types
    //// in packages
    types::Type<types::PackageTypeKind>,
    types::TupleType<types::PackageTypeKind>,
    types::FnType<types::PackageTypeKind>,
    types::ArgumentedType<types::PackageTypeKind>,
    types::TypeArgument<types::PackageTypeKind>,


    //// in games
    types::Type<types::GameTypeKind>,
    types::TupleType<types::GameTypeKind>,
    types::FnType<types::GameTypeKind>,
    types::ArgumentedType<types::GameTypeKind>,
    types::TypeArgument<types::GameTypeKind>,

    //// in theorems
    types::Type<types::TheoremTypeKind>,
    types::TupleType<types::TheoremTypeKind>,
    types::FnType<types::TheoremTypeKind>,
    types::ArgumentedType<types::TheoremTypeKind>,
    types::TypeArgument<types::TheoremTypeKind>,

    // oracle expressions
    oracles::OracleExpression,
    oracles::TableIndexExpression,
    oracles::TupleExpression,
    oracles::ParenExpression,
    oracles::BinOpExpression,
    oracles::UnOpExpression,
    oracles::CallExpression,
    oracles::OracleInvocationExpression,
    oracles::SampleExpression,

    // statemnts
    statements::Statement,
    statements::AssertStatement,
    statements::AssignStatement,
    statements::IfThenElseStatement,
    statements::ReturnStatement,
    statements::ExpressionStatement,
    statements::Pattern,
    statements::TablePattern,
    statements::TuplePattern,

    // oracles
    oracles::OracleSignature,
    oracles::OracleValueArgDecl,
    oracles::OracleDefinition,

    // packages
    package::PackageConstDecl,
    package::PackageConstParamBlock,

    package::ImportOraclesBlock,
    package::StateBlock,
    package::PackageTypeParamBlock,
    package::PackageItem,
    package::Package,
    // games
    game::InstanceConstAssignmentItem,
    game::InstanceConstBlock,
    game::InstanceTypeAssignmentItem,
    game::InstanceTypeBlock,
    game::InstanceItem,
    game::InstanceBlock,
    game::ComposeOracleAssignmentItem,
    game::ComposePackageInstanceItem,
    game::ComposeBlock,
    game::GameConstDecl,
    game::GameConstParamBlock,

    game::GameTypeParamBlock,

    game::GameItem,
    game::Game,

    // theorems
    //// instances
    theorem::InstanceConstAssignmentItem,
    theorem::InstanceConstBlock,

    theorem::InstanceTypeAssignmentItem,
    theorem::InstanceTypeBlock,

    theorem::InstanceItem,

    theorem::InstanceBlock,

    //// hybrid instances
    // theorem::HybridInstanceBlockOne,
    // theorem::HybridInstanceBlockTwo,
    // theorem::HybridInstanceBlock,

    theorem::TheoremConstDecl,
    theorem::TheoremConstParamBlock,

    theorem::Path,
    theorem::InvariantSpec,

    theorem::SmtIdentifier,
    theorem::LemmaItem,
    theorem::LemmaBlock,
    theorem::EquivalenceOracleItem,
    theorem::EquivalenceOracleBlock,
    theorem::Equivalence,

    theorem::Bound,
    theorem::AssumptionsItem,
    theorem::AssumptionsBlock,

    theorem::Conjecture,

    theorem::ReductionAssumptionLine,
    theorem::ReductionMapItem,
    theorem::ReductionMap,
    theorem::ReductionItem,
    theorem::Reduction,

    theorem::GameHopItem,
    theorem::GameHops,

    theorem::TheoremItem,
    theorem::Theorem,

    // lists
    list::Colon,
    list::Comma,
    list::Semicolon,
}
