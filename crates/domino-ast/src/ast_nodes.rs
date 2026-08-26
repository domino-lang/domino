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
    source::SourceLocation,
    State,
};

pub trait NodeType: Sized {
    const NODE_TYPE: NodeTypeEnum;
    fn global_ref_id(r: Ref<Self>) -> GlobalRefId;
}

pub trait InArena: Sized {
    fn arena(arenas: &Arenas) -> &crate::arena::Arena<Self>;
    fn arena_mut(arenas: &mut Arenas) -> &mut crate::arena::Arena<Self>;
}

impl<T: NodeType> Ref<T> {
    pub fn global_ref_id(self) -> GlobalRefId {
        NodeType::global_ref_id(self)
    }
}

impl<T: NodeType + InArena> Ref<T> {
    pub fn from_parsed(state: &mut State, loc: SourceLocation, node: T) -> Self {
        let arena = T::arena_mut(&mut state.arenas);
        let id = arena.alloc(node);

        state.tables.locations.insert(id.global_ref_id(), loc);

        id
    }
}

pub trait RefHandler<O> {
    fn handle<T: NodeType>(self, r: Ref<T>) -> O;
}

impl GlobalRefId {
    pub fn with<O, H: RefHandler<O>>(self, h: H) -> O {
        with_global_ref_id!(self, |r| { h.handle(r) })
    }
}

#[derive(Debug, Clone, Copy)]
pub struct File<T> {
    pub leading_trivia: Ref<Trivia>,
    pub main: Ref<T>,
    pub trailing_trivia: Ref<Trivia>,
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

macro_rules! define_arenas {
    ($($name:ident: $ty:path),* $(,)?) => {
        #[derive(Default, Debug)]
        pub struct Arenas {
            $(pub $name : crate::arena::Arena<$ty>),*
        }

        $(
            impl crate::ast_nodes::InArena for $ty {
                fn arena(arenas: &$crate::Arenas) -> &$crate::arena::Arena<Self> {
                    &arenas.$name
                }

                fn arena_mut(arenas: &mut $crate::Arenas) -> &mut $crate::arena::Arena<Self> {
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
        fn $fn_name(
            &mut self,
            arenas: &$crate::Arenas,
            node: $crate::arena::Ref<$node_type>
        ) {
            $crate::walk::walk(self, arenas, node)
        }
      )*
    }

    pub trait Visit: Sized {
      fn visit<V: Visitor + ?Sized>(
        visitor: &mut V,
        arenas: &$crate::Arenas,
        node: $crate::arena::Ref<Self>
      );
    }

    $(
      impl Visit for $node_type {
        fn visit<V: Visitor + ?Sized>(
            visitor: &mut V,
            arenas: &$crate::Arenas,
            node: $crate::arena::Ref<Self>
        ){
            visitor.$fn_name(arenas, node)
        }
      }
    )*
  }
}

macro_rules! define_node_type_enum {
    ($($variant_name:ident : $node_type:ty),* $(,)?) => {
        #[repr(u8)]
        #[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
        pub enum NodeTypeEnum {
            $($variant_name),*
        }

        #[derive(Clone, Copy, Debug,Eq,PartialEq,Hash)]
        pub enum GlobalRefId {
            $($variant_name(Ref<$node_type>)),*
        }

        #[macro_export]
        macro_rules! with_global_ref_id {
            ($global_ref_id:expr, |$id:ident| $code:block ) => {
                match $global_ref_id {
                    $($crate::GlobalRefId::$variant_name($id) => $code),*
                }
            };
        }


        $(
            impl NodeType for $node_type {
                const NODE_TYPE: NodeTypeEnum = NodeTypeEnum::$variant_name;
                fn global_ref_id(r: Ref<$node_type>) -> GlobalRefId {
                    GlobalRefId::$variant_name(r)
                }
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
    PackageFile { package_file: File<package::Package> }
    GameFile { game_file: File<game::Game> }
    TheoremFile { theorem_file: File<theorem::Theorem> }

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

    OracleImportSignature { oracle_import_sig: oracles::OracleSignature<identifier::OracleImportIdentifierKind> }
    OracleDefinitionSignature { oracle_def_sig: oracles::OracleSignature<identifier::OracleDefinitionIdentifierKind> }
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

    OracleImportIdentifier { oracle_import_ident: identifier::OracleImportIdentifier }
    OracleDefinitionIdentifier { oracle_def_ident: identifier::OracleDefinitionIdentifier }
    OracleComposeIdentifier { oracle_compose_ident: identifier::OracleCompositionIdentifier }
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

    ComposeOracleItem { compose_oracle_item: game::ComposeOracleAssignmentItem }
    ComposeOracleItemList { compose_oracle_item_list: game::ComposeOracleAssignmentList }

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

use with_global_ref_id;
