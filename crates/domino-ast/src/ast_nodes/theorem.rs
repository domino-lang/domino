use crate::{
    arena::Ref,
    ast_nodes::{
        common,
        identifier::{
            AssumptionIdentifier, GameConstValueIdentifierKind, GameInstanceIdentifier,
            GameInstanceIdentifierKind, GameTypeIdentifierKind, LemmaIdentifier, OracleIdentifier,
            PackageInstanceIdentifier, TheoremConstValueIdentifierKind, TheoremIdentifier,
            TheoremTypeIdentifierKind,
        },
        instances,
        list::{Comma, List, ListNoDelim},
        params, ListItem, Parsable, Trivia,
    },
    Rule,
};

pub type TheoremConstDecl = common::ValueDecl<TheoremConstValueIdentifierKind>;
pub type TheoremConstDeclList = common::ConstDeclList<TheoremConstValueIdentifierKind>;
pub type TheoremConstParamBlock = params::ConstParamBlock<TheoremConstValueIdentifierKind>;

pub type InstanceConstAssignmentItem = instances::InstanceConstAssignmentItem<
    GameConstValueIdentifierKind,
    TheoremConstValueIdentifierKind,
>;

impl ListItem for InstanceConstAssignmentItem {
    const LIST_RULE: Rule = Rule::inst_const_assignment_list;
}

pub type InstanceConstAssignmentList = instances::InstanceConstAssignmentList<
    GameConstValueIdentifierKind,
    TheoremConstValueIdentifierKind,
>;
pub type InstanceConstBlock =
    instances::InstanceConstBlock<GameConstValueIdentifierKind, TheoremConstValueIdentifierKind>;
pub type InstanceTypeAssignmentItem =
    instances::InstanceTypeAssignmentItem<GameTypeIdentifierKind, TheoremTypeIdentifierKind>;

impl ListItem for InstanceTypeAssignmentItem {
    const LIST_RULE: Rule = Rule::inst_type_assignment_list;
}

pub type InstanceTypeAssignmentList =
    instances::InstanceTypeAssignmentList<GameTypeIdentifierKind, TheoremTypeIdentifierKind>;
pub type InstanceTypeBlock =
    instances::InstanceTypeBlock<GameTypeIdentifierKind, TheoremTypeIdentifierKind>;
pub type InstanceItem = instances::InstanceItem<GameInstanceIdentifierKind>;

impl ListItem for InstanceItem {
    const LIST_RULE: Rule = Rule::inst_list;
}

pub type InstanceItemList = instances::InstanceItemList<GameInstanceIdentifierKind>;
pub type InstanceBlock = instances::InstanceBlock<GameInstanceIdentifierKind>;

// hybrid instances

// #[derive(Debug, Copy, Clone)]
// pub struct HybridInstanceBlockOne {
//     pub pre_instance_trivia: Ref<Trivia>,
//     pub left_trivia: Ref<Trivia>,
//     pub left: Ref<GameIdentifier>,
//     pub right_trivia: Ref<Trivia>,
//     pub right: Ref<GameIdentifier>,
//     pub bit_trivia: Ref<Trivia>,
//     pub bit: Ref<GameIdentifier>,
//     pub eq_trivia: Ref<Trivia>,
//     pub game_trivia: Ref<Trivia>,
//     pub inst_items: Ref<InstanceItemList>,
// }
//
// #[derive(Debug, Copy, Clone)]
// pub struct HybridInstanceBlockTwo {
//     pub pre_instance_trivia: Ref<Trivia>,
//     pub left_trivia: Ref<Trivia>,
//     pub right_trivia: Ref<Trivia>,
//     pub eq_trivia: Ref<Trivia>,
//     pub outer_brace_trivia: Ref<Trivia>,
//     pub left_game_trivia: Ref<Trivia>,
//     pub left_brace_trivia: Ref<Trivia>,
//     pub letft_inst_items: Ref<InstanceItemList>,
//     pub right_game_trivia: Ref<Trivia>,
//     pub right_brace_trivia: Ref<Trivia>,
//     pub right_inst_items: Ref<InstanceItemList>,
// }
//
// #[derive(Debug, Copy, Clone)]
// pub enum HybridInstanceBlock {
//     One(Ref<HybridInstanceBlockOne>),
//     Two(Ref<HybridInstanceBlockTwo>),
// }

// paths for smt files

#[derive(Debug, Copy, Clone)]
pub struct Path;

impl ListItem for Path {
    const LIST_RULE: Rule = Rule::path_list;
}

pub type PathList = ListNoDelim<Path>;

#[derive(Debug, Copy, Clone)]
pub struct InvariantSpec {
    pub pre_colon_trivia: Ref<Trivia>,
    pub pre_open_trivia: Ref<Trivia>,
    pub paths: Ref<PathList>,
}

#[derive(Debug, Copy, Clone)]
pub struct SmtIdentifier;

impl ListItem for SmtIdentifier {
    const LIST_RULE: Rule = Rule::smt_identifier_list;
}

pub type SmtIdentifierList = List<SmtIdentifier, Comma>;

#[derive(Debug, Copy, Clone)]
pub struct LemmaItem {
    pub name: Ref<LemmaIdentifier>,
    pub pre_colon_trivia: Ref<Trivia>,
    pub pre_open_trivia: Ref<Trivia>,
    pub dependencies: Ref<SmtIdentifierList>,
}

impl ListItem for LemmaItem {
    const LIST_RULE: Rule = Rule::lemma_items;
}

pub type LemmaItemList = ListNoDelim<LemmaItem>;

#[derive(Debug, Copy, Clone)]
pub struct LemmaBlock {
    pub trivia: Ref<Trivia>,
    pub items: Ref<LemmaItemList>,
}

#[derive(Debug, Copy, Clone)]
pub enum EquivalenceOracleItem {
    InvariantSpec(Ref<InvariantSpec>),
    LemmaBlock(Ref<LemmaBlock>),
}

impl ListItem for EquivalenceOracleItem {
    const LIST_RULE: Rule = Rule::eqv_oracle_block_list;
}

pub type EquivalenceOracleItemList = ListNoDelim<EquivalenceOracleItem>;

#[derive(Debug, Copy, Clone)]
pub struct EquivalenceOracleBlock {
    pub name: Ref<OracleIdentifier>,
    pub pre_colon_trivia: Ref<Trivia>,
    pub pre_brace_trivia: Ref<Trivia>,
    pub items: Ref<EquivalenceOracleItemList>,
}

impl ListItem for EquivalenceOracleBlock {
    const LIST_RULE: Rule = Rule::eqv_oracle_blocks;
}

pub type EquivalenceOracleBlockList = ListNoDelim<EquivalenceOracleBlock>;

#[derive(Debug, Copy, Clone)]
pub struct Equivalence {
    pub kw_trivia: Ref<Trivia>,
    pub left_name: Ref<GameInstanceIdentifier>,
    pub left_trivia: Ref<Trivia>,
    pub right_name: Ref<GameInstanceIdentifier>,
    pub right_trivia: Ref<Trivia>,
    pub blocks: Ref<EquivalenceOracleBlockList>,
}

#[derive(Debug, Copy, Clone)]
pub struct Bound {
    pub lhs: Ref<GameInstanceIdentifier>,
    pub pre_tilde_trivia: Ref<Trivia>,
    pub post_tilde_trivia: Ref<Trivia>,
    pub rhs: Ref<GameInstanceIdentifier>,
}

#[derive(Debug, Copy, Clone)]
pub struct AssumptionsItem {
    pub name: Ref<AssumptionIdentifier>,
    pub pre_colon_trivia: Ref<Trivia>,
    pub pre_brace_trivia: Ref<Trivia>,
    pub bound: Ref<Bound>,
}

impl ListItem for AssumptionsItem {
    const LIST_RULE: Rule = Rule::assumptions_items;
}

pub type AssumptionsItemList = ListNoDelim<AssumptionsItem>;

#[derive(Debug, Copy, Clone)]
pub struct AssumptionsBlock {
    pub trivia: Ref<Trivia>,
    pub items: Ref<AssumptionsItemList>,
}

#[derive(Debug, Copy, Clone)]
pub struct Conjecture {
    pub left_trivia: Ref<Trivia>,
    pub left_name: Ref<GameInstanceIdentifier>,
    pub right_trivia: Ref<Trivia>,
    pub right_name: Ref<GameInstanceIdentifier>,
}

#[derive(Debug, Copy, Clone)]
pub struct ReductionAssumptionLine {
    pub trivia: Ref<Trivia>,
    pub name: Ref<AssumptionIdentifier>,
}

#[derive(Debug, Copy, Clone)]
pub struct ReductionMapItem {
    pub left_name: Ref<PackageInstanceIdentifier>,
    pub colon_trivia: Ref<Trivia>,
    pub right_trivia: Ref<Trivia>,
    pub right_name: Ref<PackageInstanceIdentifier>,
}

impl ListItem for ReductionMapItem {
    const LIST_RULE: Rule = Rule::red_map_items;
}

pub type ReductionMapItemList = ListNoDelim<ReductionMapItem>;

#[derive(Debug, Copy, Clone)]
pub struct ReductionMap {
    pub assumption_trivia: Ref<Trivia>,
    pub assumption_name: Ref<GameInstanceIdentifier>,
    pub construction_trivia: Ref<Trivia>,
    pub construction_name: Ref<GameInstanceIdentifier>,
    pub items_trivia: Ref<Trivia>,
    pub items: Ref<ReductionMapItemList>,
}

#[derive(Debug, Copy, Clone)]
pub enum ReductionItem {
    AssumptionLine(Ref<ReductionAssumptionLine>),
    Map(Ref<ReductionMap>),
}

impl ListItem for ReductionItem {
    const LIST_RULE: Rule = Rule::red_items;
}

pub type ReductionItemList = ListNoDelim<ReductionItem>;

#[derive(Debug, Copy, Clone)]
pub struct Reduction {
    pub left_trivia: Ref<Trivia>,
    pub left_name: Ref<GameInstanceIdentifier>,
    pub right_trivia: Ref<Trivia>,
    pub right_name: Ref<GameInstanceIdentifier>,
    pub items_trivia: Ref<Trivia>,
    pub items: Ref<ReductionItemList>,
}

#[derive(Debug, Copy, Clone)]
pub enum GameHopItem {
    Reduction(Ref<Reduction>),
    Equivalence(Ref<Equivalence>),
    Conjecture(Ref<Conjecture>),
}

impl ListItem for GameHopItem {
    const LIST_RULE: Rule = Rule::gamehop_items;
}

pub type GameHopItemList = ListNoDelim<GameHopItem>;

#[derive(Debug, Copy, Clone)]
pub struct GameHops {
    pub trivia: Ref<Trivia>,
    pub items: Ref<GameHopItemList>,
}

#[derive(Debug, Copy, Clone)]
pub enum TheoremItem {
    ConstParams(Ref<TheoremConstParamBlock>),
    GameInstance(Ref<InstanceBlock>),
    Assumptions(Ref<AssumptionsBlock>),
    GameHops(Ref<GameHops>),
    // TODO: Propositions
}

impl ListItem for TheoremItem {
    const LIST_RULE: Rule = Rule::theorem_item_list;
}

pub type TheoremItemList = ListNoDelim<TheoremItem>;

#[derive(Debug, Copy, Clone)]
pub struct Theorem {
    pub name_trivia: Ref<Trivia>,
    pub name: Ref<TheoremIdentifier>,
    pub brace_trivia: Ref<Trivia>,
    pub items: Ref<TheoremItemList>,
}

impl Parsable for InstanceConstAssignmentItem {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        super::instances::parse_instance_const_assignment_item(file_id, state, pair)
    }
}

impl Parsable for InstanceConstBlock {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::inst_const_block);

        let mut inner = pair.into_inner();

        let _kw_consts = inner.next().unwrap();
        let trivia_pair = inner.next().unwrap();
        let list_pair = inner.next().unwrap();

        let trivia = Trivia::parse_ref(file_id, state, trivia_pair);
        let list = InstanceConstAssignmentList::parse_ref(file_id, state, list_pair);

        Self { trivia, list }
    }
}

impl Parsable for InstanceTypeAssignmentItem {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        instances::parse_instance_type_assignment_item(file_id, state, pair)
    }
}

impl Parsable for InstanceTypeBlock {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::inst_type_block);

        let mut inner = pair.into_inner();

        let _kw_consts = inner.next().unwrap();
        let trivia_pair = inner.next().unwrap();
        let list_pair = inner.next().unwrap();

        let trivia = Trivia::parse_ref(file_id, state, trivia_pair);
        let list = InstanceTypeAssignmentList::parse_ref(file_id, state, list_pair);

        Self { trivia, list }
    }
}
impl Parsable for InstanceItem {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::inst_item);

        let inner = pair.into_inner().next().unwrap();

        match inner.as_rule() {
            Rule::inst_const_block => {
                InstanceItem::InstanceConst(InstanceConstBlock::parse_ref(file_id, state, inner))
            }
            Rule::inst_type_block => {
                InstanceItem::InstanceType(InstanceTypeBlock::parse_ref(file_id, state, inner))
            }
            _ => unreachable!(),
        }
    }
}

impl Parsable for InstanceBlock {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        super::instances::parse_instance_block(file_id, state, pair)
    }
}

impl Parsable for Path {
    fn parse(
        _file_id: crate::source::FileId,
        _state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::path);

        Path
    }
}

impl Parsable for InvariantSpec {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::invariant_spec);

        let mut inner = pair.into_inner();

        let _kw_pair = inner.next().unwrap();
        let pre_colon_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let pre_open_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let paths = PathList::parse_ref(file_id, state, inner.next().unwrap());

        Self {
            pre_colon_trivia,
            pre_open_trivia,
            paths,
        }
    }
}

impl Parsable for SmtIdentifier {
    fn parse(
        _file_id: crate::source::FileId,
        _state: &mut crate::State,
        pair: crate::Pair,
    ) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::smt_identifier);

        SmtIdentifier
    }
}

impl Parsable for LemmaItem {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::lemma_item);

        let mut inner = pair.into_inner();

        let name = LemmaIdentifier::parse_ref(file_id, state, inner.next().unwrap());
        let pre_colon_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let pre_open_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let dependencies = SmtIdentifierList::parse_ref(file_id, state, inner.next().unwrap());

        Self {
            name,
            pre_colon_trivia,
            pre_open_trivia,
            dependencies,
        }
    }
}

impl Parsable for LemmaBlock {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::lemmas_block);

        let mut inner = pair.into_inner();

        let _kw_pair = inner.next().unwrap();
        let trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let items = LemmaItemList::parse_ref(file_id, state, inner.next().unwrap());

        Self { trivia, items }
    }
}

impl Parsable for EquivalenceOracleItem {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::eqv_oracle_block_item);

        let inner = pair.into_inner().next().unwrap();

        match inner.as_rule() {
            Rule::invariant_spec => {
                Self::InvariantSpec(InvariantSpec::parse_ref(file_id, state, inner))
            }
            Rule::lemmas_block => Self::LemmaBlock(LemmaBlock::parse_ref(file_id, state, inner)),
            _ => unreachable!(),
        }
    }
}

impl Parsable for EquivalenceOracleBlock {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::eqv_oracle_block);

        let mut inner = pair.into_inner();

        let name = OracleIdentifier::parse_ref(file_id, state, inner.next().unwrap());
        let pre_colon_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let pre_brace_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let items = EquivalenceOracleItemList::parse_ref(file_id, state, inner.next().unwrap());

        Self {
            name,
            pre_colon_trivia,
            pre_brace_trivia,
            items,
        }
    }
}

impl Parsable for Equivalence {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::equivalence);

        let mut inner = pair.into_inner();

        let _kw_pair = inner.next().unwrap();
        let kw_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let left_name = GameInstanceIdentifier::parse_ref(file_id, state, inner.next().unwrap());
        let left_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let right_name = GameInstanceIdentifier::parse_ref(file_id, state, inner.next().unwrap());
        let right_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let blocks = EquivalenceOracleBlockList::parse_ref(file_id, state, inner.next().unwrap());

        Self {
            kw_trivia,
            left_name,
            left_trivia,
            right_name,
            right_trivia,
            blocks,
        }
    }
}

impl Parsable for Bound {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::bound);

        let mut inner = pair.into_inner();

        let lhs = GameInstanceIdentifier::parse_ref(file_id, state, inner.next().unwrap());
        let pre_tilde_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let post_tilde_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let rhs = GameInstanceIdentifier::parse_ref(file_id, state, inner.next().unwrap());

        Self {
            lhs,
            pre_tilde_trivia,
            post_tilde_trivia,
            rhs,
        }
    }
}

impl Parsable for AssumptionsItem {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::assumptions_item);

        let mut inner = pair.into_inner();

        let name = AssumptionIdentifier::parse_ref(file_id, state, inner.next().unwrap());
        let pre_colon_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let pre_brace_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let bound = Bound::parse_ref(file_id, state, inner.next().unwrap());

        Self {
            name,
            pre_colon_trivia,
            pre_brace_trivia,
            bound,
        }
    }
}

impl Parsable for AssumptionsBlock {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::assumptions_block);

        let mut inner = pair.into_inner();

        let _kw_pair = inner.next().unwrap();
        let trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let items = AssumptionsItemList::parse_ref(file_id, state, inner.next().unwrap());

        Self { trivia, items }
    }
}

impl Parsable for Conjecture {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::conjecture);

        let mut inner = pair.into_inner();

        let _kw_pair = inner.next().unwrap();
        let left_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let left_name = GameInstanceIdentifier::parse_ref(file_id, state, inner.next().unwrap());
        let right_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let right_name = GameInstanceIdentifier::parse_ref(file_id, state, inner.next().unwrap());

        Self {
            left_trivia,
            left_name,
            right_trivia,
            right_name,
        }
    }
}

impl Parsable for ReductionAssumptionLine {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::red_assumption_line);

        let mut inner = pair.into_inner();

        let _kw_assumption = inner.next().unwrap();
        let trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let name = AssumptionIdentifier::parse_ref(file_id, state, inner.next().unwrap());

        Self { trivia, name }
    }
}

impl Parsable for ReductionMapItem {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::red_map_item);

        let mut inner = pair.into_inner();

        let left_name = PackageInstanceIdentifier::parse_ref(file_id, state, inner.next().unwrap());
        let colon_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let right_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let right_name =
            PackageInstanceIdentifier::parse_ref(file_id, state, inner.next().unwrap());

        Self {
            left_name,
            colon_trivia,
            right_trivia,
            right_name,
        }
    }
}

impl Parsable for ReductionMap {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::red_map);

        let mut inner = pair.into_inner();

        let _kw = inner.next().unwrap();

        Self {
            assumption_trivia: Trivia::parse_ref(file_id, state, inner.next().unwrap()),
            assumption_name: GameInstanceIdentifier::parse_ref(
                file_id,
                state,
                inner.next().unwrap(),
            ),
            construction_trivia: Trivia::parse_ref(file_id, state, inner.next().unwrap()),
            construction_name: GameInstanceIdentifier::parse_ref(
                file_id,
                state,
                inner.next().unwrap(),
            ),
            items_trivia: Trivia::parse_ref(file_id, state, inner.next().unwrap()),
            items: ReductionMapItemList::parse_ref(file_id, state, inner.next().unwrap()),
        }
    }
}

impl Parsable for ReductionItem {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::red_item);

        let inner = pair.into_inner().next().unwrap();

        match inner.as_rule() {
            Rule::red_assumption_line => {
                Self::AssumptionLine(ReductionAssumptionLine::parse_ref(file_id, state, inner))
            }
            Rule::red_map => Self::Map(ReductionMap::parse_ref(file_id, state, inner)),
            _ => unreachable!(),
        }
    }
}

impl Parsable for Reduction {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::reduction);

        let mut inner = pair.into_inner();

        let _kw = inner.next().unwrap();

        Self {
            left_trivia: Trivia::parse_ref(file_id, state, inner.next().unwrap()),
            left_name: GameInstanceIdentifier::parse_ref(file_id, state, inner.next().unwrap()),
            right_trivia: Trivia::parse_ref(file_id, state, inner.next().unwrap()),
            right_name: GameInstanceIdentifier::parse_ref(file_id, state, inner.next().unwrap()),
            items_trivia: Trivia::parse_ref(file_id, state, inner.next().unwrap()),
            items: ReductionItemList::parse_ref(file_id, state, inner.next().unwrap()),
        }
    }
}

impl Parsable for GameHopItem {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::gamehop_item);

        let inner = pair.into_inner().next().unwrap();

        match inner.as_rule() {
            Rule::reduction => Self::Reduction(Reduction::parse_ref(file_id, state, inner)),
            Rule::equivalence => Self::Equivalence(Equivalence::parse_ref(file_id, state, inner)),
            Rule::conjecture => Self::Conjecture(Conjecture::parse_ref(file_id, state, inner)),
            _ => unreachable!(),
        }
    }
}

impl Parsable for GameHops {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::gamehops);

        let mut inner = pair.into_inner();

        let _kw = inner.next().unwrap();

        Self {
            trivia: Trivia::parse_ref(file_id, state, inner.next().unwrap()),
            items: GameHopItemList::parse_ref(file_id, state, inner.next().unwrap()),
        }
    }
}

impl Parsable for TheoremConstDecl {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        common::parse_value_decl(file_id, state, pair)
    }
}

impl Parsable for TheoremConstParamBlock {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::consts_param_block);

        let mut inner = pair.into_inner();

        let _kw_pair = inner.next().unwrap();
        let trivia_pair = inner.next().unwrap();
        let decls_pair = inner.next().unwrap();

        let trivia = Trivia::parse_ref(file_id, state, trivia_pair);
        let decls = TheoremConstDeclList::parse_ref(file_id, state, decls_pair);

        Self { trivia, decls }
    }
}

impl Parsable for TheoremItem {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::theorem_item);

        let inner = pair.into_inner().next().unwrap();

        match inner.as_rule() {
            Rule::consts_param_block => {
                Self::ConstParams(TheoremConstParamBlock::parse_ref(file_id, state, inner))
            }
            Rule::inst_block => Self::GameInstance(InstanceBlock::parse_ref(file_id, state, inner)),
            Rule::assumptions_block => {
                Self::Assumptions(AssumptionsBlock::parse_ref(file_id, state, inner))
            }
            Rule::gamehops => Self::GameHops(GameHops::parse_ref(file_id, state, inner)),
            Rule::proposition_block => todo!(),
            _ => unreachable!(),
        }
    }
}

impl Parsable for Theorem {
    fn parse(file_id: crate::source::FileId, state: &mut crate::State, pair: crate::Pair) -> Self {
        debug_assert_eq!(pair.as_rule(), Rule::theorem);

        let mut inner = pair.into_inner();
        let _kw_pair = inner.next().unwrap();
        let name_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let name = TheoremIdentifier::parse_ref(file_id, state, inner.next().unwrap());
        let brace_trivia = Trivia::parse_ref(file_id, state, inner.next().unwrap());
        let items = TheoremItemList::parse_ref(file_id, state, inner.next().unwrap());

        Self {
            name_trivia,
            name,
            brace_trivia,
            items,
        }
    }
}

#[cfg(test)]
mod static_checks {
    use super::*;

    fn impls_parsable<T: Parsable>() {}

    #[test]
    fn impl_parsable() {
        impls_parsable::<TheoremItem>();
        impls_parsable::<TheoremConstParamBlock>();
    }
}
