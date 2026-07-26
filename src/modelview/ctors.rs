// SPDX-License-Identifier: MIT OR Apache-2.0

//! Builds two lookup tables that let us turn raw SMT names from a `cvc5` model back into the
//! Domino-level concepts they came from:
//!
//! - [`CtorMap`]: SMT constructor name -> record label + field labels. Used to interpret *values*
//!   (e.g. the body of `<<game-state-H7_1_1_0-old>>` is an application of
//!   `<mk-game-H7-<params>>`, and this map tells us the 5 positional arguments are
//!   "pkgstate-PRF", "pkgstate-MAC", ...).
//! - [`EntryLabels`]: SMT top-level entry name -> a [`Category`] + human display label. Used to
//!   group/label the *entries* of the model itself when rendering the report.
//!
//! Both maps are built by calling the exact same naming functions the SMT writer
//! (`writers::smt::patterns::*`) uses, fed with the real project data (the matched
//! `GameInstance`s, their packages, the theorem). This guarantees the names match exactly what
//! `cvc5` was given, without re-deriving or guessing the naming scheme.

use std::collections::HashMap;

use crate::{
    package::{Export, OracleSig, PackageInstance},
    theorem::{GameInstance, Theorem},
    transforms::samplify::{SampleInfo, Transformation},
    transforms::Transformation as _,
    writers::smt::patterns::{
        self,
        datastructures::game_consts::GameConstsPattern as DsGameConstsPattern,
        datastructures::theorem_consts::TheoremConstsPattern as DsTheoremConstsPattern,
        theorem_constants::ConstantPattern,
        DatastructurePattern, GameStateDeclareInfo, GameStatePattern as DsGameStatePattern,
        PackageStatePattern as DsPackageStatePattern, ReturnPattern,
    },
};

#[derive(Debug, Clone, Default)]
pub struct CtorInfo {
    pub label: String,
    pub fields: Vec<String>,
}

pub type CtorMap = HashMap<String, CtorInfo>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Side {
    Left,
    Right,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Category {
    TheoremConsts,
    GameConsts(Side),
    OldState(Side),
    NewState(Side, String),
    OracleArg { oracle: String, arg: String },
    RawReturn(Side, String),
    ReturnValue(Side, String),
    IsAbort(Side, String),
    RandVal(Side),
    RandCtr(Side),
}

#[derive(Debug, Clone)]
pub struct EntryLabel {
    pub category: Category,
    pub display: String,
}

pub type EntryLabels = HashMap<String, EntryLabel>;

fn insert_label(labels: &mut EntryLabels, name: String, category: Category, display: String) {
    labels.insert(name, EntryLabel { category, display });
}

fn insert_spec<'a, P: DatastructurePattern<'a>>(
    ctors: &mut CtorMap,
    pattern: &P,
    info: &'a P::DeclareInfo,
    label_prefix: &str,
    field_label: impl Fn(&P::Selector) -> String,
) {
    let spec = pattern.datastructure_spec(info);
    for (cons, sels) in spec.0 {
        let name = pattern.constructor_name(&cons);
        let fields = sels.iter().map(&field_label).collect();
        ctors.insert(
            name,
            CtorInfo {
                label: label_prefix.to_string(),
                fields,
            },
        );
    }
}

/// Project-independent constructors: `Maybe`, `TupleN` and the generic `ReturnValue` sum type
/// (`mk-return-value`/`mk-abort`), all declared verbatim for every project by `src/hacks.rs`.
/// (`mk-some`/`mk-none`/`mk-tupleN` are also special-cased directly in `value::interpret`; they're
/// kept here too so a lookup against `CtorMap` alone is still meaningful, e.g. for tests.)
pub fn builtin_ctors() -> CtorMap {
    let mut ctors = CtorMap::new();

    ctors.insert(
        "mk-some".to_string(),
        CtorInfo {
            label: "Some".to_string(),
            fields: vec!["value".to_string()],
        },
    );
    ctors.insert(
        "mk-none".to_string(),
        CtorInfo {
            label: "None".to_string(),
            fields: vec![],
        },
    );

    for n in 0..32 {
        ctors.insert(
            format!("mk-tuple{n}"),
            CtorInfo {
                label: String::new(),
                fields: (0..n).map(|i| format!("_{i}")).collect(),
            },
        );
    }

    ctors.insert(
        "mk-return-value".to_string(),
        CtorInfo {
            label: "Return".to_string(),
            fields: vec!["value".to_string()],
        },
    );
    ctors.insert(
        "mk-abort".to_string(),
        CtorInfo {
            label: "Abort".to_string(),
            fields: vec![],
        },
    );

    ctors
}

/// One side (left or right) of a matched equivalence-style proof step, with everything needed to
/// rebuild the exact naming scheme the writer used for it.
pub struct SideInfo<'a> {
    pub side: Side,
    pub game_inst: &'a GameInstance,
    pub sample_info: SampleInfo,
}

impl<'a> SideInfo<'a> {
    pub fn new(side: Side, game_inst: &'a GameInstance) -> Self {
        let (_, sample_info) = Transformation(game_inst.game()).transform().unwrap();
        Self {
            side,
            game_inst,
            sample_info,
        }
    }

    pub fn game_name(&self) -> &str {
        self.game_inst.game_name()
    }

    pub fn inst_name(&self) -> &str {
        self.game_inst.name()
    }

    fn pkg_instances(&self) -> &[PackageInstance] {
        &self.game_inst.game().pkgs
    }

    fn exports(&self) -> &[Export] {
        &self.game_inst.game().exports
    }
}

/// Builds the constructor map and entry-label map for a matched proof step (a pair of game
/// instances belonging to one theorem). Also merges in [`builtin_ctors`].
pub fn build_maps(theorem: &Theorem, left: &SideInfo, right: &SideInfo) -> (CtorMap, EntryLabels) {
    let mut ctors = builtin_ctors();
    let mut labels = EntryLabels::new();

    // theorem constants
    let theorem_consts_pattern = DsTheoremConstsPattern {
        theorem_name: &theorem.name,
    };
    insert_spec(
        &mut ctors,
        &theorem_consts_pattern,
        theorem,
        "theorem consts",
        |sel| sel.name.to_string(),
    );
    insert_label(
        &mut labels,
        "<<theorem-consts>>".to_string(),
        Category::TheoremConsts,
        "theorem constants".to_string(),
    );

    for side in [left, right] {
        add_side(&mut ctors, &mut labels, side);
    }

    (ctors, labels)
}

fn add_side(ctors: &mut CtorMap, labels: &mut EntryLabels, side: &SideInfo) {
    let inst_name = side.inst_name();
    let game_name = side.game_name();
    let params = &side.game_inst.consts;

    // game state datatype (pkg-instance + randomness fields)
    let game_state_pattern = DsGameStatePattern { game_name, params };
    let declare_info = GameStateDeclareInfo {
        game_inst: side.game_inst,
        sample_info: &side.sample_info,
    };
    // NOTE: the game-state constructor/sort only depend on the game name and its *integer*
    // params (see `only_ints` in the naming code), not on the game *instance* name -- so for a
    // same-game equivalence (the common case) left and right share this exact constructor. Don't
    // put an instance name in its label, or whichever side is processed last wins.
    insert_spec(
        ctors,
        &game_state_pattern,
        &declare_info,
        &format!("{game_name} state"),
        |sel| match sel {
            patterns::GameStateSelector::PackageInstance { pkg_inst_name, .. } => {
                pkg_inst_name.to_string()
            }
            patterns::GameStateSelector::Randomness { sample_pos } => {
                format!("rand[{}.{}]", sample_pos.pkg_name, sample_pos.oracle_name)
            }
        },
    );

    insert_label(
        labels,
        format!("<<game-state-{inst_name}-old>>"),
        Category::OldState(side.side),
        format!("{inst_name}: old state"),
    );

    // game consts
    let game_consts_pattern = DsGameConstsPattern { game_name };
    insert_spec(
        ctors,
        &game_consts_pattern,
        side.game_inst.game(),
        &format!("{game_name} consts"),
        |sel| sel.name.to_string(),
    );

    // package state, per package instance
    for pkg_inst in side.pkg_instances() {
        let pkg_state_pattern = DsPackageStatePattern {
            pkg_name: &pkg_inst.pkg.name,
            params: &pkg_inst.params,
        };
        insert_spec(
            ctors,
            &pkg_state_pattern,
            &pkg_inst.pkg,
            &pkg_inst.name,
            |sel| sel.name.to_string(),
        );
    }

    // return values + abort flags + new-state, per exported oracle
    for export in side.exports() {
        let pkg_inst = &side.game_inst.game().pkgs[export.to()];
        let sig: &OracleSig = export.sig();
        let oracle_import_name = export.name();

        // like the game-state constructor above, this only depends on game/pkg/oracle name, not
        // the game instance name.
        let return_pattern = ReturnPattern {
            game_name,
            game_params: params,
            pkg_name: &pkg_inst.pkg.name,
            pkg_params: &pkg_inst.params,
            oracle_name: &sig.name,
        };
        insert_spec(
            ctors,
            &return_pattern,
            &sig.ty,
            &format!("{oracle_import_name} return"),
            |sel| match sel {
                patterns::ReturnSelector::GameState => "new-state".to_string(),
                patterns::ReturnSelector::ReturnValueOrAbort { .. } => {
                    "return-value-or-abort".to_string()
                }
            },
        );

        // `mk-return-value`/`mk-abort` are a single project-wide generic sum type (see
        // `builtin_ctors`); no need to (and no good way to, since the constructor name doesn't
        // depend on the oracle) re-register it per oracle here.

        // oracle args are (usually) shared between both sides, named using this side's game
        // name; if left/right happen to use different game names, both get their own entry.
        for (arg_name, arg_type) in &sig.args {
            let arg = patterns::theorem_constants::OracleArgs {
                oracle_name: oracle_import_name,
                game_name,
                arg_name,
                arg_type,
            };
            insert_label(
                labels,
                arg.name(),
                Category::OracleArg {
                    oracle: oracle_import_name.to_string(),
                    arg: arg_name.clone(),
                },
                format!("{oracle_import_name} arg {arg_name}"),
            );
        }

        let ret = patterns::theorem_constants::ReturnConst {
            game_inst_name: inst_name,
            game_name,
            game_params: params,
            pkg_name: &pkg_inst.pkg.name,
            pkg_params: &pkg_inst.params,
            oracle_name: &sig.name,
            oracle_import_name,
        };
        insert_label(
            labels,
            ret.name(),
            Category::RawReturn(side.side, oracle_import_name.to_string()),
            format!("{inst_name}.{oracle_import_name}: raw return"),
        );

        let ret_value = patterns::theorem_constants::ReturnValueConst {
            game_inst_name: inst_name,
            pkg_inst_name: &pkg_inst.name,
            oracle_name: oracle_import_name,
            ty: &sig.ty,
        };
        insert_label(
            labels,
            ret_value.name(),
            Category::ReturnValue(side.side, oracle_import_name.to_string()),
            format!("{inst_name}.{oracle_import_name}: return value"),
        );

        let is_abort = patterns::ReturnIsAbortConst {
            game_inst_name: inst_name,
            pkg_inst_name: &pkg_inst.name,
            oracle_name: oracle_import_name,
            ty: &sig.ty,
        };
        insert_label(
            labels,
            is_abort.name(),
            Category::IsAbort(side.side, oracle_import_name.to_string()),
            format!("{inst_name}.{oracle_import_name}: aborted?"),
        );

        insert_label(
            labels,
            format!("<<game-state-{inst_name}-new-{oracle_import_name}>>"),
            Category::NewState(side.side, oracle_import_name.to_string()),
            format!("{inst_name}: new state (after {oracle_import_name})"),
        );
    }

    // sampled randomness
    for pos in &side.sample_info.positions {
        insert_label(
            labels,
            format!("randval-{inst_name}-{}", pos.sample_id),
            Category::RandVal(side.side),
            format!(
                "{inst_name}: sampled value for {}.{}/{}",
                pos.pkg_name, pos.oracle_name, pos.sample_name
            ),
        );
        insert_label(
            labels,
            format!("randctr-{inst_name}-{}", pos.sample_id),
            Category::RandCtr(side.side),
            format!(
                "{inst_name}: sample counter for {}.{}/{}",
                pos.pkg_name, pos.oracle_name, pos.sample_name
            ),
        );
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::writers::smt::patterns::DatastructureSpec;

    #[test]
    fn builtin_ctors_cover_maybe_tuple_and_return_value() {
        let ctors = builtin_ctors();

        assert_eq!(ctors["mk-some"].fields, vec!["value".to_string()]);
        assert!(ctors["mk-none"].fields.is_empty());
        assert_eq!(ctors["mk-tuple3"].fields, vec!["_0", "_1", "_2"]);
        assert_eq!(ctors["mk-return-value"].label, "Return");
        assert_eq!(ctors["mk-abort"].label, "Abort");
    }

    /// A minimal `DatastructurePattern` used only to exercise `insert_spec` without needing a
    /// real `Package`/`Theorem`/`GameInstance`.
    struct TestPattern;

    impl<'a> DatastructurePattern<'a> for TestPattern {
        type Constructor = ();
        type Selector = &'a str;
        type DeclareInfo = Vec<&'a str>;

        const CAMEL_CASE: &'static str = "Test";
        const KEBAB_CASE: &'static str = "test";

        fn sort_name(&self) -> String {
            "Test".to_string()
        }

        fn constructor_name(&self, _cons: &Self::Constructor) -> String {
            "mk-test".to_string()
        }

        fn selector_name(&self, sel: &Self::Selector) -> String {
            format!("test-{sel}")
        }

        fn selector_sort(&self, _sel: &Self::Selector) -> crate::writers::smt::exprs::SmtExpr {
            "Int".into()
        }

        fn matchfield_name(&self, sel: &Self::Selector) -> String {
            format!("match-{sel}")
        }

        fn datastructure_spec(&self, info: &'a Self::DeclareInfo) -> DatastructureSpec<'a, Self> {
            DatastructureSpec(vec![((), info.clone())])
        }
    }

    #[test]
    fn insert_spec_registers_constructor_with_field_labels() {
        let mut ctors = CtorMap::new();
        let fields = vec!["a", "b"];

        insert_spec(&mut ctors, &TestPattern, &fields, "my record", |sel| {
            sel.to_uppercase()
        });

        let info = ctors.get("mk-test").expect("constructor should be registered");
        assert_eq!(info.label, "my record");
        assert_eq!(info.fields, vec!["A".to_string(), "B".to_string()]);
    }
}
