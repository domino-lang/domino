pub mod diag;
mod scope;
mod util;

mod resolve_game;
mod resolve_package;
mod resolve_theorem;

mod resolutions;

use std::collections::HashMap;

use domino_ast::{
    arena::{Arena, Ref},
    ast_nodes::{game, identifier, package, theorem},
    Arenas, DenseTable, LocationTable, PartialDenseTable, Visitor as _,
};
use scope::{Declaration, DeclarationType};

pub use resolve_package::{PackageInfo, PackageVisitor};

use crate::{resolve_package::PartialPackagedIdentifierResolution, util::get_text};

pub struct Resolver<'arena> {
    locations: &'arena LocationTable,
    arenas: &'arena Arenas,

    // side tables for packages
    pkg_names: PartialDenseTable<identifier::PackageIdentifier, resolutions::PackageResolution>,

    oracle_def_names: PartialDenseTable<
        identifier::OracleDefinitionIdentifier,
        resolutions::OracleDefinitionResolution,
    >,
    oracle_import_names:
        PartialDenseTable<identifier::OracleImportIdentifier, resolutions::OracleImportResolution>,
    oracle_composition_import_names: PartialDenseTable<
        identifier::OracleCompositionIdentifier,
        resolutions::OracleCompositionImportResolution,
    >,
    oracle_composition_def_names: PartialDenseTable<
        identifier::OracleCompositionIdentifier,
        resolutions::OracleCompositionDefinitionResolution,
    >,
    pkg_const_value_names: PartialDenseTable<
        identifier::PackageConstValueIdentifier,
        resolutions::PackageConstValueResolution,
    >,
    oracle_value_names:
        PartialDenseTable<identifier::OracleValueIdentifier, resolutions::OracleValueResolution>,
    pkg_type_names:
        PartialDenseTable<identifier::PackageTypeIdentifier, resolutions::PackageTypeResolution>,
    pkg_type_arg_names: PartialDenseTable<
        identifier::PackageTypeArgumentIdentifier,
        resolutions::PackageTypeArgResolution,
    >,
    is_state: PartialDenseTable<package::PackageConstDecl, bool>,

    // indexed packages
    pkg_infos: HashMap<&'arena str, PackageInfo>,

    // side tables for games
    game_names: PartialDenseTable<identifier::GameIdentifier, resolutions::GameResolution>,
    game_type_names:
        PartialDenseTable<identifier::GameTypeIdentifier, resolutions::GameTypeResolution>,
    game_type_arg_names: PartialDenseTable<
        identifier::GameTypeArgumentIdentifier,
        resolutions::GameTypeArgResolution,
    >,
    game_const_value_names: PartialDenseTable<
        identifier::GameConstValueIdentifier,
        resolutions::GameConstValueResolution,
    >,
    pkg_inst_names: PartialDenseTable<
        identifier::PackageInstanceIdentifier,
        resolutions::PackageInstanceResolution,
    >,

    // indexed games
    game_infos: HashMap<&'arena str, resolve_game::GameInfo>,

    // side tables for theorems
    theorem_names:
        PartialDenseTable<identifier::TheoremIdentifier, resolutions::TheoremResolution>,
    theorem_type_names:
        PartialDenseTable<identifier::TheoremTypeIdentifier, resolutions::TheoremTypeResolution>,
    theorem_type_arg_names: PartialDenseTable<
        identifier::TheoremTypeArgumentIdentifier,
        resolutions::TheoremTypeArgResolution,
    >,
    theorem_const_value_names: PartialDenseTable<
        identifier::TheoremConstValueIdentifier,
        resolutions::TheoremConstValueResolution,
    >,
    game_inst_names:
        PartialDenseTable<identifier::GameInstanceIdentifier, resolutions::GameInstanceResolution>,
    assumption_names:
        PartialDenseTable<identifier::AssumptionIdentifier, resolutions::AssumptionResolution>,
    lemma_names: PartialDenseTable<identifier::LemmaIdentifier, resolutions::LemmaResolution>,

    // indexed theorems
    theorem_infos: HashMap<&'arena str, resolve_theorem::TheoremInfo>,

    diagnostics: Arena<diag::Diagnostic>,
}

pub struct IdentifierResolution<'arena> {
    // indexed packages
    pub pkg_infos: HashMap<&'arena str, PackageInfo>,
    //
    // indexed games
    pub game_infos: HashMap<&'arena str, resolve_game::GameInfo>,
    //
    // indexed theorems
    pub theorem_infos: HashMap<&'arena str, resolve_theorem::TheoremInfo>,

    // side tables for packages
    pub pkg_names: DenseTable<identifier::PackageIdentifier, resolutions::PackageResolution>,
    pub oracle_def_names:
        DenseTable<identifier::OracleDefinitionIdentifier, resolutions::OracleDefinitionResolution>,
    pub oracle_import_names:
        DenseTable<identifier::OracleImportIdentifier, resolutions::OracleImportResolution>,
    pub oracle_composition_import_names: DenseTable<
        identifier::OracleCompositionIdentifier,
        resolutions::OracleCompositionImportResolution,
    >,
    pub oracle_composition_def_names: DenseTable<
        identifier::OracleCompositionIdentifier,
        resolutions::OracleCompositionDefinitionResolution,
    >,
    pub pkg_const_value_names: DenseTable<
        identifier::PackageConstValueIdentifier,
        resolutions::PackageConstValueResolution,
    >,
    pub oracle_value_names:
        DenseTable<identifier::OracleValueIdentifier, resolutions::OracleValueResolution>,
    pub pkg_type_names:
        DenseTable<identifier::PackageTypeIdentifier, resolutions::PackageTypeResolution>,
    pub pkg_type_arg_names: DenseTable<
        identifier::PackageTypeArgumentIdentifier,
        resolutions::PackageTypeArgResolution,
    >,
    pub is_state: DenseTable<package::PackageConstDecl, bool>,

    // side tables for games
    pub game_names: DenseTable<identifier::GameIdentifier, resolutions::GameResolution>,
    pub game_type_names:
        DenseTable<identifier::GameTypeIdentifier, resolutions::GameTypeResolution>,
    pub game_type_arg_names:
        DenseTable<identifier::GameTypeArgumentIdentifier, resolutions::GameTypeArgResolution>,
    pub game_const_value_names:
        DenseTable<identifier::GameConstValueIdentifier, resolutions::GameConstValueResolution>,
    pub pkg_inst_names:
        DenseTable<identifier::PackageInstanceIdentifier, resolutions::PackageInstanceResolution>,

    // side tables for theorems
    pub theorem_names:
        DenseTable<identifier::TheoremIdentifier, resolutions::TheoremResolution>,
    pub theorem_type_names:
        DenseTable<identifier::TheoremTypeIdentifier, resolutions::TheoremTypeResolution>,
    pub theorem_type_arg_names: DenseTable<
        identifier::TheoremTypeArgumentIdentifier,
        resolutions::TheoremTypeArgResolution,
    >,
    pub theorem_const_value_names: DenseTable<
        identifier::TheoremConstValueIdentifier,
        resolutions::TheoremConstValueResolution,
    >,
    pub game_inst_names:
        DenseTable<identifier::GameInstanceIdentifier, resolutions::GameInstanceResolution>,
    pub assumption_names:
        DenseTable<identifier::AssumptionIdentifier, resolutions::AssumptionResolution>,
    pub lemma_names: DenseTable<identifier::LemmaIdentifier, resolutions::LemmaResolution>,
}

impl<'arena> Resolver<'arena> {
    pub fn new(locations: &'arena LocationTable, arenas: &'arena Arenas) -> Self {
        Self {
            locations,
            arenas,

            oracle_def_names: PartialDenseTable::with_sizes_from_arena(arenas),
            oracle_import_names: PartialDenseTable::with_sizes_from_arena(arenas),
            oracle_composition_def_names: PartialDenseTable::with_sizes_from_arena(arenas),
            oracle_composition_import_names: PartialDenseTable::with_sizes_from_arena(arenas),
            pkg_const_value_names: PartialDenseTable::with_sizes_from_arena(arenas),
            oracle_value_names: PartialDenseTable::with_sizes_from_arena(arenas),
            pkg_type_names: PartialDenseTable::with_sizes_from_arena(arenas),
            pkg_type_arg_names: PartialDenseTable::with_sizes_from_arena(arenas),
            is_state: PartialDenseTable::with_sizes_from_arena(arenas),

            pkg_names: PartialDenseTable::with_sizes_from_arena(arenas),
            game_names: PartialDenseTable::with_sizes_from_arena(arenas),
            game_type_names: PartialDenseTable::with_sizes_from_arena(arenas),
            game_type_arg_names: PartialDenseTable::with_sizes_from_arena(arenas),
            game_const_value_names: PartialDenseTable::with_sizes_from_arena(arenas),
            pkg_inst_names: PartialDenseTable::with_sizes_from_arena(arenas),

            theorem_names: PartialDenseTable::with_sizes_from_arena(arenas),
            theorem_type_names: PartialDenseTable::with_sizes_from_arena(arenas),
            theorem_type_arg_names: PartialDenseTable::with_sizes_from_arena(arenas),
            theorem_const_value_names: PartialDenseTable::with_sizes_from_arena(arenas),
            game_inst_names: PartialDenseTable::with_sizes_from_arena(arenas),
            assumption_names: PartialDenseTable::with_sizes_from_arena(arenas),
            lemma_names: PartialDenseTable::with_sizes_from_arena(arenas),

            diagnostics: Default::default(),
            pkg_infos: Default::default(),
            game_infos: Default::default(),
            theorem_infos: Default::default(),
        }
    }

    pub fn process_package(&mut self, package: Ref<package::Package>) {
        let tables = PartialPackagedIdentifierResolution {
            pkg_names: &mut self.pkg_names,
            oracle_def_names: &mut self.oracle_def_names,
            oracle_import_names: &mut self.oracle_import_names,
            const_value_names: &mut self.pkg_const_value_names,
            oracle_value_names: &mut self.oracle_value_names,
            type_names: &mut self.pkg_type_names,
            type_arg_names: &mut self.pkg_type_arg_names,
            is_state: &mut self.is_state,
        };
        let mut info = None;

        let mut visitor = resolve_package::PackageVisitor::new(
            self.locations,
            &mut self.diagnostics,
            tables,
            &mut info,
        );

        visitor.package(self.arenas, package);

        if let Some(pkg_info) = info {
            let name = get_text(pkg_info.name, self.locations, &self.arenas.source);
            self.pkg_infos.insert(name, pkg_info);
        }
    }

    pub fn process_game(&mut self, game: Ref<game::Game>) {
        let tables = resolve_game::GameVisitorPartialTables {
            game_names: &mut self.game_names,
            game_type_names: &mut self.game_type_names,
            game_type_arg_names: &mut self.game_type_arg_names,
            game_const_value_names: &mut self.game_const_value_names,
            pkg_inst_names: &mut self.pkg_inst_names,
            pkg_const_value_names: &mut self.pkg_const_value_names,
            pkg_type_names: &mut self.pkg_type_names,
            pkg_names: &mut self.pkg_names,
            oracle_composition_def_names: &mut self.oracle_composition_def_names,
            oracle_composition_import_names: &mut self.oracle_composition_import_names,
        };

        let mut info = None;

        let mut visitor = resolve_game::GameVisitor::new(
            self.locations,
            &mut self.diagnostics,
            tables,
            &mut info,
            &self.pkg_infos,
        );

        visitor.game(self.arenas, game);

        if let Some(game_info) = info {
            let name = get_text(game_info.name, self.locations, &self.arenas.source);
            self.game_infos.insert(name, game_info);
        }
    }

    pub fn process_theorem(&mut self, thm: Ref<theorem::Theorem>) {
        let tables = resolve_theorem::TheoremVisitorPartialTables {
            theorem_names: &mut self.theorem_names,
            theorem_type_names: &mut self.theorem_type_names,
            theorem_type_arg_names: &mut self.theorem_type_arg_names,
            theorem_const_value_names: &mut self.theorem_const_value_names,
            game_inst_names: &mut self.game_inst_names,
            assumption_names: &mut self.assumption_names,
            lemma_names: &mut self.lemma_names,
            game_names: &mut self.game_names,
            game_type_names: &mut self.game_type_names,
            game_const_value_names: &mut self.game_const_value_names,
            pkg_inst_names: &mut self.pkg_inst_names,
            oracle_composition_import_names: &mut self.oracle_composition_import_names,
            oracle_composition_def_names: &mut self.oracle_composition_def_names,
        };

        let mut info = None;

        let mut visitor = resolve_theorem::TheoremVisitor::new(
            self.locations,
            &mut self.diagnostics,
            tables,
            &mut info,
            &self.game_infos,
            &self.pkg_infos,
        );

        visitor.thm(self.arenas, thm);

        if let Some(theorem_info) = info {
            let name = get_text(theorem_info.name, self.locations, &self.arenas.source);
            self.theorem_infos.insert(name, theorem_info);
        }
    }

    pub fn diagnostics(&self) -> &Arena<diag::Diagnostic> {
        &self.diagnostics
    }

    pub fn pkg_infos(&self) -> &HashMap<&'arena str, PackageInfo> {
        &self.pkg_infos
    }

    pub fn finish(self) -> IdentifierResolution<'arena> {
        let failed = print_missing! {
            self,
            pkg_names,
            oracle_def_names,
            oracle_import_names,
            oracle_composition_def_names,
            oracle_composition_import_names,
            pkg_const_value_names,
            oracle_value_names,
            pkg_type_names,
            pkg_type_arg_names,
            is_state,
            game_names,
            game_type_names,
            game_type_arg_names,
            game_const_value_names,
            pkg_inst_names,
            theorem_names,
            theorem_type_names,
            theorem_type_arg_names,
            theorem_const_value_names,
            game_inst_names,
            assumption_names,
            lemma_names,
        };

        if failed {
            panic!("did not expect to find unresolved nodes")
        }

        IdentifierResolution {
            pkg_infos: self.pkg_infos,
            game_infos: self.game_infos,
            theorem_infos: self.theorem_infos,

            pkg_names: self.pkg_names.finish().expect("error finishing pkg_names"),
            oracle_def_names: self
                .oracle_def_names
                .finish()
                .expect("error finishing oracle_def_names"),
            oracle_import_names: self
                .oracle_import_names
                .finish()
                .expect("error finishing oracle_import_names"),
            oracle_composition_import_names: self
                .oracle_composition_import_names
                .finish()
                .expect("error finishing oracle_composition_import_names"),
            oracle_composition_def_names: self
                .oracle_composition_def_names
                .finish()
                .expect("error finishing oracle_composition_def_names"),
            pkg_const_value_names: self
                .pkg_const_value_names
                .finish()
                .expect("error finishing pkg_const_value_names"),
            oracle_value_names: self
                .oracle_value_names
                .finish()
                .expect("error finishing oracle_value_names"),
            pkg_type_names: self
                .pkg_type_names
                .finish()
                .expect("error finishing pkg_type_names"),
            pkg_type_arg_names: self
                .pkg_type_arg_names
                .finish()
                .expect("error finishing pkg_type_arg_names"),
            is_state: self.is_state.finish().expect("error finishing is_state"),
            game_names: self
                .game_names
                .finish()
                .expect("error finishing game_names"),
            game_type_names: self
                .game_type_names
                .finish()
                .expect("error finishing game_type_names"),
            game_type_arg_names: self
                .game_type_arg_names
                .finish()
                .expect("error finishing game_type_arg_names"),
            game_const_value_names: self
                .game_const_value_names
                .finish()
                .expect("error finishing game_const_value_names"),
            pkg_inst_names: self
                .pkg_inst_names
                .finish()
                .expect("error finishing pkg_inst_names"),
            theorem_names: self
                .theorem_names
                .finish()
                .expect("error finishing theorem_names"),
            theorem_type_names: self
                .theorem_type_names
                .finish()
                .expect("error finishing theorem_type_names"),
            theorem_type_arg_names: self
                .theorem_type_arg_names
                .finish()
                .expect("error finishing theorem_type_arg_names"),
            theorem_const_value_names: self
                .theorem_const_value_names
                .finish()
                .expect("error finishing theorem_const_value_names"),
            game_inst_names: self
                .game_inst_names
                .finish()
                .expect("error finishing game_inst_names"),
            assumption_names: self
                .assumption_names
                .finish()
                .expect("error finishing assumption_names"),
            lemma_names: self
                .lemma_names
                .finish()
                .expect("error finishing lemma_names"),
        }
    }
}

// TODO: move these to a domino-semantics crate or so?

#[derive(Debug, Clone, Copy)]
pub enum BuiltinType {
    Integer,
    Bool,
    Bits,
    Table,
    Maybe,
}

#[derive(Debug, Clone, Copy)]
pub enum BuiltinValue {
    True,
    False,
    Some,
    None,
    EmptyTable,
}

/// If resolution fails, we emit a diagnostic and set an error resolution with a reference to the
/// diagnostic on the node.
///
/// It would be nicer if this could be a function, but we need to put in the name of the table, so
/// that doesn't work.
macro_rules! fail_resolution {
    ($self:expr, $node:expr, $diag:expr, $table:ident) => {
        $crate::fail_resolution!($self, $node, $diag, $table, then { return; })
    };

    ($self:expr, $node:expr, $diag:expr, $table:ident, then $blk:block ) => {{
        $crate::fail_resolution!($self, $node, $diag, $table, then err => $blk);
    }};

    ($self:expr, $node:expr, $diag:expr, $table:ident, then $err_name:ident => $blk:block ) => {{
        let $err_name = $self.diagnostics.alloc($diag.into());
        $self.tables.$table.set($node, $err_name.into());
        $blk
    }};
}

/// If resolution fails, we emit a diagnostic and set an error resolution with a reference to the
/// diagnostic on the node.
///
/// It would be nicer if this could be a function, but we need to put in the name of the table, so
/// that doesn't work.
///
/// This one takes a Ref<Diagnostic>, i.e. it's already allocated. Useful for forwarding errors
macro_rules! fail_resolution_ref {
    ($self:expr, $node:expr, $diag:expr, $table:ident) => {
        $crate::fail_resolution_ref!($self, $node, $diag, $table, then { return; })
    };

    ($self:expr, $node:expr, $diag:expr, $table:ident, then $blk:block ) => {{
        $crate::fail_resolution_ref!($self, $node, $diag, $table, then err => $blk);
    }};

    ($self:expr, $node:expr, $diag:expr, $table:ident, then $err_name:ident => $blk:block ) => {{
        $self.tables.$table.set($node, $diag.into());
        $blk
    }};
}

use fail_resolution;
use fail_resolution_ref;

macro_rules! print_missing {
    ($self:expr, $($name:ident),* ,) => { {
        let dx = domino_diagnostic::Resolver {
            arenas: $self.arenas,
            locations: $self.locations,
        };

        fn print_missing<T: domino_ast::ast_nodes::InArena + domino_ast::ast_nodes::NodeType>(dx: domino_diagnostic::Resolver,  name: &'static str, mut missing: impl Iterator<Item = Ref<T>>) {

            if let Some(first) = missing.next() {
                let mut errs = vec![diag::MissingResolution::new(dx, name, first)];

                print!("{name} is missing: {first:?}");

                for r in missing {
                    print!(", {r:?}");
                    errs.push(diag::MissingResolution::new(dx, name, r));
                }

                println!();
                for d in errs {
                    println!("{:?}", miette::Report::from(d));
                }
            }
        }

        let mut failed = false;
        $({
            let mut missing = $self.$name.missing().peekable();
            failed |= missing.peek().is_some();

            print_missing(dx, stringify!($name), missing);

        };)*

        failed

    } };
}

use print_missing;
