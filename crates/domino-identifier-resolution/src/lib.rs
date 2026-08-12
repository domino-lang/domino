pub mod diag;
mod scope;
mod util;

mod resolve_game;
mod resolve_package;

mod resolutions;

use std::collections::HashMap;

use domino_ast::{
    arena::{Arena, Ref},
    ast_nodes::{game, identifier, package},
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

    diagnostics: Arena<diag::Diagnostic>,
}

pub struct IdentifierResolution<'arena> {
    // indexed packages
    pub pkg_infos: HashMap<&'arena str, PackageInfo>,
    //
    // indexed games
    pub game_infos: HashMap<&'arena str, resolve_game::GameInfo>,

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
    pub game_const_value_names:
        DenseTable<identifier::GameConstValueIdentifier, resolutions::GameConstValueResolution>,
    pub pkg_inst_names:
        DenseTable<identifier::PackageInstanceIdentifier, resolutions::PackageInstanceResolution>,
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
            game_const_value_names: PartialDenseTable::with_sizes_from_arena(arenas),
            pkg_inst_names: PartialDenseTable::with_sizes_from_arena(arenas),

            diagnostics: Default::default(),
            pkg_infos: Default::default(),
            game_infos: Default::default(),
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
            game_const_value_names: &mut self.game_const_value_names,
            pkg_inst_names: &mut self.pkg_inst_names,
            pkg_const_value_names: &mut self.pkg_const_value_names,
            pkg_names: &mut self.pkg_names,
            oracle_def_names: &mut self.oracle_def_names,
            oracle_import_names: &mut self.oracle_import_names,
            oracle_composition_def_names: &mut self.oracle_composition_def_names,
            oracle_composition_import_names: &mut self.oracle_composition_import_names,
        };

        let mut info = None;

        let mut visitor = resolve_game::GameVisitor::new(
            &self.locations,
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

    pub fn diagnostics(&self) -> &Arena<diag::Diagnostic> {
        &self.diagnostics
    }

    pub fn pkg_infos(&self) -> &HashMap<&'arena str, PackageInfo> {
        &self.pkg_infos
    }

    pub fn finish(self) -> IdentifierResolution<'arena> {
        IdentifierResolution {
            pkg_infos: self.pkg_infos,
            game_infos: self.game_infos,

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
            game_const_value_names: self
                .game_const_value_names
                .finish()
                .expect("error finishing game_const_value_names"),
            pkg_inst_names: self
                .pkg_inst_names
                .finish()
                .expect("error finishing pkg_inst_names"),
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
        let err = $self.diagnostics.alloc($diag.into());
        $self.tables.$table.set($node, err.into());
        $blk
    }};
}

use fail_resolution;
