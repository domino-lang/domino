use domino_ast::ast_nodes::identifier;
use domino_resolutions::Resolves;

use crate::resolutions;

macro_rules! impl_resolves {
    ($from:ty, $to:ty, $name:ident) => {
        impl<'arena> Resolves<$from, $to> for crate::IdentifierResolution<'arena> {
            fn resolve(&self, from: domino_collections::arena::Ref<$from>) -> &$to {
                self.$name.get(from)
            }
            fn resolve_mut(&mut self, from: domino_collections::arena::Ref<$from>) -> &mut $to {
                self.$name.get_mut(from)
            }
        }
    };
}

// TODO: consider generating this alongside the struct in a single macro

impl_resolves!(
    identifier::PackageIdentifier,
    resolutions::PackageResolution,
    pkg_names
);

impl_resolves!(
    identifier::OracleDefinitionIdentifier,
    resolutions::OracleDefinitionResolution,
    oracle_def_names
);

impl_resolves!(
    identifier::OracleImportIdentifier,
    resolutions::OracleImportResolution,
    oracle_import_names
);

impl_resolves!(
    identifier::OracleCompositionIdentifier,
    resolutions::OracleCompositionImportResolution,
    oracle_composition_import_names
);

impl_resolves!(
    identifier::OracleCompositionIdentifier,
    resolutions::OracleCompositionDefinitionResolution,
    oracle_composition_def_names
);

impl_resolves!(
    identifier::PackageConstValueIdentifier,
    resolutions::PackageConstValueResolution,
    pkg_const_value_names
);

impl_resolves!(
    identifier::OracleValueIdentifier,
    resolutions::OracleValueResolution,
    oracle_value_names
);

impl_resolves!(
    identifier::PackageTypeIdentifier,
    resolutions::PackageTypeResolution,
    pkg_type_names
);

impl_resolves!(
    identifier::PackageTypeArgumentIdentifier,
    resolutions::PackageTypeArgResolution,
    pkg_type_arg_names
);

// side tables for games
impl_resolves!(
    identifier::GameIdentifier,
    resolutions::GameResolution,
    game_names
);

impl_resolves!(
    identifier::GameTypeIdentifier,
    resolutions::GameTypeResolution,
    game_type_names
);

impl_resolves!(
    identifier::GameTypeArgumentIdentifier,
    resolutions::GameTypeArgResolution,
    game_type_arg_names
);

impl_resolves!(
    identifier::GameConstValueIdentifier,
    resolutions::GameConstValueResolution,
    game_const_value_names
);

impl_resolves!(
    identifier::PackageInstanceIdentifier,
    resolutions::PackageInstanceResolution,
    pkg_inst_names
);

// side tables for theorems
impl_resolves!(
    identifier::TheoremIdentifier,
    resolutions::TheoremResolution,
    theorem_names
);

impl_resolves!(
    identifier::TheoremTypeIdentifier,
    resolutions::TheoremTypeResolution,
    theorem_type_names
);

impl_resolves!(
    identifier::TheoremTypeArgumentIdentifier,
    resolutions::TheoremTypeArgResolution,
    theorem_type_arg_names
);

impl_resolves!(
    identifier::TheoremConstValueIdentifier,
    resolutions::TheoremConstValueResolution,
    theorem_const_value_names
);

impl_resolves!(
    identifier::GameInstanceIdentifier,
    resolutions::GameInstanceResolution,
    game_inst_names
);

impl_resolves!(
    identifier::AssumptionIdentifier,
    resolutions::AssumptionResolution,
    assumption_names
);

impl_resolves!(
    identifier::LemmaIdentifier,
    resolutions::LemmaResolution,
    lemma_names
);
