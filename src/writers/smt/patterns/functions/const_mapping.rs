use crate::{
    package::{Composition, Package},
    theorem::Theorem,
    writers::smt::{
        exprs::{SmtExpr, SmtLet},
        names::FunctionNameBuilder,
        patterns::{
            datastructures::game_consts::GameConstsPattern as GameConstsDatatypePattern,
            game_consts::{bind_game_consts, bind_theorem_consts},
            oracle_args::{GameConstsPattern, OracleArgPattern as _, TheoremConstsPattern},
            pkg_consts::PackageConstsPattern,
            DatastructurePattern, FunctionPattern,
        },
        sorts::Sort,
    },
};

use super::SmtDefineFun;

pub struct PackageConstMappingFunction<'a> {
    pub game_name: &'a str,
    pub pkg_name: &'a str,
    pub pkg_inst_name: &'a str,
}

impl FunctionPattern for PackageConstMappingFunction<'_> {
    fn function_name(&self) -> String {
        FunctionNameBuilder::new()
            .push("pkgconsts")
            .push(self.game_name)
            .push(self.pkg_inst_name)
            .build()
    }

    fn function_args(&self) -> Vec<(String, Sort)> {
        let game_consts_pattern = GameConstsPattern {
            game_name: self.game_name,
        };
        vec![("<game-consts>".to_string(), game_consts_pattern.sort())]
    }

    fn function_return_sort(&self) -> Sort {
        PackageConstsPattern {
            pkg_name: self.pkg_name,
        }
        .sort(vec![])
    }

    fn function_args_count(&self) -> usize {
        1
    }
}

pub struct GameConstMappingFunction<'a> {
    pub theorem_name: &'a str,
    pub game_name: &'a str,
    pub game_inst_name: &'a str,
}

impl FunctionPattern for GameConstMappingFunction<'_> {
    fn function_name(&self) -> String {
        FunctionNameBuilder::new()
            .push("gameconsts")
            .push(self.theorem_name)
            .push(self.game_inst_name)
            .build()
    }

    fn function_args(&self) -> Vec<(String, Sort)> {
        let theorem_consts_pattern = TheoremConstsPattern {
            theorem_name: self.theorem_name,
        };
        vec![(
            "<theorem-consts>".to_string(),
            theorem_consts_pattern.sort(),
        )]
    }

    fn function_return_sort(&self) -> Sort {
        GameConstsPattern {
            game_name: self.game_name,
        }
        .sort()
    }

    fn function_args_count(&self) -> usize {
        1
    }
}

pub fn define_pkg_const_mapping_fun<'a>(
    game: &'a Composition,
    pkg: &'a Package,
    pkg_inst_name: &'a str,
) -> Option<SmtDefineFun<SmtLet<SmtExpr>>> {
    let pkg_inst = game
        .pkgs
        .iter()
        .find(|pkg_inst| pkg_inst.name == pkg_inst_name)?;

    if pkg_inst.pkg.name != pkg.name {
        // TODO: return an error here
        return None;
    }
    let pkg_name = &pkg.name;

    let mapping_fun = PackageConstMappingFunction {
        game_name: game.name(),
        pkg_inst_name,
        pkg_name,
    };

    let pkg_consts = PackageConstsPattern { pkg_name };
    let pkg_consts_spec = pkg_consts.datastructure_spec(pkg);

    Some(
        mapping_fun.define_fun(bind_game_consts(
            game,
            &"<game-consts>".into(),
            pkg_consts
                .call_constructor(&pkg_consts_spec, vec![], &(), |sel| {
                    pkg_inst
                        .params
                        .iter()
                        .find(|(name, _)| name.ident_ref() == sel.name)
                        .map(|(_, expr)| expr.clone().into())
                })
                .unwrap(),
        )),
    )
}

pub fn define_game_const_mapping_fun<'a>(
    theorem: &'a Theorem<'a>,
    game: &'a Composition,
    game_inst_name: &'a str,
) -> Option<SmtDefineFun<SmtLet<SmtExpr>>> {
    let game_inst = theorem.find_game_instance(game_inst_name)?;

    if game_inst.game.name != game.name {
        // TODO: return an error here
        return None;
    }
    let game_name = &game.name;

    let mapping_fun = GameConstMappingFunction {
        theorem_name: &theorem.name,
        game_inst_name,
        game_name,
    };

    let game_consts = GameConstsDatatypePattern { game_name };
    let game_consts_spec = game_consts.datastructure_spec(game);

    Some(
        mapping_fun.define_fun(bind_theorem_consts(
            theorem,
            &"<theorem-consts>".into(),
            game_consts
                .call_constructor(&game_consts_spec, vec![], &(), |sel| {
                    game_inst
                        .consts
                        .iter()
                        .find(|(ident, _)| ident.name == sel.name)
                        .map(|(_, expr)| expr.clone().into())
                })
                .unwrap(),
        )),
    )
}
