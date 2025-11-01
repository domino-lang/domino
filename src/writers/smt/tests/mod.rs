// SPDX-License-Identifier: MIT OR Apache-2.0

use super::patterns::{game_consts, pkg_consts, pkg_state, DatastructurePattern};
use crate::{
    parser::tests::*,
    types::{CountSpec, Type},
    writers::smt::{
        exprs::SmtExpr,
        patterns::{
            const_mapping::define_pkg_const_mapping_fun, declare_datatype,
            game_consts::GameConstsSelector, pkg_consts::PackageConstsSelector,
            pkg_state::PackageStateSelector,
        },
        sorts::Sort,
    },
};

#[test]
fn test_const_datatypes_eq_small_small() {
    let pkgs = packages::parse_files(&["tiny.ssp"]);
    let games = games::parse_files(&["small.ssp"], &pkgs);
    let theorem_file = theorems::read_file("equivalence-small-small.ssp");
    let theorem = theorems::parse(&theorem_file, "equivalence-small-small.ssp", &pkgs, &games);

    let equivalence = theorem
        .game_hops
        .iter()
        .find_map(|hop| hop.as_equivalence())
        .unwrap();

    let game_inst = theorem.find_game_instance(equivalence.left_name()).unwrap();
    let game = &game_inst.game;
    let game_name = game.name();
    let game = &games[game_name];

    let game_const_pattern = game_consts::GameConstsPattern { game_name };
    let game_const_spec = game_const_pattern.datastructure_spec(game);

    let game_const_constructors = &game_const_spec.0;
    assert_eq!(game_const_constructors.len(), 1);
    let (_, game_const_selectors) = &game_const_constructors[0];
    assert_eq!(game_const_selectors.len(), game.consts.len());

    for GameConstsSelector { name, ty } in game_const_selectors {
        let (_, const_ty) = game
            .consts
            .iter()
            .find(|(const_name, _ty)| name == const_name)
            .unwrap();
        assert_eq!(ty, &const_ty);
    }

    let pkg_inst = &game.pkgs[0];
    let pkg_inst_name = &pkg_inst.name;
    let pkg = &pkg_inst.pkg;
    let pkg_name = &pkg.name;
    let pkg = &pkgs[pkg_name];

    let pkg_const_pattern = pkg_consts::PackageConstsPattern { pkg_name };
    let pkg_const_spec = pkg_const_pattern.datastructure_spec(pkg);

    let pkg_const_constructors = &pkg_const_spec.0;
    assert_eq!(pkg_const_constructors.len(), 1);
    let (_, pkg_const_selectors) = &pkg_const_constructors[0];
    assert_eq!(pkg_const_selectors.len(), 1);

    for PackageConstsSelector { name, ty } in pkg_const_selectors {
        let (_, const_ty, _) = pkg
            .params
            .iter()
            .find(|(const_name, _ty, _)| name == const_name)
            .unwrap();
        assert_eq!(ty, &const_ty);
    }

    let mapping = define_pkg_const_mapping_fun(game, pkg, pkg_inst_name).unwrap();
    let args = &mapping.args;

    // takes a single argument as described here
    assert_eq!(args.len(), 1);
    assert_eq!(args[0].0, "<game-consts>");
    assert_eq!(args[0].1, game_const_pattern.sort(vec![]));
    assert_eq!(
        args[0].1,
        Sort::Other(format!("<GameConsts_{game_name}>"), vec![]),
    );

    // returns a package const
    assert_eq!(mapping.sort, pkg_const_pattern.sort(vec![]));
    assert_eq!(
        mapping.sort,
        Sort::Other(format!("<PackageConsts_{pkg_name}>"), vec![]),
    );

    let bindings = &mapping.body.bindings;
    assert_eq!(bindings.len(), 1);
    assert_eq!(bindings[0].0, "n");
}

#[test]
fn test_const_datatypes_remap_consts() {
    let pkgs = packages::parse_files(&["tiny.ssp"]);
    let game = games::parse_file("small_remap_consts.ssp", &pkgs);

    let game_name = game.name();

    let game_const_pattern = game_consts::GameConstsPattern { game_name };
    let game_const_spec = game_const_pattern.datastructure_spec(&game);

    let game_const_constructors = &game_const_spec.0;
    assert_eq!(game_const_constructors.len(), 1);
    let (_, game_const_selectors) = &game_const_constructors[0];
    assert_eq!(game_const_selectors.len(), game.consts.len());

    for GameConstsSelector { name, ty } in game_const_selectors {
        let (_, const_ty) = game
            .consts
            .iter()
            .find(|(const_name, _ty)| name == const_name)
            .unwrap();
        assert_eq!(ty, &const_ty);
    }

    let pkg_inst = &game.pkgs[0];
    let pkg_inst_name = &pkg_inst.name;
    let pkg = &pkg_inst.pkg;
    let pkg_name = &pkg.name;
    let pkg = &pkgs[pkg_name];

    let pkg_const_pattern = pkg_consts::PackageConstsPattern { pkg_name };
    let pkg_const_spec = pkg_const_pattern.datastructure_spec(pkg);

    let pkg_const_constructors = &pkg_const_spec.0;
    assert_eq!(pkg_const_constructors.len(), 1);
    let (_, pkg_const_selectors) = &pkg_const_constructors[0];
    assert_eq!(pkg_const_selectors.len(), 1);

    for PackageConstsSelector { name, ty } in pkg_const_selectors {
        let (_, const_ty, _) = pkg
            .params
            .iter()
            .find(|(const_name, _ty, _)| name == const_name)
            .unwrap();
        assert_eq!(ty, &const_ty);
    }

    let mapping = define_pkg_const_mapping_fun(&game, pkg, pkg_inst_name).unwrap();
    let args = &mapping.args;

    // takes a single argument as described here
    assert_eq!(args.len(), 1);
    assert_eq!(args[0].0, "<game-consts>");
    assert_eq!(args[0].1, game_const_pattern.sort(vec![]));
    assert_eq!(
        SmtExpr::Atom(format!("<GameConsts_{game_name}>")),
        args[0].1.clone().into(),
    );

    // returns a package const
    assert_eq!(mapping.sort, pkg_const_pattern.sort(vec![]));
    assert_eq!(
        mapping.sort,
        Sort::Other(format!("<PackageConsts_{pkg_name}>"), vec![]),
    );

    let bindings = &mapping.body.bindings;

    println!("bindings: {bindings:?}");
    assert!(bindings.is_empty());

    let constructor = &mapping.body.body;
    println!("body: {:?}", mapping.body.body);
    let SmtExpr::List(constructor_list) = constructor else {
        panic!("expected list in body, got {constructor}")
    };

    assert_eq!(constructor_list.len(), 2);
    assert_eq!(constructor_list[0].to_string(), "<mk-pkg-consts-TinyPkg>");
    assert_eq!(constructor_list[1].to_string(), "1");
}

#[test]
fn test_state_datatypes_remap_consts() {
    let pkgs = packages::parse_files(&["PRF.pkg.ssp", "KeyReal.pkg.ssp"]);
    let games = games::parse_files(&["small_PRF.ssp"], &pkgs);
    let theorem_file_name = "simple-SmallPRFGame.ssp";
    let theorem_file = theorems::read_file(theorem_file_name);
    let theorem = theorems::parse(&theorem_file, theorem_file_name, &pkgs, &games);

    // check prf package instance

    let pkg_inst = &theorem.instances[0]
        .game()
        .pkgs
        .iter()
        .find(|pkg_inst| pkg_inst.name == "prf")
        .unwrap();
    let pkg = &pkg_inst.pkg;

    assert_eq!(pkg.state.len(), 1);

    let pkg_name = &pkg.name;
    let pkg = &pkgs[pkg_name];
    let params = &pkg_inst.params;

    let pkg_state_pattern = pkg_state::PackageStatePattern { pkg_name, params };
    let pkg_state_spec = pkg_state_pattern.datastructure_spec(pkg);

    let pkg_state_constructors = &pkg_state_spec.0;
    assert_eq!(pkg_state_constructors.len(), 1);
    let (_, pkg_state_selectors) = &pkg_state_constructors[0];
    assert_eq!(pkg_state_selectors.len(), 1);

    let PackageStateSelector { ty, .. } = &pkg_state_selectors[0];
    let (name, state_ty, _) = &pkg.state[0];

    println!("state entry {name:?} {ty:?} {state_ty:?}");
    assert_eq!(ty, &state_ty);

    assert_eq!(
        pkg_state_pattern.constructor_name(&()),
        "<mk-pkg-state-PRF-<$<!n!>$>>"
    );

    // check key package instance

    let pkg_inst = &theorem.instances[0]
        .game()
        .pkgs
        .iter()
        .find(|pkg_inst| pkg_inst.name == "key")
        .unwrap();
    let pkg = &pkg_inst.pkg;

    assert_eq!(pkg.state.len(), 1);

    let pkg_name = &pkg.name;
    let params = &pkg_inst.params;

    let pkg_state_pattern = pkg_state::PackageStatePattern { pkg_name, params };
    let pkg_state_spec = pkg_state_pattern.datastructure_spec(pkg);

    let pkg_state_constructors = &pkg_state_spec.0;
    assert_eq!(pkg_state_constructors.len(), 1);
    let (_, pkg_state_selectors) = &pkg_state_constructors[0];
    assert_eq!(pkg_state_selectors.len(), 1);

    let PackageStateSelector { ty, .. } = &pkg_state_selectors[0];
    let (name, state_ty, _) = &pkg.state[0];

    println!("state entry {name:?} {ty:?} {state_ty:?}");
    assert_eq!(ty, &state_ty);

    assert_eq!(
        pkg_state_pattern.constructor_name(&()),
        "<mk-pkg-state-KeyReal-<$<!n!>$>>"
    );

    println!("{}", declare_datatype(&pkg_state_pattern, &pkg_state_spec));
}

#[test]
fn test_fully_resolved_idents_103() {
    let pkgs = packages::parse_files(&["TrivialA.ssp"]);
    let games = games::parse_files(&["TrivialB.ssp"], &pkgs);
    let theorem_file_name = "TrivialC.ssp";
    let theorem_file = theorems::read_file(theorem_file_name);
    let theorem = theorems::parse(&theorem_file, theorem_file_name, &pkgs, &games);

    for game_inst in &theorem.instances {
        for (_, ty) in &game_inst.game.consts {
            if let Type::Bits(cs) = ty {
                match &**cs {
                    CountSpec::Identifier(identifier) => {
                        assert!(identifier.as_theorem_identifier().is_some())
                    }
                    CountSpec::Literal(_) => (),
                    CountSpec::Any => (),
                }
            }
        }
        for package_inst in &game_inst.game.pkgs {
            for (_, ty, _) in &package_inst.pkg.params {
                if let Type::Bits(cs) = ty {
                    match &**cs {
                        CountSpec::Identifier(identifier) => {
                            assert!(identifier.as_theorem_identifier().is_some())
                        }
                        CountSpec::Literal(_) => (),
                        CountSpec::Any => (),
                    }
                }
            }
        }
    }
}
