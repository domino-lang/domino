// SPDX-License-Identifier: MIT OR Apache-2.0

//! Builds the synthetic game that a package invariant is proved against.
//!
//! A package invariant is a property of a single package `P`, and it should be proved once, for
//! arbitrary package constants, instead of once per instance of `P` in every game of every
//! theorem. To do that we need to give `P` an environment: `P` may import oracles, and those
//! imported oracles may be stateful and may share state with each other.
//!
//! We model that environment by a *virtual package* `V`:
//!
//!  * `V` exposes exactly the oracles that `P` imports, so `P` composed with `V` is a closed game.
//!  * `V` has a single state variable of type `Bits(*)`, which stands for an arbitrary encoding of
//!    whatever state the real environment keeps. A single variable is enough (and necessary):
//!    imported oracles may share state, either because they come from the same package or because
//!    the packages they come from call a common package.
//!  * Each oracle of `V` is implemented by an uninterpreted function of the same name, taking the
//!    environment state and the oracle arguments, and returning
//!    `Maybe((Bits(*), <return type>))`. `None` means the imported oracle aborts; otherwise the
//!    pair is unwrapped into the new environment state and the value that is returned.
//!
//! Because the function is uninterpreted and the state is an arbitrary bit string, every behaviour
//! a real environment could exhibit -- including returning different values for the same arguments
//! -- is covered.
//!
//! The result is a normal [`Theorem`] with a single [`GameInstance`], so the existing translation
//! of oracle bodies to SMT applies unchanged.

use miette::SourceSpan;

use crate::{
    expressions::{Expression, ExpressionKind},
    identifier::{
        game_ident::{GameConstIdentifier, GameIdentifier},
        pkg_ident::{
            PackageConstIdentifier, PackageIdentifier, PackageLocalIdentifier,
            PackageStateIdentifier,
        },
        theorem_ident::TheoremConstIdentifier,
        Identifier,
    },
    package::{Composition, Edge, Export, OracleDef, OracleSig, Package, PackageInstance},
    statement::{Assignment, AssignmentRhs, CodeBlock, Pattern, Statement},
    theorem::{GameInstance, Theorem},
    types::{CountSpec, Type, TypeKind},
};

/// The name of the single state variable of the virtual package.
const VIRTUAL_STATE_VAR: &str = "virtual$state";

/// The name of the local variable holding the (still wrapped) result of the virtual function.
const VIRTUAL_RESULT_VAR: &str = "virtual$result";

/// The name of the local variable holding the value the virtual oracle returns.
const VIRTUAL_VALUE_VAR: &str = "virtual$value";

/// A synthetic theorem that consists of a single game: the package under scrutiny, composed with
/// the virtual package modelling the oracles it imports.
pub(crate) struct VirtualGame<'a> {
    theorem: Theorem<'a>,
    game_inst_name: String,
    pkg_inst_name: String,
}

impl<'a> VirtualGame<'a> {
    /// Builds the synthetic theorem for `pkg`.
    pub(crate) fn new(pkg: &Package) -> Self {
        let pkg_name = pkg.name.clone();
        let imports = sorted_imports(pkg);
        let theorem_name = format!("{pkg_name}$Invariant");
        let game_name = theorem_name.clone();
        let game_inst_name = theorem_name.clone();
        let pkg_inst_name = pkg_name.clone();
        let virtual_pkg_name = format!("{pkg_name}$Env");
        let virtual_pkg_inst_name = virtual_pkg_name.clone();

        // ---- the constants of the synthetic game ------------------------------------------
        //
        // The game has one constant per package parameter of `P` (so the invariant is proved for
        // arbitrary package constants) plus one constant per imported oracle, holding the
        // uninterpreted function that implements it.
        let mut game_consts: Vec<(String, Type)> = pkg
            .params
            .iter()
            .map(|(name, ty, _)| {
                (
                    name.clone(),
                    lift_type(ty, &pkg_name, Level::Game(&game_name)),
                )
            })
            .collect();

        // an imported oracle and a package parameter can never share a name -- they live in the
        // same scope -- so we can name the constant holding the uninterpreted function after the
        // oracle it implements.
        for sig in &imports {
            game_consts.push((
                sig.name.clone(),
                virtual_fn_type(&lift_oracle_sig(sig, &pkg_name, Level::Game(&game_name))),
            ));
        }
        game_consts.sort();

        // ---- the virtual package ----------------------------------------------------------
        let virtual_pkg = build_virtual_package(pkg, &virtual_pkg_name, &imports);

        // ---- instantiate both packages into the game --------------------------------------
        let pkg_inst = PackageInstance::new(
            &pkg_inst_name,
            &game_name,
            pkg,
            game_const_assignments(&pkg.params, &pkg_name, &game_name, &game_consts),
            vec![],
        );
        let virtual_pkg_inst = PackageInstance::new(
            &virtual_pkg_inst_name,
            &game_name,
            &virtual_pkg,
            game_const_assignments(
                &virtual_pkg.params,
                &virtual_pkg_name,
                &game_name,
                &game_consts,
            ),
            vec![],
        );

        const PKG_OFFS: usize = 0;
        const VIRTUAL_OFFS: usize = 1;

        // wire every oracle `P` imports up with the virtual package
        let edges = virtual_pkg_inst
            .pkg
            .oracles
            .iter()
            .map(|odef| {
                let sig = virtual_pkg_inst.instantiate_oracle_signature(odef.sig.clone());
                Edge::new(PKG_OFFS, VIRTUAL_OFFS, sig, None)
            })
            .collect();

        // and export every oracle `P` offers, so we can check the invariant for each of them
        let exports = pkg_inst
            .pkg
            .oracles
            .iter()
            .map(|odef| {
                let sig = pkg_inst.instantiate_oracle_signature(odef.sig.clone());
                Export::new(PKG_OFFS, sig, None)
            })
            .collect();

        let game = Composition {
            pkgs: vec![pkg_inst, virtual_pkg_inst],
            edges,
            exports,
            name: game_name.clone(),
            consts: game_consts.clone(),
            invariants: vec![],
        };

        // ---- lift the game constants to theorem constants ---------------------------------
        let theorem_consts: Vec<(String, Type)> = game_consts
            .iter()
            .map(|(name, ty)| {
                (
                    name.clone(),
                    lift_type(ty, &game_name, Level::Theorem(&theorem_name)),
                )
            })
            .collect();

        let game_inst_consts: Vec<(GameConstIdentifier, Expression)> = game_consts
            .iter()
            .zip(&theorem_consts)
            .map(|((name, game_ty), (_, theorem_ty))| {
                let game_const = GameConstIdentifier {
                    game_name: game_name.clone(),
                    name: name.clone(),
                    ty: game_ty.clone(),
                    game_inst_name: None,
                    theorem_name: None,
                    inst_info: None,
                    assigned_value: None,
                };

                let theorem_const = TheoremConstIdentifier {
                    theorem_name: theorem_name.clone(),
                    name: name.clone(),
                    ty: theorem_ty.clone(),
                    inst_info: None,
                };

                (
                    game_const,
                    Expression::from(Identifier::from(theorem_const)),
                )
            })
            .collect();

        let game_inst = GameInstance::new(
            game_inst_name.clone(),
            theorem_name.clone(),
            game,
            vec![],
            game_inst_consts,
        );

        let theorem = Theorem {
            name: theorem_name,
            consts: theorem_consts,
            instances: vec![game_inst],
            assumptions: vec![],
            proofs: vec![],
            game_hops: vec![],
            pkgs: vec![pkg.clone(), virtual_pkg],
        };

        Self {
            theorem,
            game_inst_name,
            pkg_inst_name,
        }
    }

    pub(crate) fn theorem(&self) -> &Theorem<'a> {
        &self.theorem
    }

    pub(crate) fn game_inst(&self) -> &GameInstance {
        &self.theorem.instances[0]
    }

    pub(crate) fn game_inst_name(&self) -> &str {
        &self.game_inst_name
    }

    /// The name the package under scrutiny is instantiated under in the synthetic game.
    pub(crate) fn pkg_inst_name(&self) -> &str {
        &self.pkg_inst_name
    }
}

/// `(Bits(*), <args>) -> Maybe((Bits(*), <return type>))`
fn virtual_fn_type(sig: &OracleSig) -> Type {
    let mut arg_types = vec![environment_state_type()];
    arg_types.extend(sig.args.iter().map(|(_, ty)| ty.clone()));

    Type::fun(
        arg_types,
        Type::maybe(Type::tuple(vec![environment_state_type(), sig.ty.clone()])),
    )
}

/// The type of the virtual package's state: an arbitrary bit string.
fn environment_state_type() -> Type {
    Type::bits(CountSpec::Any)
}

fn dummy_span() -> SourceSpan {
    (0..0).into()
}

/// Builds the virtual package exposing the oracles `pkg` imports.
fn build_virtual_package(pkg: &Package, virtual_pkg_name: &str, imports: &[OracleSig]) -> Package {
    // The virtual package needs the parameters of `pkg`, because the signatures of the imported
    // oracles may mention them (e.g. as the length in `Bits(n)`).
    let mut params: Vec<(String, Type, SourceSpan)> = pkg
        .params
        .iter()
        .map(|(name, ty, span)| {
            (
                name.clone(),
                lift_type(ty, &pkg.name, Level::Package(virtual_pkg_name)),
                *span,
            )
        })
        .collect();

    let mut oracles = Vec::with_capacity(imports.len());

    for sig in imports {
        let sig = lift_oracle_sig(sig, &pkg.name, Level::Package(virtual_pkg_name));
        params.push((sig.name.clone(), virtual_fn_type(&sig), dummy_span()));
        oracles.push(build_virtual_oracle(virtual_pkg_name, sig));
    }

    params.sort();

    Package {
        name: virtual_pkg_name.to_string(),
        types: vec![],
        params,
        state: vec![(
            VIRTUAL_STATE_VAR.to_string(),
            environment_state_type(),
            dummy_span(),
        )],
        oracles,
        imports: vec![],
        invariants: vec![],
        file_name: pkg.file_name.clone(),
        file_contents: pkg.file_contents.clone(),
    }
}

/// Builds the body of one virtual oracle:
///
/// ```text
/// oracle Foo(x: T) -> U {
///     virtual$result <- Foo(virtual$state, x);        // Maybe((Bits(*), U))
///     (virtual$state, virtual$value) <- Unwrap(virtual$result);
///     return virtual$value;
/// }
/// ```
///
/// The `Unwrap` is what makes the oracle abort when the uninterpreted function returns `None`.
fn build_virtual_oracle(virtual_pkg_name: &str, sig: OracleSig) -> OracleDef {
    let oracle_name = sig.name.clone();
    let returns_value = !matches!(sig.ty.kind(), TypeKind::Empty);

    let state_ident = Identifier::from(PackageStateIdentifier {
        pkg_name: virtual_pkg_name.to_string(),
        name: VIRTUAL_STATE_VAR.to_string(),
        ty: environment_state_type(),
        pkg_inst_name: None,
        game_name: None,
        game_inst_name: None,
        theorem_name: None,
    });

    let local = |name: &str, ty: Type| {
        Identifier::PackageIdentifier(PackageIdentifier::Local(PackageLocalIdentifier {
            pkg_name: virtual_pkg_name.to_string(),
            oracle_name: oracle_name.clone(),
            name: name.to_string(),
            ty,
            pkg_inst_name: None,
            game_name: None,
            game_inst_name: None,
            theorem_name: None,
        }))
    };

    let unwrapped_type = Type::tuple(vec![environment_state_type(), sig.ty.clone()]);
    let result_ident = local(VIRTUAL_RESULT_VAR, Type::maybe(unwrapped_type));
    let value_ident = local(VIRTUAL_VALUE_VAR, sig.ty.clone());

    let fn_ident = Identifier::from(PackageConstIdentifier::new(
        oracle_name.clone(),
        virtual_pkg_name.to_string(),
        virtual_fn_type(&sig),
    ));

    let mut call_args = vec![Expression::from(state_ident.clone())];
    call_args.extend(sig.args.iter().map(|(name, ty)| {
        Expression::from(Identifier::PackageIdentifier(PackageIdentifier::OracleArg(
            crate::identifier::pkg_ident::PackageOracleArgIdentifier {
                pkg_name: virtual_pkg_name.to_string(),
                oracle_name: oracle_name.clone(),
                name: name.clone(),
                ty: ty.clone(),
                pkg_inst_name: None,
                game_name: None,
                game_inst_name: None,
                theorem_name: None,
            },
        )))
    }));

    let call = Expression::from_kind(ExpressionKind::FnCall(fn_ident, call_args));

    let unwrap = Expression::from_kind(ExpressionKind::Unwrap(Box::new(Expression::from(
        result_ident.clone(),
    ))));

    let code = CodeBlock(vec![
        Statement::Assignment(
            Assignment {
                pattern: Pattern::Ident(result_ident),
                rhs: AssignmentRhs::Expression(call),
            },
            dummy_span(),
        ),
        Statement::Assignment(
            Assignment {
                pattern: Pattern::Tuple(vec![state_ident, value_ident.clone()]),
                rhs: AssignmentRhs::Expression(unwrap),
            },
            dummy_span(),
        ),
        Statement::Return(
            returns_value.then(|| Expression::from(value_ident)),
            dummy_span(),
        ),
    ]);

    OracleDef {
        sig,
        code,
        file_pos: dummy_span(),
    }
}

/// Assigns each parameter of a package the game constant of the same name.
fn game_const_assignments(
    params: &[(String, Type, SourceSpan)],
    pkg_name: &str,
    game_name: &str,
    game_consts: &[(String, Type)],
) -> Vec<(PackageConstIdentifier, Expression)> {
    let mut assignments: Vec<_> = params
        .iter()
        .map(|(name, _ty, _span)| {
            let (_, game_ty) = game_consts
                .iter()
                .find(|(game_const_name, _)| game_const_name == name)
                .unwrap_or_else(|| {
                    panic!("no game constant for parameter `{name}' of package `{pkg_name}'")
                });

            let value = Expression::from(Identifier::GameIdentifier(GameIdentifier::Const(
                GameConstIdentifier {
                    game_name: game_name.to_string(),
                    name: name.clone(),
                    ty: game_ty.clone(),
                    game_inst_name: None,
                    theorem_name: None,
                    inst_info: None,
                    assigned_value: None,
                },
            )));

            let ident = PackageConstIdentifier {
                pkg_name: pkg_name.to_string(),
                name: name.clone(),
                ty: value.get_type(),
                game_name: None,
                game_assignment: None,
                pkg_inst_name: None,
                game_inst_name: None,
                theorem_name: None,
            };

            (ident, value)
        })
        .collect();

    assignments.sort();
    assignments
}

/// The signatures of the oracles `pkg` imports, sorted by name.
///
/// The parser collects the imports in a hash map, so their order is not stable across runs. We
/// need a stable order here, because it decides the order of the oracles of the virtual package,
/// and with it the order of the SMT we emit.
fn sorted_imports(pkg: &Package) -> Vec<OracleSig> {
    let mut imports: Vec<OracleSig> = pkg.imports.iter().map(|(sig, _span)| sig.clone()).collect();
    imports.sort_by(|left, right| left.name.cmp(&right.name));
    imports
}

/// The three levels constants live at. A `Bits(n)` length is spelled with a different kind of
/// identifier depending on which level the surrounding type belongs to.
#[derive(Clone, Copy)]
enum Level<'a> {
    Package(&'a str),
    Game(&'a str),
    Theorem(&'a str),
}

/// Rewrites the `Bits(<length>)` lengths in `sig` from the level of `from` to `to`.
fn lift_oracle_sig(sig: &OracleSig, from: &str, to: Level) -> OracleSig {
    OracleSig {
        name: sig.name.clone(),
        args: sig
            .args
            .iter()
            .map(|(name, ty)| (name.clone(), lift_type(ty, from, to)))
            .collect(),
        ty: lift_type(&sig.ty, from, to),
    }
}

/// Rewrites the `Bits(<length>)` lengths of `ty` to refer to the constants of `to`.
///
/// Every level (package, game, theorem) refers to its constants with its own kind of identifier,
/// and in the synthetic game we build here a constant is always assigned the constant of the same
/// name at the next level. So lifting a type just means swapping the identifier, keeping the name.
fn lift_type(ty: &Type, from: &str, to: Level) -> Type {
    let lift_all =
        |tys: &[Type]| -> Vec<Type> { tys.iter().map(|ty| lift_type(ty, from, to)).collect() };

    match ty.kind() {
        TypeKind::Bits(count_spec) => Type::bits(lift_count_spec(count_spec, from, to)),
        TypeKind::Tuple(tys) => Type::tuple(lift_all(tys)),
        TypeKind::Table(key, value) => {
            Type::table(lift_type(key, from, to), lift_type(value, from, to))
        }
        TypeKind::Fn(arg_tys, ret_ty) => Type::fun(lift_all(arg_tys), lift_type(ret_ty, from, to)),
        TypeKind::List(inner) => Type::list(lift_type(inner, from, to)),
        TypeKind::Set(inner) => Type::set(lift_type(inner, from, to)),
        TypeKind::Maybe(inner) => Type::maybe(lift_type(inner, from, to)),
        _ => ty.clone(),
    }
}

fn lift_count_spec(count_spec: &CountSpec, from: &str, to: Level) -> CountSpec {
    let CountSpec::Identifier(ident) = count_spec else {
        return count_spec.clone();
    };

    // only rewrite constants that belong to the level we are lifting away from
    let name = match ident.as_ref() {
        Identifier::PackageIdentifier(PackageIdentifier::Const(pkg_const))
            if pkg_const.pkg_name == from =>
        {
            &pkg_const.name
        }
        Identifier::GameIdentifier(GameIdentifier::Const(game_const))
            if game_const.game_name == from =>
        {
            &game_const.name
        }
        _ => return count_spec.clone(),
    };

    let lifted = match to {
        Level::Package(pkg_name) => Identifier::from(PackageConstIdentifier::new(
            name.clone(),
            pkg_name.to_string(),
            Type::integer(),
        )),
        Level::Game(game_name) => {
            Identifier::GameIdentifier(GameIdentifier::Const(GameConstIdentifier {
                game_name: game_name.to_string(),
                name: name.clone(),
                ty: Type::integer(),
                game_inst_name: None,
                theorem_name: None,
                inst_info: None,
                assigned_value: None,
            }))
        }
        Level::Theorem(theorem_name) => Identifier::from(TheoremConstIdentifier {
            theorem_name: theorem_name.to_string(),
            name: name.clone(),
            ty: Type::integer(),
            inst_info: None,
        }),
    };

    CountSpec::Identifier(Box::new(lifted))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::tests::packages;

    const CTR: &str = r#"
package Ctr {
    params {
        n: Integer,
    }

    state {
        ctr: Integer,
    }

    import oracles {
        Get(x: Integer) -> Bits(n),
        Put(y: Bits(n)),
    }

    oracle Step(x: Integer) -> Bits(n) {
        y <- invoke Get(x);
        ctr <- (ctr + 1);
        return y;
    }

    oracle Peek() -> Integer {
        return ctr;
    }
}
"#;

    const NO_IMPORTS: &str = r#"
package Closed {
    params {
        n: Integer,
    }

    state {
        ctr: Integer,
    }

    oracle Peek() -> Integer {
        return ctr;
    }
}
"#;

    #[test]
    fn virtual_package_exposes_exactly_the_imported_oracles() {
        let (_, pkg) = packages::parse(CTR.trim_start(), "Ctr.pkg.ssp");
        let virtual_game = VirtualGame::new(&pkg);
        let game = virtual_game.game_inst().game();

        assert_eq!(game.pkgs.len(), 2, "the package and its environment");

        let env = &game.pkgs[1];
        let env_oracle_names: Vec<&str> = env
            .pkg
            .oracles
            .iter()
            .map(|odef| odef.sig.name.as_str())
            .collect();

        assert_eq!(env_oracle_names, vec!["Get", "Put"]);
        assert!(
            env.pkg.imports.is_empty(),
            "the environment is the rightmost package, it imports nothing"
        );
        assert_eq!(
            env.pkg.state.len(),
            1,
            "the environment has a single state variable standing for an arbitrary encoding"
        );
    }

    #[test]
    fn every_import_is_wired_up_and_every_oracle_is_exported() {
        let (_, pkg) = packages::parse(CTR.trim_start(), "Ctr.pkg.ssp");
        let virtual_game = VirtualGame::new(&pkg);
        let game = virtual_game.game_inst().game();

        assert_eq!(game.edges.len(), pkg.imports.len());
        assert!(
            game.edges
                .iter()
                .all(|edge| edge.from() == 0 && edge.to() == 1),
            "every import points from the package under scrutiny at the environment"
        );

        let exported: Vec<&str> = game.exports.iter().map(|export| export.name()).collect();
        assert_eq!(exported, vec!["Step", "Peek"]);
    }

    #[test]
    fn the_package_keeps_its_own_name_as_the_instance_name() {
        let (_, pkg) = packages::parse(CTR.trim_start(), "Ctr.pkg.ssp");
        let virtual_game = VirtualGame::new(&pkg);

        assert_eq!(virtual_game.pkg_inst_name(), "Ctr");
        assert_eq!(virtual_game.game_inst().game().pkgs[0].name, "Ctr");
    }

    #[test]
    fn the_package_constants_become_theorem_constants() {
        let (_, pkg) = packages::parse(CTR.trim_start(), "Ctr.pkg.ssp");
        let virtual_game = VirtualGame::new(&pkg);

        let const_names: Vec<&str> = virtual_game
            .theorem()
            .consts
            .iter()
            .map(|(name, _)| name.as_str())
            .collect();

        // `n` is the package parameter, `Get` and `Put` hold the uninterpreted functions
        // implementing the imported oracles
        assert_eq!(const_names, vec!["Get", "Put", "n"]);
    }

    #[test]
    fn a_package_without_imports_gets_an_empty_environment() {
        let (_, pkg) = packages::parse(NO_IMPORTS.trim_start(), "Closed.pkg.ssp");
        let virtual_game = VirtualGame::new(&pkg);
        let game = virtual_game.game_inst().game();

        assert!(game.edges.is_empty());
        assert!(game.pkgs[1].pkg.oracles.is_empty());
    }
}
