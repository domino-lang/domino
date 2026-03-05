use super::EquivalenceContext;
use crate::package::Export;
use crate::packageinstance::PackageInstance;
use crate::theorem::GameInstance;
use crate::transforms::samplify::SampleInfo;
use crate::util::smtparser::SmtParser;
use crate::writers::smt::exprs::SmtExpr;
use crate::writers::smt::exprs::SmtLet;
use crate::writers::smt::patterns;
use crate::writers::smt::patterns::datastructures::DatastructurePattern;

use super::error::{Error, Result};
use itertools::Itertools;

struct SmtRewrite<'a> {
    context: &'a EquivalenceContext<'a>,
    content: Vec<SmtExpr>,
}

impl<'a> SmtRewrite<'a> {
    fn new(context: &'a EquivalenceContext) -> Self {
        Self {
            context,
            content: Vec::new(),
        }
    }
}

fn gen_returnbinding(
    game: &GameInstance,
    return_value: &str,
    export: &Export,
) -> Vec<(String, SmtExpr)> {
    let pkginst = &game.game().pkgs[export.to()];
    let pattern = patterns::ReturnPattern {
        game_name: &game.game().name,
        game_params: &game.consts,
        pkg_name: &pkginst.pkg.name,
        pkg_params: &pkginst.params,
        oracle_name: &export.sig().name,
    };
    let spec = pattern.datastructure_spec(&export.sig().ty);
    let (_, selectors) = &spec.0[0];

    selectors
        .iter()
        .map(|sel| match sel {
            patterns::ReturnSelector::GameState => (
                format!("{return_value}.state"),
                (pattern.selector_name(sel), return_value).into(),
            ),
            patterns::ReturnSelector::ReturnValueOrAbort { .. } => (
                format!("{return_value}.value"),
                (pattern.selector_name(sel), return_value).into(),
            ),
        })
        .collect()
}

fn gen_pkgbinding(game: &GameInstance, game_state: &str) -> Vec<(String, SmtExpr)> {
    let pattern = patterns::GameStatePattern {
        game_name: game.game_name(),
        params: &game.consts,
    };
    let info = patterns::GameStateDeclareInfo {
        game_inst: game,
        sample_info: &SampleInfo {
            tys: Vec::new(),
            count: 0,
            positions: Vec::new(),
        },
    };

    let spec = pattern.datastructure_spec(&info);
    let (_, selectors) = &spec.0[0];

    selectors
        .iter()
        .filter_map(|sel| match sel {
            patterns::GameStateSelector::Randomness { .. } => None,
            patterns::GameStateSelector::PackageInstance { pkg_inst_name, .. } => Some((
                format!("{game_state}.{pkg_inst_name}"),
                (pattern.selector_name(sel), game_state).into(),
            )),
        })
        .collect()
}

fn gen_varbinding(package: &PackageInstance, package_state: &str) -> Vec<(String, SmtExpr)> {
    let pattern = patterns::PackageStatePattern {
        pkg_name: package.pkg_name(),
        params: &package.params,
    };

    let spec = pattern.datastructure_spec(&package.pkg);
    let (_, selectors) = &spec.0[0];

    selectors
        .iter()
        .map(|sel| {
            let varname = sel.name;
            (
                format!("{package_state}.{varname}"),
                (pattern.selector_name(sel), package_state).into(),
            )
        })
        .collect()
}

impl SmtParser<SmtExpr, Error> for SmtRewrite<'_> {
    fn handle_atom(&mut self, content: &str) -> Result<SmtExpr> {
        Ok(SmtExpr::Atom(content.to_string()))
    }

    fn handle_list(&mut self, content: Vec<SmtExpr>) -> Result<SmtExpr> {
        Ok(SmtExpr::List(content))
    }

    fn handle_sexp(&mut self, parsed: SmtExpr) -> Result<()> {
        self.content.push(parsed);
        Ok(())
    }

    fn handle_define_state_relation(
        &mut self,
        funname: &str,
        args: Vec<SmtExpr>,
        body: SmtExpr,
    ) -> Result<SmtExpr> {
        let left_game_inst = self
            .context
            .theorem
            .find_game_instance(&self.context.equivalence.left_name)
            .unwrap();
        let right_game_inst = self
            .context
            .theorem
            .find_game_instance(&self.context.equivalence.right_name)
            .unwrap();

        let [SmtExpr::List(left_arg), SmtExpr::List(right_arg)] = &args[..] else {
            return Err(Error::IncorrectNumberOfArguments {
                argument: format!(
                    "({})",
                    args.iter().map(|sexpr| format!("{sexpr}")).join(" ")
                ),
                expected: "2".to_string(),
            });
        };
        let [left_arg_name, _left_arg_type] = &left_arg[..] else {
            return Err(Error::IncorrectArgument {
                argument: format!(
                    "({})",
                    left_arg.iter().map(|sexpr| format!("{sexpr}")).join(" ")
                ),
            });
        };
        let [right_arg_name, _right_arg_type] = &right_arg[..] else {
            return Err(Error::IncorrectArgument {
                argument: format!(
                    "({})",
                    left_arg.iter().map(|sexpr| format!("{sexpr}")).join(" ")
                ),
            });
        };

        let mut pkgbindings = Vec::new();
        pkgbindings.extend(gen_pkgbinding(left_game_inst, &format!("{left_arg_name}")));
        pkgbindings.extend(gen_pkgbinding(
            right_game_inst,
            &format!("{right_arg_name}"),
        ));

        let mut varbindings = Vec::new();
        varbindings.extend(
            left_game_inst
                .game
                .pkgs
                .iter()
                .flat_map(|pkg| gen_varbinding(pkg, &format!("{left_arg_name}.{}", pkg.name))),
        );
        varbindings.extend(
            right_game_inst
                .game
                .pkgs
                .iter()
                .flat_map(|pkg| gen_varbinding(pkg, &format!("{right_arg_name}.{}", pkg.name))),
        );

        let bindvars = SmtLet {
            bindings: varbindings,
            body,
        };

        let bindpackages = SmtLet {
            bindings: pkgbindings,
            body: bindvars,
        };
        self.handle_definefun(funname, args, "Bool", bindpackages.into())
    }

    fn handle_define_lemma(
        &mut self,
        funname: &str,
        args: Vec<SmtExpr>,
        body: SmtExpr,
    ) -> Result<SmtExpr> {
        let left_game_inst = self
            .context
            .theorem
            .find_game_instance(&self.context.equivalence.left_name)
            .unwrap();
        let right_game_inst = self
            .context
            .theorem
            .find_game_instance(&self.context.equivalence.right_name)
            .unwrap();

        let Some(oracle_name) = funname
            .rfind("-")
            .map(|i| &funname[i + 1..funname.len() - 1])
        else {
            return Err(Error::IllegalLemmaName {
                lemma_name: funname.to_string(),
            });
        };

        let Some(oracle_export) = left_game_inst
            .game()
            .exports
            .iter()
            .find(|export| export.sig().name == oracle_name)
        else {
            return Err(Error::UnknownLemmaName {
                lemma_name: funname.to_string(),
                oracle_name: oracle_name.to_string(),
            });
        };

        let [SmtExpr::List(left_old), SmtExpr::List(right_old), SmtExpr::List(left_return), SmtExpr::List(right_return), ..] =
            &args[..]
        else {
            return Err(Error::IncorrectNumberOfArguments {
                argument: format!(
                    "({})",
                    args.iter().map(|sexpr| format!("{sexpr}")).join(" ")
                ),
                expected: "at least 4".to_string(),
            });
        };
        let [left_old_name, _left_old_type] = &left_old[..] else {
            return Err(Error::IncorrectArgument {
                argument: format!(
                    "({})",
                    left_old.iter().map(|sexpr| format!("{sexpr}")).join(" ")
                ),
            });
        };
        let [right_old_name, _right_old_type] = &right_old[..] else {
            return Err(Error::IncorrectArgument {
                argument: format!(
                    "({})",
                    right_old.iter().map(|sexpr| format!("{sexpr}")).join(" ")
                ),
            });
        };
        let [left_return_name, _left_return_type] = &left_return[..] else {
            return Err(Error::IncorrectArgument {
                argument: format!(
                    "({})",
                    left_return.iter().map(|sexpr| format!("{sexpr}")).join(" ")
                ),
            });
        };
        let [right_return_name, _right_return_type] = &right_return[..] else {
            return Err(Error::IncorrectArgument {
                argument: format!(
                    "({})",
                    right_return
                        .iter()
                        .map(|sexpr| format!("{sexpr}"))
                        .join(" ")
                ),
            });
        };

        let mut retbindings = Vec::new();
        retbindings.extend(gen_returnbinding(
            left_game_inst,
            &format!("{left_return_name}"),
            oracle_export,
        ));
        retbindings.extend(gen_returnbinding(
            right_game_inst,
            &format!("{right_return_name}"),
            oracle_export,
        ));

        let mut pkgbindings = Vec::new();
        pkgbindings.extend(gen_pkgbinding(left_game_inst, &format!("{left_old_name}")));
        pkgbindings.extend(gen_pkgbinding(
            left_game_inst,
            &format!("{left_return_name}.state"),
        ));
        pkgbindings.extend(gen_pkgbinding(
            right_game_inst,
            &format!("{right_old_name}"),
        ));
        pkgbindings.extend(gen_pkgbinding(
            right_game_inst,
            &format!("{right_return_name}.state"),
        ));

        let mut varbindings = Vec::new();
        varbindings.extend(
            left_game_inst
                .game
                .pkgs
                .iter()
                .flat_map(|pkg| gen_varbinding(pkg, &format!("{left_old_name}.{}", pkg.name))),
        );
        varbindings.extend(left_game_inst.game.pkgs.iter().flat_map(|pkg| {
            gen_varbinding(pkg, &format!("{left_return_name}.state.{}", pkg.name))
        }));
        varbindings.extend(
            right_game_inst
                .game
                .pkgs
                .iter()
                .flat_map(|pkg| gen_varbinding(pkg, &format!("{right_old_name}.{}", pkg.name))),
        );
        varbindings.extend(right_game_inst.game.pkgs.iter().flat_map(|pkg| {
            gen_varbinding(pkg, &format!("{right_return_name}.state.{}", pkg.name))
        }));

        let bindvars = SmtLet {
            bindings: varbindings,
            body,
        };

        let bindpackages = SmtLet {
            bindings: pkgbindings,
            body: bindvars,
        };
        let bindreturn = SmtLet {
            bindings: retbindings,
            body: bindpackages,
        };
        self.handle_definefun(funname, args, "Bool", bindreturn.into())
    }
}

pub fn rewrite(context: &EquivalenceContext, content: &str) -> Result<Vec<SmtExpr>> {
    let mut rewriter: SmtRewrite = SmtRewrite::new(context);
    rewriter.parse_sexps(content)?;
    Ok(rewriter.content)
}
