use miette::Diagnostic;
use thiserror::Error;

use super::EquivalenceContext;
use crate::package::Export;
use crate::packageinstance::PackageInstance;
use crate::theorem::GameInstance;
use crate::transforms::samplify::SampleInfo;
use crate::util::smtparser::SmtParser;
use crate::writers::smt::contexts::GameInstanceContext;
use crate::writers::smt::exprs::SmtExpr;
use crate::writers::smt::exprs::SmtLet;
use crate::writers::smt::patterns;
use crate::writers::smt::patterns::datastructures::DatastructurePattern;

use crate::gamehops::equivalence::error::{Error, Result};
use itertools::Itertools;

#[derive(Error, Diagnostic, Debug)]
#[error("custom smt in invariant file:\n{expr}")]
#[diagnostic(code(domino::theorem::custom_smt), severity(Warning))]
pub struct CustomSmtWarning {
    pub expr: SmtExpr,
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum SmtStatementSort {
    StateRelation,
    GeneralRelation,
    PackageInvariant,
    GameInvariant,
    Function,
    Other,
}

#[derive(Clone, Debug)]
pub struct SmtStmt {
    pub sort: SmtStatementSort,
    pub name: String,
    pub expr: SmtExpr,
}

#[derive(Clone, Debug)]
enum SmtObject {
    Statement(SmtStmt),
    Expression(SmtExpr),
}

impl std::fmt::Display for SmtObject {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SmtObject::Expression(e) => write!(f, "{e}"),
            _ => todo!(),
        }
    }
}

impl SmtObject {
    fn as_expression(&self) -> Option<&SmtExpr> {
        match self {
            SmtObject::Expression(e) => Some(e),
            _ => None,
        }
    }
}

struct SmtRewrite<'a> {
    context: &'a EquivalenceContext<'a>,
    package: Option<&'a PackageInstance>,
    game: Option<&'a GameInstance>,
    content: Vec<SmtStmt>,
}

impl<'a> SmtRewrite<'a> {
    fn new(context: &'a EquivalenceContext) -> Self {
        Self {
            context,
            package: None,
            game: None,
            content: Vec::new(),
        }
    }

    fn new_with_game(context: &'a EquivalenceContext, game: &'a GameInstance) -> Self {
        Self {
            context,
            package: None,
            game: Some(game),
            content: Vec::new(),
        }
    }

    fn new_with_package(
        context: &'a EquivalenceContext,
        game: &'a GameInstance,
        package: &'a PackageInstance,
    ) -> Self {
        Self {
            context,
            package: Some(package),
            game: Some(game),
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
        sample_info: &SampleInfo::default(),
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

impl SmtRewrite<'_> {
    fn equivalence_name(&self) -> String {
        format!(
            "{} = {}",
            self.context.equivalence().left_name,
            self.context.equivalence().right_name
        )
    }
}

impl SmtParser<SmtObject, Error> for SmtRewrite<'_> {
    fn handle_atom(&mut self, content: &str) -> Result<SmtObject> {
        Ok(SmtObject::Expression(SmtExpr::Atom(content.to_string())))
    }

    fn handle_list(&mut self, content: Vec<SmtObject>) -> Result<SmtObject> {
        Ok(SmtObject::Expression(SmtExpr::List(
            content
                .iter()
                .map(|smt| smt.as_expression().unwrap())
                .cloned()
                .collect(),
        )))
    }

    fn handle_sexp(&mut self, parsed: SmtObject) -> Result<()> {
        let parsed = match parsed {
            SmtObject::Statement(s) => s,
            SmtObject::Expression(expr) => {
                eprintln!(
                    "{:?}",
                    miette::Report::new(CustomSmtWarning { expr: expr.clone() })
                );
                SmtStmt {
                    expr,
                    name: String::new(),
                    sort: SmtStatementSort::Other,
                }
            }
        };

        self.content.push(parsed);
        Ok(())
    }

    fn handle_definefun(
        &mut self,
        funname: &str,
        args: Vec<SmtObject>,
        ty: &str,
        body: SmtObject,
    ) -> Result<SmtObject> {
        let SmtObject::Expression(body) = body else {
            unreachable!()
        };
        let args: Vec<_> = args
            .iter()
            .map(|smt| smt.as_expression().unwrap())
            .cloned()
            .collect();

        let expr = ("define-fun", funname, args, ty, body).into();

        Ok(SmtObject::Statement(SmtStmt {
            sort: SmtStatementSort::Function,
            name: funname.to_string(),
            expr,
        }))
    }

    fn handle_define_game_invariant(
        &mut self,
        invname: &str,
        body: SmtObject,
    ) -> Result<SmtObject> {
        let SmtObject::Expression(body) = body else {
            unreachable!()
        };

        if self.game.is_none() {
            return Err(Error::RewriteNeedsGameContext {
                defn: format!("(define-game-invariant {body})"),
            });
        }

        let gamestate_context = GameInstanceContext::new(self.game.unwrap());
        let gamestate_pattern = gamestate_context.datastructure_game_state_pattern();
        let gamestate_sort = gamestate_pattern.sort_name();

        let pkgbindings = gen_pkgbinding(self.game.unwrap(), "game");
        let varbindings: Vec<_> = self
            .game
            .unwrap()
            .game
            .pkgs
            .iter()
            .flat_map(|pkg| gen_varbinding(pkg, &format!("game.{}", pkg.name)))
            .collect();

        let bindvars = SmtLet {
            bindings: varbindings,
            body,
        };

        let bindpackages: SmtExpr = SmtLet {
            bindings: pkgbindings,
            body: bindvars,
        }
        .into();

        let name = format!("game-invariant!{invname}!{}!", self.game.unwrap().name());

        let expr = (
            "define-fun",
            &name,
            vec![(
                SmtExpr::Atom("game".to_string()),
                SmtExpr::Atom(gamestate_sort),
            )
                .into()],
            "Bool",
            bindpackages,
        )
            .into();

        Ok(SmtObject::Statement(SmtStmt {
            sort: SmtStatementSort::GameInvariant,
            name,
            expr,
        }))
    }

    fn handle_define_package_invariant(
        &mut self,
        invname: &str,
        body: SmtObject,
    ) -> Result<SmtObject> {
        let SmtObject::Expression(body) = body else {
            unreachable!()
        };

        if self.game.is_none() || self.package.is_none() {
            return Err(Error::RewriteNeedsPackageContext {
                defn: format!("(define-package-invariant {body})"),
            });
        }

        let gamestate_context = GameInstanceContext::new(self.game.unwrap());
        let gamestate_pattern = gamestate_context.datastructure_game_state_pattern();
        let gamestate_sort = gamestate_pattern.sort_name();

        let varbindings = gen_varbinding(self.package.unwrap(), "pkg");
        let bindvars = SmtLet {
            bindings: varbindings,
            body,
        };
        let bindpkg: SmtExpr = SmtLet {
            bindings: vec![(
                "pkg".to_string(),
                gamestate_context
                    .smt_access_gamestate_pkgstate("game", self.package.unwrap().name())
                    .unwrap(),
            )],
            body: bindvars,
        }
        .into();

        let name = format!(
            "package-invariant!{invname}!{}-{}!",
            self.game.unwrap().name(),
            self.package.unwrap().name()
        );

        let expr = (
            "define-fun",
            &name,
            vec![(
                SmtExpr::Atom("game".to_string()),
                SmtExpr::Atom(gamestate_sort),
            )
                .into()],
            "Bool",
            bindpkg,
        )
            .into();

        Ok(SmtObject::Statement(SmtStmt {
            sort: SmtStatementSort::PackageInvariant,
            name,
            expr,
        }))
    }

    fn handle_define_state_relation(
        &mut self,
        funname: &str,
        args: Vec<SmtObject>,
        body: SmtObject,
    ) -> Result<SmtObject> {
        let SmtObject::Expression(body) = body else {
            unreachable!()
        };

        let left_game_inst = self
            .context
            .theorem()
            .find_game_instance(&self.context.equivalence().left_name)
            .unwrap();
        let right_game_inst = self
            .context
            .theorem()
            .find_game_instance(&self.context.equivalence().right_name)
            .unwrap();
        let left_game_state_pattern = patterns::GameStatePattern {
            game_name: left_game_inst.game_name(),
            params: &left_game_inst.consts,
        };
        let right_game_state_pattern = patterns::GameStatePattern {
            game_name: right_game_inst.game_name(),
            params: &right_game_inst.consts,
        };

        let [left_arg, right_arg] = &args[..] else {
            return Err(Error::IncorrectNumberOfArguments {
                argument: format!(
                    "({})",
                    args.iter()
                        .map(|sexpr| format!("{}", sexpr.as_expression().unwrap()))
                        .join(" ")
                ),
                expected: "2".to_string(),
                equivalence: self.equivalence_name(),
            });
        };
        let SmtExpr::Atom(left_arg_name) = left_arg.as_expression().unwrap() else {
            return Err(Error::IncorrectArgument {
                argument: format!("{left_arg}",),
                equivalence: self.equivalence_name(),
            });
        };
        let SmtExpr::Atom(right_arg_name) = right_arg.as_expression().unwrap() else {
            return Err(Error::IncorrectArgument {
                argument: format!("{right_arg}",),
                equivalence: self.equivalence_name(),
            });
        };

        let mut pkgbindings = Vec::new();
        pkgbindings.extend(gen_pkgbinding(left_game_inst, left_arg_name));
        pkgbindings.extend(gen_pkgbinding(right_game_inst, right_arg_name));

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

        let bindpackages: SmtExpr = SmtLet {
            bindings: pkgbindings,
            body: bindvars,
        }
        .into();
        let expr = (
            "define-fun",
            funname,
            vec![
                (left_arg_name.clone(), left_game_state_pattern.sort_name()).into(),
                (right_arg_name.clone(), right_game_state_pattern.sort_name()).into(),
            ],
            "Bool",
            bindpackages,
        )
            .into();

        Ok(SmtObject::Statement(SmtStmt {
            sort: SmtStatementSort::StateRelation,
            name: funname.to_string(),
            expr,
        }))
    }

    fn handle_define_lemma(
        &mut self,
        funname: &str,
        args: Vec<SmtObject>,
        body: SmtObject,
    ) -> Result<SmtObject> {
        let SmtObject::Expression(body) = body else {
            unreachable!()
        };

        let left_game_inst = self
            .context
            .theorem()
            .find_game_instance(&self.context.equivalence().left_name)
            .unwrap();
        let right_game_inst = self
            .context
            .theorem()
            .find_game_instance(&self.context.equivalence().right_name)
            .unwrap();
        let left_game_state_pattern = patterns::GameStatePattern {
            game_name: left_game_inst.game_name(),
            params: &left_game_inst.consts,
        };
        let right_game_state_pattern = patterns::GameStatePattern {
            game_name: right_game_inst.game_name(),
            params: &right_game_inst.consts,
        };

        let Some(oracle_name) = funname
            .rfind("-")
            .map(|i| &funname[i + 1..funname.len() - 1])
        else {
            return Err(Error::IllegalLemmaName {
                lemma_name: funname.to_string(),
            });
        };

        let Some(left_oracle_export) = left_game_inst
            .game()
            .exports
            .iter()
            .find(|export| export.name() == oracle_name)
        else {
            return Err(Error::UnknownLemmaName {
                lemma_name: funname.to_string(),
                oracle_name: oracle_name.to_string(),
            });
        };
        let left_oracle_return_pattern = patterns::ReturnPattern {
            game_name: left_game_inst.game_name(),
            game_params: &left_game_inst.consts,
            pkg_name: &left_game_inst.game.pkgs[left_oracle_export.to()].pkg.name,
            pkg_params: &left_game_inst.game.pkgs[left_oracle_export.to()].params,
            oracle_name: &left_oracle_export.sig().name,
        };

        let Some(right_oracle_export) = right_game_inst
            .game()
            .exports
            .iter()
            .find(|export| export.name() == oracle_name)
        else {
            return Err(Error::UnknownLemmaName {
                lemma_name: funname.to_string(),
                oracle_name: oracle_name.to_string(),
            });
        };
        let right_oracle_return_pattern = patterns::ReturnPattern {
            game_name: right_game_inst.game_name(),
            game_params: &right_game_inst.consts,
            pkg_name: &right_game_inst.game.pkgs[right_oracle_export.to()].pkg.name,
            pkg_params: &right_game_inst.game.pkgs[right_oracle_export.to()].params,
            oracle_name: &right_oracle_export.sig().name,
        };

        let [left_old, right_old, left_return, right_return, ..] = &args[..] else {
            return Err(Error::IncorrectNumberOfArguments {
                argument: format!(
                    "({})",
                    args.iter().map(|sexpr| format!("{sexpr}")).join(" ")
                ),
                expected: "at least 4".to_string(),
                equivalence: self.equivalence_name(),
            });
        };
        let SmtExpr::Atom(left_old_name) = left_old.as_expression().unwrap() else {
            return Err(Error::IncorrectArgument {
                argument: format!("{left_old}"),
                equivalence: self.equivalence_name(),
            });
        };
        let SmtExpr::Atom(right_old_name) = right_old.as_expression().unwrap() else {
            return Err(Error::IncorrectArgument {
                argument: format!("{right_old}",),
                equivalence: self.equivalence_name(),
            });
        };
        let SmtExpr::Atom(left_return_name) = left_return.as_expression().unwrap() else {
            return Err(Error::IncorrectArgument {
                argument: format!("{left_return}",),
                equivalence: self.equivalence_name(),
            });
        };
        let SmtExpr::Atom(right_return_name) = right_return.as_expression().unwrap() else {
            return Err(Error::IncorrectArgument {
                argument: format!("{right_return}",),
                equivalence: self.equivalence_name(),
            });
        };

        let mut retbindings = Vec::new();
        retbindings.extend(gen_returnbinding(
            left_game_inst,
            left_return_name,
            left_oracle_export,
        ));
        retbindings.extend(gen_returnbinding(
            right_game_inst,
            right_return_name,
            right_oracle_export,
        ));

        let mut pkgbindings = Vec::new();
        pkgbindings.extend(gen_pkgbinding(left_game_inst, left_old_name));
        pkgbindings.extend(gen_pkgbinding(
            left_game_inst,
            &format!("{left_return_name}.state"),
        ));
        pkgbindings.extend(gen_pkgbinding(right_game_inst, right_old_name));
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
        let bindreturn: SmtExpr = SmtLet {
            bindings: retbindings,
            body: bindpackages,
        }
        .into();
        let mut newargs: Vec<SmtExpr> = vec![
            (left_old_name.clone(), left_game_state_pattern.sort_name()).into(),
            (right_old_name.clone(), right_game_state_pattern.sort_name()).into(),
            (
                left_return_name.clone(),
                left_oracle_return_pattern.sort_name(),
            )
                .into(),
            (
                right_return_name.clone(),
                right_oracle_return_pattern.sort_name(),
            )
                .into(),
        ];
        newargs.extend(
            args.into_iter()
                .skip(4)
                .map(|smt| smt.as_expression().unwrap().clone()),
        );
        let expr = ("define-fun", funname, newargs, "Bool", bindreturn).into();

        Ok(SmtObject::Statement(SmtStmt {
            sort: SmtStatementSort::GeneralRelation,
            name: funname.to_string(),
            expr,
        }))
    }
}

pub fn rewrite(context: &EquivalenceContext, content: &str) -> Result<Vec<SmtStmt>> {
    let mut rewriter: SmtRewrite = SmtRewrite::new(context);
    rewriter.parse_stmts(content)?;
    Ok(rewriter.content)
}
pub fn rewrite_game(
    context: &EquivalenceContext,
    game: &GameInstance,
    content: &str,
) -> Result<Vec<SmtStmt>> {
    let mut rewriter: SmtRewrite = SmtRewrite::new_with_game(context, game);
    rewriter.parse_stmts(content)?;
    Ok(rewriter.content)
}
pub fn rewrite_package(
    context: &EquivalenceContext,
    game: &GameInstance,
    package: &PackageInstance,
    content: &str,
) -> Result<Vec<SmtStmt>> {
    let mut rewriter: SmtRewrite = SmtRewrite::new_with_package(context, game, package);
    rewriter.parse_stmts(content)?;
    Ok(rewriter.content)
}
