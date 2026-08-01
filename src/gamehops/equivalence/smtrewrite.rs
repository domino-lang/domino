use super::EquivalenceContext;
use crate::package::Export;
use crate::packageinstance::PackageInstance;
use crate::theorem::GameInstance;
use crate::transforms::samplify::SampleInfo;
use crate::util::smtparser::SmtParser;
use crate::writers::smt::contexts::GameInstanceContext;
use crate::writers::smt::exprs::SmtAnd;
use crate::writers::smt::exprs::SmtExpr;
use crate::writers::smt::exprs::SmtLet;
use crate::writers::smt::patterns;
use crate::writers::smt::patterns::datastructures::DatastructurePattern;
use crate::writers::smt::patterns::SmtDefineFun;
use crate::writers::smt::sorts::Sort;

use crate::gamehops::equivalence::error::{Error, Result};
use itertools::Itertools;

struct SmtRewrite<'a> {
    context: &'a EquivalenceContext<'a>,
    package: Option<&'a PackageInstance>,
    game: Option<&'a GameInstance>,
    content: Vec<SmtExpr>,
    file_name: String,
    /// Names of every `define-state-relation` encountered while rewriting. Only meaningful for
    /// `rewrite()` (the equivalence-level "main invariant" files) — these are the candidate
    /// invariant fragments (see `EquivalenceContext::state_relation_names`).
    state_relations: Vec<String>,
}

impl<'a> SmtRewrite<'a> {
    fn new(context: &'a EquivalenceContext, file_name: &str) -> Self {
        Self {
            context,
            package: None,
            game: None,
            content: Vec::new(),
            file_name: file_name.to_string(),
            state_relations: Vec::new(),
        }
    }

    fn new_with_game(context: &'a EquivalenceContext, game: &'a GameInstance, file_name: &str) -> Self {
        Self {
            context,
            package: None,
            game: Some(game),
            content: Vec::new(),
            file_name: file_name.to_string(),
            state_relations: Vec::new(),
        }
    }

    fn new_with_package(
        context: &'a EquivalenceContext,
        game: &'a GameInstance,
        package: &'a PackageInstance,
        file_name: &str,
    ) -> Self {
        Self {
            context,
            package: Some(package),
            game: Some(game),
            content: Vec::new(),
            file_name: file_name.to_string(),
            state_relations: Vec::new(),
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

fn format_definition(keyword: &str, funname: &str, args: &[SmtExpr], body: &SmtExpr) -> String {
    format!(
        "({keyword} {funname} ({}) {body})",
        args.iter().map(|arg| format!("{arg}")).join(" ")
    )
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

    fn handle_define_game_invariant(&mut self, body: SmtExpr) -> Result<SmtExpr> {
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

        let bindpackages = SmtLet {
            bindings: pkgbindings,
            body: bindvars,
        };

        self.handle_definefun(
            &format!("game-invariant!{}!", self.game.unwrap().name()),
            vec![(
                SmtExpr::Atom("game".to_string()),
                SmtExpr::Atom(gamestate_sort),
            )
                .into()],
            "Bool",
            bindpackages.into(),
        )
    }

    fn handle_define_package_invariant(&mut self, body: SmtExpr) -> Result<SmtExpr> {
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
        let bindpkg = SmtLet {
            bindings: vec![(
                "pkg".to_string(),
                gamestate_context
                    .smt_access_gamestate_pkgstate("game", self.package.unwrap().name())
                    .unwrap(),
            )],
            body: bindvars,
        };

        self.handle_definefun(
            &format!(
                "package-invariant!{}-{}!",
                self.game.unwrap().name(),
                self.package.unwrap().name()
            ),
            vec![(
                SmtExpr::Atom("game".to_string()),
                SmtExpr::Atom(gamestate_sort),
            )
                .into()],
            "Bool",
            bindpkg.into(),
        )
    }

    fn handle_define_state_relation(
        &mut self,
        funname: &str,
        args: Vec<SmtExpr>,
        body: SmtExpr,
    ) -> Result<SmtExpr> {
        self.state_relations.push(funname.to_string());

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

        let expression = format_definition("define-state-relation", funname, &args, &body);

        let [left_arg, right_arg] = &args[..] else {
            return Err(Error::IncorrectNumberOfArguments {
                name: funname.to_string(),
                file_name: self.file_name.clone(),
                expression,
                argument: format!(
                    "({})",
                    args.iter().map(|sexpr| format!("{sexpr}")).join(" ")
                ),
                expected: "2".to_string(),
                equivalence: self.equivalence_name(),
            });
        };
        let SmtExpr::Atom(left_arg_name) = left_arg else {
            return Err(Error::IncorrectArgument {
                argument: format!("{left_arg}",),
                equivalence: self.equivalence_name(),
            });
        };
        let SmtExpr::Atom(right_arg_name) = right_arg else {
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

        let bindpackages = SmtLet {
            bindings: pkgbindings,
            body: bindvars,
        };
        self.handle_definefun(
            funname,
            vec![
                (left_arg_name.clone(), left_game_state_pattern.sort_name()).into(),
                (right_arg_name.clone(), right_game_state_pattern.sort_name()).into(),
            ],
            "Bool",
            bindpackages.into(),
        )
    }

    fn handle_define_lemma(
        &mut self,
        funname: &str,
        args: Vec<SmtExpr>,
        body: SmtExpr,
    ) -> Result<SmtExpr> {
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

        let expression = format_definition("define-lemma", funname, &args, &body);

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
            .find(|export| export.sig().name == oracle_name)
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
            oracle_name,
        };

        let Some(right_oracle_export) = right_game_inst
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
        let right_oracle_return_pattern = patterns::ReturnPattern {
            game_name: right_game_inst.game_name(),
            game_params: &right_game_inst.consts,
            pkg_name: &right_game_inst.game.pkgs[right_oracle_export.to()].pkg.name,
            pkg_params: &right_game_inst.game.pkgs[right_oracle_export.to()].params,
            oracle_name,
        };

        let [left_old, right_old, left_return, right_return, ..] = &args[..] else {
            return Err(Error::IncorrectNumberOfArguments {
                name: funname.to_string(),
                file_name: self.file_name.clone(),
                expression: expression.clone(),
                argument: format!(
                    "({})",
                    args.iter().map(|sexpr| format!("{sexpr}")).join(" ")
                ),
                expected: "at least 4".to_string(),
                equivalence: self.equivalence_name(),
            });
        };
        let SmtExpr::Atom(left_old_name) = left_old else {
            return Err(Error::IncorrectArgument {
                argument: format!("{left_old}"),
                equivalence: self.equivalence_name(),
            });
        };
        let SmtExpr::Atom(right_old_name) = right_old else {
            return Err(Error::IncorrectArgument {
                argument: format!("{right_old}",),
                equivalence: self.equivalence_name(),
            });
        };
        let SmtExpr::Atom(left_return_name) = left_return else {
            return Err(Error::IncorrectArgument {
                argument: format!("{left_return}",),
                equivalence: self.equivalence_name(),
            });
        };
        let SmtExpr::Atom(right_return_name) = right_return else {
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
        let bindreturn = SmtLet {
            bindings: retbindings,
            body: bindpackages,
        };
        let mut newargs = vec![
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

        let oracle_args = &left_oracle_export.sig().args;
        let extra_args = &args[4..];
        if extra_args.len() != oracle_args.len() {
            return Err(Error::IncorrectNumberOfArguments {
                name: funname.to_string(),
                file_name: self.file_name.clone(),
                expression,
                argument: format!(
                    "({})",
                    extra_args.iter().map(|sexpr| format!("{sexpr}")).join(" ")
                ),
                expected: format!("{} oracle argument(s)", oracle_args.len()),
                equivalence: self.equivalence_name(),
            });
        }
        for (arg, (_, ty)) in extra_args.iter().zip(oracle_args.iter()) {
            let arg_name = match arg {
                SmtExpr::Atom(name) => name.clone(),
                SmtExpr::List(elems) => match elems.first() {
                    Some(SmtExpr::Atom(name)) => name.clone(),
                    _ => {
                        return Err(Error::IncorrectArgument {
                            argument: format!("{arg}"),
                            equivalence: self.equivalence_name(),
                        })
                    }
                },
                _ => {
                    return Err(Error::IncorrectArgument {
                        argument: format!("{arg}"),
                        equivalence: self.equivalence_name(),
                    })
                }
            };
            newargs.push((arg_name, ty.clone()).into());
        }

        self.handle_definefun(funname, newargs, "Bool", bindreturn.into())
    }
}

/// Rewrites an equivalence-level ("main") invariant file, returning both the rewritten SMT
/// content and the names of every `define-state-relation` it declared (the invariant fragment
/// names — see `EquivalenceContext::state_relation_names`).
pub fn rewrite(
    context: &EquivalenceContext,
    file_name: &str,
    content: &str,
) -> Result<(Vec<SmtExpr>, Vec<String>)> {
    let mut rewriter: SmtRewrite = SmtRewrite::new(context, file_name);
    rewriter.parse_sexps(content)?;
    Ok((rewriter.content, rewriter.state_relations))
}

/// Whether `exprs` already contains a top-level `define-fun`/`define-fun-rec` literally named
/// `name`. Unlike tracking `define-state-relation` macro invocations, this also recognizes older
/// projects that hand-write the fully mangled `(define-fun invariant ...)` form directly instead
/// of going through the macro (see the domino skill docs / `hello-world` example project).
pub fn defines_function_named(exprs: &[SmtExpr], name: &str) -> bool {
    exprs.iter().any(|expr| {
        let SmtExpr::List(items) = expr else {
            return false;
        };
        let is_define = matches!(
            items.first(),
            Some(SmtExpr::Atom(kw)) if kw == "define-fun" || kw == "define-fun-rec"
        );
        let matches_name = matches!(items.get(1), Some(SmtExpr::Atom(n)) if n == name);
        is_define && matches_name
    })
}

/// Synthesizes a `define-fun invariant ((L <left_sort>) (R <right_sort>)) Bool (and (frag1 L R)
/// ...))` combining every named invariant fragment via conjunction. Used when an oracle's main
/// invariant files declare one or more `define-state-relation`s but none of them is literally
/// named `invariant` — every existing call site that assumes/asserts the old-state invariant
/// hardcodes a call to the function literally named `invariant`, so synthesizing it under that
/// name lets those call sites work unmodified.
pub fn synthesize_invariant(left_sort: Sort, right_sort: Sort, fragment_names: &[String]) -> SmtExpr {
    let calls: Vec<SmtExpr> = fragment_names
        .iter()
        .map(|name| (name.as_str(), "L", "R").into())
        .collect();

    let body: SmtExpr = match calls.len() {
        0 => "true".into(),
        1 => calls.into_iter().next().unwrap(),
        _ => SmtAnd(calls).into(),
    };

    SmtDefineFun {
        is_rec: false,
        name: "invariant".to_string(),
        args: vec![("L".to_string(), left_sort), ("R".to_string(), right_sort)],
        sort: Sort::Bool,
        body,
    }
    .into()
}

pub fn rewrite_game(
    context: &EquivalenceContext,
    game: &GameInstance,
    file_name: &str,
    content: &str,
) -> Result<Vec<SmtExpr>> {
    let mut rewriter: SmtRewrite = SmtRewrite::new_with_game(context, game, file_name);
    rewriter.parse_sexps(content)?;
    Ok(rewriter.content)
}
pub fn rewrite_package(
    context: &EquivalenceContext,
    game: &GameInstance,
    package: &PackageInstance,
    file_name: &str,
    content: &str,
) -> Result<Vec<SmtExpr>> {
    let mut rewriter: SmtRewrite = SmtRewrite::new_with_package(context, game, package, file_name);
    rewriter.parse_sexps(content)?;
    Ok(rewriter.content)
}
