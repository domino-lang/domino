use super::EquivalenceContext;
use crate::packageinstance::PackageInstance;
use crate::theorem::GameInstance;
use crate::transforms::samplify::SampleInfo;
use crate::util::smtparser::SmtParser;
use crate::writers::smt::exprs::SmtExpr;
use crate::writers::smt::exprs::SmtLet;
use crate::writers::smt::patterns;
use crate::writers::smt::patterns::datastructures::DatastructurePattern;

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

impl SmtParser<SmtExpr> for SmtRewrite<'_> {
    fn handle_atom(&mut self, content: &str) -> SmtExpr {
        SmtExpr::Atom(content.to_string())
    }

    fn handle_list(&mut self, content: Vec<SmtExpr>) -> SmtExpr {
        SmtExpr::List(content)
    }

    fn handle_sexp(&mut self, parsed: SmtExpr) {
        self.content.push(parsed);
    }

    fn handle_define_state_relation(
        &mut self,
        funname: &str,
        args: Vec<SmtExpr>,
        body: SmtExpr,
    ) -> SmtExpr {
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
            unreachable!()
        };
        let [left_arg_name, _left_arg_type] = &left_arg[..] else {
            unreachable!()
        };
        let [right_arg_name, _right_arg_type] = &right_arg[..] else {
            unreachable!()
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
}

pub fn rewrite(context: &EquivalenceContext, content: &str) -> Vec<SmtExpr> {
    let mut rewriter: SmtRewrite = SmtRewrite::new(context);
    rewriter.parse_sexps(content).unwrap();
    rewriter.content
}
