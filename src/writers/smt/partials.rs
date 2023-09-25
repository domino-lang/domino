use std::collections::HashMap;

use crate::split::{SplitPath, SplitType};
use crate::transforms::split_partial::SplitInfo;
use crate::{package::OracleSig, types::Type};

use super::contexts::PackageInstanceContext;
use super::exprs::SmtExpr;
use super::exprs::{SmtAnd, SmtEq2, SmtIte};

// these are just the arg-x part, withpout the full oracle and package instance and game name up front

fn intermediate_state_piece_selector_child_match_name() -> String {
    format!("match-child")
}

fn intermediate_state_piece_selector_arg_match_name(arg_name: &str) -> String {
    format!("match-arg-{arg_name}")
}

fn intermediate_state_piece_selector_loopvar_match_name(local_name: &str) -> String {
    format!("match-loopvar-{local_name}")
}

fn intermediate_state_piece_selector_local_match_name(local_name: &str) -> String {
    format!("match-local-{local_name}")
}

fn partial_function_arg_intermediate_state_name() -> String {
    format!("__intermediate_state")
}

#[derive(Debug, Clone)]
pub struct PartialsDatatype {
    pub pkg_inst_name: String,
    pub real_oracle_sig: OracleSig,
    pub partial_steps: Vec<PartialStep>,
}

#[derive(Debug, Clone)]
pub struct PartialStep {
    path: SplitPath,
    locals: Vec<(String, Type)>,
}

pub(crate) fn into_partial_dtypes(splits: &SplitInfo) -> Vec<PartialsDatatype> {
    let mut map: HashMap<_, Vec<_>> = HashMap::new();

    for entry in splits {
        map.entry(entry.original_sig()).or_default().push(entry);
    }

    let mut out = vec![];

    for (real_oracle_sig, entries) in map {
        let partials_dt = PartialsDatatype {
            pkg_inst_name: entries[0].pkg_inst_name().to_string(),
            real_oracle_sig: real_oracle_sig.clone(),
            partial_steps: entries
                .iter()
                .map(|entry| PartialStep {
                    path: entry.path().clone(),
                    locals: entry.locals().clone(),
                })
                .collect(),
        };
        out.push(partials_dt);
    }

    out
}

impl PartialStep {
    fn has_child(&self) -> bool {
        matches!(self.path.split_type(), Some(SplitType::Invoc(_)))
    }

    pub(crate) fn path(&self) -> &SplitPath {
        &self.path
    }

    pub(crate) fn locals(&self) -> &Vec<(String, Type)> {
        &self.locals
    }
}

trait NameMapper {
    type Constructor;
    type Selector;

    fn map(&self, data: &PartialsDatatype) -> Vec<(Self::Constructor, Vec<Self::Selector>)> {
        data.partial_steps
            .iter()
            .map(|partial| {
                let constructor = self.constructor(&partial.path);
                let mut selectors = vec![];

                selectors.append(&mut self.loopvar(&partial.path()));
                for (arg_name, arg_type) in &data.real_oracle_sig.args {
                    selectors.push(self.arg(&partial.path, arg_type.into(), &arg_name))
                }
                for (local_name, local_type) in &partial.locals {
                    selectors.push(self.local(&partial.path, local_type.into(), &local_name))
                }

                if partial.has_child() {
                    selectors.push(self.child(&partial.path))
                }

                (constructor, selectors)
            })
            .collect()
    }

    fn arg(&self, path: &SplitPath, sort: SmtExpr, arg_name: &str) -> Self::Selector;
    fn local(&self, path: &SplitPath, sort: SmtExpr, local_name: &str) -> Self::Selector;
    fn child(&self, path: &SplitPath) -> Self::Selector;
    fn loopvar(&self, path: &SplitPath) -> Vec<Self::Selector>;
    fn end(&self) -> Self::Constructor;
    fn constructor(&self, path: &SplitPath) -> Self::Constructor;
}

struct MatchBlockMapper<'a> {
    game_name: &'a str,
    pkg_inst_name: &'a str,
    oracle_name: &'a str,
}

impl<'a> NameMapper for MatchBlockMapper<'a> {
    type Constructor = (String, Option<String>);
    type Selector = String;

    fn arg(&self, _path: &SplitPath, _sort: SmtExpr, arg_name: &str) -> Self::Selector {
        intermediate_state_piece_selector_arg_match_name(arg_name)
    }

    fn local(&self, _path: &SplitPath, _sort: SmtExpr, local_name: &str) -> Self::Selector {
        intermediate_state_piece_selector_local_match_name(local_name)
    }

    fn loopvar(&self, path: &SplitPath) -> Vec<Self::Selector> {
        let mut out = vec![];

        for elem in path.path() {
            if let SplitType::ForStep(loopvar, _, _) = elem.split_type() {
                out.push(intermediate_state_piece_selector_loopvar_match_name(
                    &loopvar.ident(),
                ))
            }
        }

        out
    }

    fn child(&self, _path: &SplitPath) -> Self::Selector {
        intermediate_state_piece_selector_child_match_name()
    }

    fn constructor(&self, path: &SplitPath) -> Self::Constructor {
        let Self {
            game_name,
            pkg_inst_name,
            oracle_name,
        } = self;

        let intermediate_state_pattern = IntermediateStatePattern {
            game_name,
            pkg_inst_name,
            oracle_name,
        };

        let partial_oracle_function_pattern = FunctionPattern::PartialOracle {
            game_name,
            pkg_inst_name,
            oracle_name,
            split_path: path,
        };

        let constructor = IntermediateStateConstructor::OracleState(path);
        let constructor_name = intermediate_state_pattern.constructor_name(&constructor);
        let target_oracle_name = partial_oracle_function_pattern.function_name();

        (constructor_name, Some(target_oracle_name))
    }

    fn end(&self) -> Self::Constructor {
        let intermediate_state_pattern = DatastructurePattern::IntermediateState {
            game_name: &self.game_name,
            pkg_inst_name: &self.pkg_inst_name,
            oracle_name: &self.oracle_name,
            variant_name: "end",
        };

        (intermediate_state_pattern.constructor_name(), None)
    }
}

/*
 *
 * [
 *   (Foo [ bar baz boo])
 *   (Bar [ foo bla blubb])
 * ]
 *
 * (match expr (  ( /pattern/   /body/ )*  )   )
 *             -----------------------------
 *             ^^^
 *
 * we want /pattern/ and /body/
 *
 * and /pattern/ is a constructor
 *
 *
 *
 * How //do// we know what to put into the block?
 *
 * - call the correct oracle
 * - how do we generate the function name of the correct oracle?
 *
 * */

use super::patterns::*;

struct SmtDefineFunction<B: Into<SmtExpr>> {
    name: String,
    args: Vec<(String, SmtExpr)>,
    ret_sort: SmtExpr,
    body: B,
}

impl<B: Into<SmtExpr>> Into<SmtExpr> for SmtDefineFunction<B> {
    fn into(self) -> SmtExpr {
        (
            "define-fun",
            self.name,
            {
                let args: Vec<_> = self
                    .args
                    .into_iter()
                    .map(|arg_spec| arg_spec.into())
                    .collect();

                SmtExpr::List(args)
            },
            self.ret_sort,
            self.body,
        )
            .into()
    }
}

impl<'a> PackageInstanceContext<'a> {
    fn check_args_are_honest<B: Into<SmtExpr>>(&self, args: &[(String, Type)], body: B) -> SmtExpr {
        if args.is_empty() {
            return body.into();
        }

        SmtIte {
            cond: SmtAnd(
                args.into_iter()
                    .map(|(arg_name, _)| {
                        let lhs = arg_name.clone(); // this is just a local variable
                        let rhs = intermediate_state_piece_selector_arg_match_name(&arg_name);
                        SmtEq2 { lhs, rhs }.into()
                    })
                    .collect(),
            ),
            then: body,
            els: "TODO check_args_are_honest instantiate an error here",
        }
        .into()
    }

    pub(crate) fn smt_declare_oracle_dispatch_function(
        &self,
        datatype: &PartialsDatatype,
    ) -> SmtExpr {
        let game_ctx = self.game_ctx();
        let game_name = &game_ctx.game().name;
        let pkg_inst_name = &self.pkg_inst_name();
        let oracle_name = &datatype.real_oracle_sig.name;

        let function_pattern = FunctionPattern::DispatchOracle {
            game_name,
            pkg_inst_name,
            oracle_sig: &datatype.real_oracle_sig,
        };

        let intermediate_state_pattern = IntermediateStatePattern {
            game_name,
            pkg_inst_name,
            oracle_name,
        };

        let intermediate_state_spec = intermediate_state_pattern.datastructure_spec(datatype);

        let match_expr = intermediate_state_pattern.match_expr(
            partial_function_arg_intermediate_state_name(),
            &intermediate_state_spec,
            |con| match con {
                IntermediateStateConstructor::End => {
                    let partial_return_pattern = PartialReturnPattern {
                        game_name,
                        pkg_inst_name,
                        oracle_name,
                    };

                    partial_return_pattern
                        .constructor_name(&PartialReturnConstructor::Abort)
                        .into()
                }
                IntermediateStateConstructor::OracleState(split_path) => {
                    let partial_oracle_function_pattern = FunctionPattern::PartialOracle {
                        game_name,
                        pkg_inst_name,
                        oracle_name,
                        split_path,
                    };

                    let oracle_fun_name = partial_oracle_function_pattern.function_name();

                    let mut call: Vec<SmtExpr> = vec![
                        oracle_fun_name.into(),
                        "__global_state".into(),
                        "__intermediate_state".into(),
                    ];
                    call.extend(
                        datatype
                            .real_oracle_sig
                            .args
                            .iter()
                            .map(|(name, _tipe)| name.to_string().into()),
                    );
                    SmtExpr::List(call)
                }
            },
        );

        SmtDefineFunction {
            name: function_pattern.function_name(),
            args: function_pattern.function_argspec(),
            ret_sort: function_pattern.function_return_sort_name().into(),
            body: match_expr,
        }
        .into()
    }
}

#[derive(Debug, Clone)]
pub struct SmtMatch<E, B>
where
    E: Into<SmtExpr> + std::fmt::Debug + Clone,
    B: Into<SmtExpr> + std::fmt::Debug + Clone,
{
    pub expr: E,
    pub cases: Vec<SmtMatchCase<B>>,
}

impl<E, B> From<SmtMatch<E, B>> for SmtExpr
where
    E: Into<SmtExpr> + std::fmt::Debug + Clone,
    B: Into<SmtExpr> + std::fmt::Debug + Clone,
{
    fn from(value: SmtMatch<E, B>) -> SmtExpr {
        let cases = value
            .cases
            .into_iter()
            .map(|case| {
                let mut pattern = vec![case.constructor.into()];
                pattern.extend(case.args.into_iter().map(|s| s.into()));

                SmtExpr::List(vec![SmtExpr::List(pattern), case.body.into()])
            })
            .collect();

        return ("match", value.expr, SmtExpr::List(cases)).into();
    }
}

#[derive(Debug, Clone)]
pub struct SmtMatchCase<B>
where
    B: Into<SmtExpr> + std::fmt::Debug + Clone,
{
    pub constructor: String,
    pub args: Vec<String>,
    pub body: B,
}
