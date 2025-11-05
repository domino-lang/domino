// SPDX-License-Identifier: MIT OR Apache-2.0

use std::collections::HashMap;

use crate::split::{SplitPath, SplitType};
use crate::transforms::split_partial::SplitInfo;
use crate::{package::OracleSig, types::Type};

use super::contexts::PackageInstanceContext;
use super::exprs::SmtExpr;
use super::exprs::{SmtAnd, SmtEq2, SmtIte};

// these are just the arg-x part, withpout the full oracle and package instance and game name up front

fn intermediate_state_piece_selector_arg_match_name(arg_name: &str) -> String {
    format!("match-arg-{arg_name}")
}

fn partial_function_arg_intermediate_state_name() -> String {
    "__intermediate_state".to_string()
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

impl<'a> PackageInstanceContext<'a> {
    pub fn check_args_are_honest<B: Into<SmtExpr>>(
        &self,
        args: &[(String, Type)],
        body: B,
    ) -> SmtExpr {
        if args.is_empty() {
            return body.into();
        }

        SmtIte {
            cond: SmtAnd(
                args.iter()
                    .map(|(arg_name, _)| {
                        let lhs = arg_name.clone(); // this is just a local variable
                        let rhs = intermediate_state_piece_selector_arg_match_name(arg_name);
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
        let game_inst_ctx = self.game_inst_ctx();
        let game_name = game_inst_ctx.game().name();
        let pkg_name = self.pkg_name();
        let pkg_params = &self.pkg_inst().params;
        let game_params = &self.game_inst().consts;
        let oracle_name = &datatype.real_oracle_sig.name;

        let octx = self.oracle_ctx_by_name(oracle_name).unwrap();

        let function_pattern = octx.dispatch_oracle_pattern();

        let intermediate_state_pattern = IntermediateStatePattern {
            pkg_name,
            params: pkg_params,
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
                        game_params,
                        pkg_name,
                        pkg_params,
                        oracle_name,
                    };

                    partial_return_pattern
                        .constructor_name(&PartialReturnConstructor::Abort)
                        .into()
                }
                IntermediateStateConstructor::OracleState(split_path) => {
                    let partial_oracle_function_pattern = PartialOraclePattern {
                        game_name,
                        pkg_name,
                        oracle_name,
                        split_path,
                        pkg_params,
                        game_params,
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
                            .map(|(name, _ty)| name.to_string().into()),
                    );
                    SmtExpr::List(call)
                }
            },
        );

        SmtDefineFun {
            name: function_pattern.function_name(),
            is_rec: false,
            args: function_pattern.function_args(),
            sort: function_pattern.function_return_sort(),
            body: match_expr,
        }
        .into()
    }
}
