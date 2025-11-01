// SPDX-License-Identifier: MIT OR Apache-2.0

pub mod const_mapping;
//pub mod dispatch_oracle;
pub mod oracle;
//pub mod partial_oracle;

pub mod relation;

//pub use dispatch_oracle::DispatchOraclePattern;
pub use oracle::{OraclePattern, ORACLE_ARG_GAME_STATE, ORACLE_ARG_INTERMEDIATE_STATE};
//pub use partial_oracle::PartialOraclePattern;

use crate::writers::smt::{exprs::SmtExpr, sorts::Sort};

pub trait FunctionPattern {
    fn function_name(&self) -> String;
    fn function_args(&self) -> Vec<(String, Sort)>;
    fn function_args_count(&self) -> usize;
    fn function_return_sort(&self) -> Sort;

    fn define_fun<B: Into<SmtExpr>>(&self, body: B) -> SmtDefineFun<B> {
        SmtDefineFun {
            is_rec: false,
            name: self.function_name(),
            args: self.function_args(),
            sort: self.function_return_sort(),
            body,
        }
    }

    fn define_fun_rec<B: Into<SmtExpr>>(&self, body: B) -> SmtExpr {
        (
            "define-fun-rec",
            self.function_name(),
            SmtExpr::List(
                self.function_args()
                    .into_iter()
                    .map(|pair| -> SmtExpr { pair.into() })
                    .collect(),
            ),
            self.function_return_sort(),
            body,
        )
            .into()
    }

    fn call(&self, args: &[SmtExpr]) -> Option<SmtExpr> {
        if args.len() == self.function_args_count() {
            let mut call: Vec<SmtExpr> = vec![self.function_name().into()];
            call.extend(args.iter().cloned());
            Some(SmtExpr::List(call))
        } else {
            None
        }
    }
}

#[derive(Debug)]
pub struct SmtDefineFun<Body: Into<SmtExpr>> {
    pub(crate) is_rec: bool,
    pub(crate) name: String,
    pub(crate) args: Vec<(String, Sort)>,
    pub(crate) sort: Sort,
    pub(crate) body: Body,
}

impl<Body: Into<SmtExpr>> From<SmtDefineFun<Body>> for SmtExpr {
    fn from(value: SmtDefineFun<Body>) -> Self {
        let command_name = if value.is_rec {
            "define-fun-rec"
        } else {
            "define-fun"
        };

        (
            command_name,
            value.name,
            SmtExpr::List(
                value
                    .args
                    .into_iter()
                    .map(|pair| -> SmtExpr { pair.into() })
                    .collect(),
            ),
            value.sort,
            value.body,
        )
            .into()
    }
}
