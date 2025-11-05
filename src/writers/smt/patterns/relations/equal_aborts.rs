// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::writers::smt::{
    exprs::{SmtEq2, SmtExpr, SmtIs, SmtLet},
    patterns::{
        relation::Relation, DatastructurePattern, FunctionPattern, ReturnSelector, ReturnValue,
        ReturnValueConstructor, SmtDefineFun,
    },
};

pub(crate) type RelationFunction =
    SmtDefineFun<SmtLet<SmtEq2<SmtIs<String, &'static str>, SmtIs<String, &'static str>>>>;

impl Relation<'_> {
    pub(crate) fn build_equal_aborts(&self) -> RelationFunction {
        let return_spec_left = self
            .return_datatype_left
            .datastructure_spec(self.return_type);

        let return_spec_right = self
            .return_datatype_right
            .datastructure_spec(self.return_type);

        let return_left: SmtExpr = self.arg_return_left().0.into();
        let return_right: SmtExpr = self.arg_return_right().0.into();

        let selector = ReturnSelector::ReturnValueOrAbort {
            return_type: self.return_type,
        };

        let return_value_left_name = "return-value-left";
        let return_value_right_name = "return-value-right";

        let return_value_pattern = ReturnValue {
            inner_type: self.return_type,
        };
        let is_abort = return_value_pattern.constructor_name(&ReturnValueConstructor::Abort);

        let body = SmtLet {
            bindings: vec![
                (
                    return_value_left_name.to_string(),
                    self.return_datatype_left
                        .access(&return_spec_left, &selector, return_left)
                        .unwrap(),
                ),
                (
                    return_value_right_name.to_string(),
                    self.return_datatype_right
                        .access(&return_spec_right, &selector, return_right)
                        .unwrap(),
                ),
            ],
            body: SmtEq2 {
                lhs: SmtIs {
                    con: is_abort.clone(),
                    expr: return_value_left_name,
                },
                rhs: SmtIs {
                    con: is_abort,
                    expr: return_value_right_name,
                },
            },
        };

        self.define_fun(body)
    }
}
