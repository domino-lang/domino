// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::writers::smt::{
    exprs::{SmtEq2, SmtExpr},
    patterns::{relation::Relation, DatastructurePattern, FunctionPattern, ReturnSelector},
};

impl Relation<'_> {
    pub(crate) fn build_same_output(&self) -> impl Into<SmtExpr> {
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

        let body = SmtEq2 {
            lhs: self
                .return_datatype_left
                .access(&return_spec_left, &selector, return_left)
                .unwrap(),
            rhs: self
                .return_datatype_right
                .access(&return_spec_right, &selector, return_right)
                .unwrap(),
        };

        self.define_fun(body)
    }
}
