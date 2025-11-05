// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::writers::smt::{
    exprs::{SmtAnd, SmtExpr, SmtIs, SmtNot},
    patterns::{
        relation::Relation, DatastructurePattern, FunctionPattern, ReturnSelector, ReturnValue,
        ReturnValueConstructor, SmtDefineFun,
    },
};

impl Relation<'_> {
    fn left_no_abort_body(&self) -> impl Into<SmtExpr> {
        let return_spec_left = self
            .return_datatype_left
            .datastructure_spec(self.return_type);

        let return_left: SmtExpr = self.arg_return_left().0.into();

        let selector = ReturnSelector::ReturnValueOrAbort {
            return_type: self.return_type,
        };

        let return_value_pattern = ReturnValue {
            inner_type: self.return_type,
        };

        let is_abort = return_value_pattern.constructor_name(&ReturnValueConstructor::Abort);

        SmtNot(SmtIs {
            con: is_abort.clone(),
            expr: self
                .return_datatype_left
                .access(&return_spec_left, &selector, return_left)
                .unwrap(),
        })
    }

    fn right_no_abort_body(&self) -> impl Into<SmtExpr> {
        let return_spec_right = self
            .return_datatype_right
            .datastructure_spec(self.return_type);

        let return_right: SmtExpr = self.arg_return_right().0.into();

        let selector = ReturnSelector::ReturnValueOrAbort {
            return_type: self.return_type,
        };

        let return_value_pattern = ReturnValue {
            inner_type: self.return_type,
        };

        let is_abort = return_value_pattern.constructor_name(&ReturnValueConstructor::Abort);

        SmtNot(SmtIs {
            con: is_abort.clone(),
            expr: self
                .return_datatype_right
                .access(&return_spec_right, &selector, return_right)
                .unwrap(),
        })
    }

    pub(crate) fn build_left_no_abort(&self) -> impl Into<SmtExpr> {
        self.define_fun(self.left_no_abort_body())
    }

    pub(crate) fn build_right_no_abort(&self) -> impl Into<SmtExpr> {
        self.define_fun(self.right_no_abort_body())
    }
    pub(crate) fn build_no_abort(&self) -> SmtDefineFun<SmtAnd> {
        self.define_fun(SmtAnd(vec![
            self.left_no_abort_body().into(),
            self.right_no_abort_body().into(),
        ]))
    }
}
