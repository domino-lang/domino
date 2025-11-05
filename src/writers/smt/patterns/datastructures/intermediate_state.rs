// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::{
    expressions::Expression,
    identifier::pkg_ident::PackageConstIdentifier,
    package::OracleSig,
    split::{SplitPath, SplitType},
    types::Type,
    writers::smt::{
        exprs::{SmtExpr, SmtLet},
        partials::{PartialStep, PartialsDatatype},
        patterns::instance_names::{encode_params, only_non_function_expression},
    },
};

use super::{DatastructurePattern, DatastructureSpec};

#[derive(Debug)]
pub struct IntermediateStatePattern<'a> {
    pub pkg_name: &'a str,
    pub params: &'a [(PackageConstIdentifier, Expression)],
    pub oracle_name: &'a str,
}

#[derive(Debug, PartialEq, Eq)]
pub enum IntermediateStateConstructor<'a> {
    End,
    OracleState(&'a SplitPath),
}

#[derive(Debug, PartialEq, Eq)]
pub enum IntermediateStateSelector<'a> {
    Arg(&'a SplitPath, &'a str, &'a Type),
    LoopVar(&'a SplitPath, &'a str),
    Local(&'a SplitPath, &'a str, &'a Type),
    Child(&'a SplitPath),
    Return(&'a Type),
}

impl SplitPath {
    pub(crate) fn loopvar_selectors(&self) -> Vec<(&str, IntermediateStateSelector)> {
        let mut out = vec![];
        for elem in self.path() {
            if let SplitType::ForStep(loopvar, _, _) = elem.split_type() {
                let name = loopvar.ident_ref();
                out.push((name, IntermediateStateSelector::LoopVar(self, name)));
            }
        }

        out
    }
}

impl<'a> IntermediateStatePattern<'a> {
    fn constructors(
        &self,
        partials: &'a PartialsDatatype,
    ) -> Vec<(
        IntermediateStateConstructor<'a>,
        Vec<IntermediateStateSelector<'a>>,
    )> {
        let return_type = &partials.real_oracle_sig.ty;
        let mut out = vec![(
            IntermediateStateConstructor::End,
            vec![IntermediateStateSelector::Return(return_type)],
        )];

        for step in &partials.partial_steps {
            let constructor = IntermediateStateConstructor::OracleState(step.path());
            let selectors = self.selectors(&partials.real_oracle_sig, step);

            out.push((constructor, selectors));
        }

        out
    }

    fn selectors(
        &self,
        original_sig: &'a OracleSig,
        step: &'a PartialStep,
    ) -> Vec<IntermediateStateSelector<'a>> {
        let path = step.path();
        let mut out = vec![];

        // loopvars
        for elem in path.path() {
            if let SplitType::ForStep(loopvar, _, _) = elem.split_type() {
                let ident = loopvar.ident_ref();
                let sel = IntermediateStateSelector::LoopVar(path, ident);

                out.push(sel)
            }
        }

        // args
        for (arg_name, arg_type) in &original_sig.args {
            let sel = IntermediateStateSelector::Arg(path, arg_name, arg_type);

            out.push(sel);
        }

        // locals
        for (local_name, local_type) in step.locals() {
            let sel = IntermediateStateSelector::Local(path, local_name, local_type);

            out.push(sel);
        }

        // child
        // the following line was copied from old code, not sure how correct it is
        let has_child = matches!(path.split_type(), Some(SplitType::Invoc(_)));
        if has_child {
            let sel = IntermediateStateSelector::Child(path);

            out.push(sel)
        }

        out
    }

    pub fn recover_variables<B: Into<SmtExpr>>(
        &self,
        spec: &DatastructureSpec<'a, Self>,
        con: &<Self as DatastructurePattern<'a>>::Constructor,
        body: B,
    ) -> Option<SmtExpr> {
        let (_, sels) = spec.0.iter().find(|(cur_con, _)| cur_con == con)?;
        let out = SmtLet {
            bindings: sels
                .iter()
                .filter_map(|sel| match sel {
                    IntermediateStateSelector::Local(_, name, _)
                    | IntermediateStateSelector::LoopVar(_, name)
                    | IntermediateStateSelector::Arg(_, name, _) => Some((
                        name.to_string(),
                        self.access(spec, sel, "__intermediate_state").unwrap(),
                    )),
                    _ => None,
                })
                .collect(),
            body: body.into(),
        };

        Some(out.into())
    }
}

impl<'a> DatastructurePattern<'a> for IntermediateStatePattern<'a> {
    type Constructor = IntermediateStateConstructor<'a>;
    type Selector = IntermediateStateSelector<'a>;
    type DeclareInfo = PartialsDatatype;

    const CAMEL_CASE: &'static str = "IntermediateState";

    const KEBAB_CASE: &'static str = "intermediate-state";

    fn sort_name(&self) -> String {
        let camel_case = IntermediateStatePattern::CAMEL_CASE;
        let Self {
            pkg_name,
            params,
            oracle_name,
        } = self;

        let params = encode_params(only_non_function_expression(*params));

        format!("{camel_case}-{pkg_name}-{params}-{oracle_name}")
    }

    fn constructor_name(&self, cons: &Self::Constructor) -> String {
        let kebab_case = Self::KEBAB_CASE;
        let Self {
            pkg_name,
            oracle_name,
            params,
        } = self;
        let variant_name = match cons {
            IntermediateStateConstructor::End => "end".to_string(),
            IntermediateStateConstructor::OracleState(path) => path.smt_name(),
        };

        let params = encode_params(only_non_function_expression(*params));

        format!("<mk-{kebab_case}-{pkg_name}-{params}-{oracle_name}-{variant_name}>")
    }

    fn selector_name(&self, sel: &Self::Selector) -> String {
        let kebab_case = Self::KEBAB_CASE;
        let Self {
            pkg_name,
            oracle_name,
            params,
        } = self;

        let params = encode_params(only_non_function_expression(*params));
        let field_name = match sel {
            IntermediateStateSelector::Arg(path, name, _type) => {
                format!("{}-arg-{name}", path.smt_name())
            }
            IntermediateStateSelector::LoopVar(path, name) => {
                format!("{}-loopvar-{name}", path.smt_name())
            }
            IntermediateStateSelector::Local(path, name, _type) => {
                format!("{}-local-{name}", path.smt_name())
            }
            IntermediateStateSelector::Child(path) => format!("{}-child", path.smt_name()),
            IntermediateStateSelector::Return(_type) => "end-return".to_string(),
        };

        format!("<{kebab_case}-{pkg_name}-{params}-{oracle_name}-{field_name}>")
    }

    fn matchfield_name(&self, sel: &Self::Selector) -> String {
        let field_name = match sel {
            IntermediateStateSelector::Arg(path, name, _type) => {
                format!("{}-arg-{name}", path.smt_name())
            }
            IntermediateStateSelector::LoopVar(path, name) => {
                format!("{}-loopvar-{name}", path.smt_name())
            }
            IntermediateStateSelector::Local(path, name, _type) => {
                format!("{}-local-{name}", path.smt_name())
            }
            IntermediateStateSelector::Child(path) => format!("{}-child", path.smt_name()),
            IntermediateStateSelector::Return(_type) => "end-return".to_string(),
        };

        format!("<match-{field_name}>")
    }

    fn selector_sort(&self, sel: &Self::Selector) -> SmtExpr {
        match sel {
            IntermediateStateSelector::LoopVar(_, _) => Type::Integer.into(),
            IntermediateStateSelector::Child(_) => self.sort(vec![]).into(),
            IntermediateStateSelector::Arg(_, _, ty)
            | IntermediateStateSelector::Local(_, _, ty)
            | IntermediateStateSelector::Return(ty) => SmtExpr::from(*ty),
        }
    }

    fn datastructure_spec(
        &self,
        info: &'a Self::DeclareInfo,
    ) -> super::DatastructureSpec<'a, Self> {
        DatastructureSpec(self.constructors(info))
    }
}
