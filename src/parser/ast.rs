// SPDX-License-Identifier: MIT OR Apache-2.0

use pest::{iterators::Pair, Span};

#[derive(Clone, Debug)]
struct IdentifierData<'a> {
    str: &'a str,
    span: Span<'a>,
}

impl<'a> IdentifierData<'a> {
    fn new(ast: Pair<'a, super::Rule>) -> Self {
        Self {
            str: ast.as_str(),
            span: ast.as_span(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct PackageName<'a>(IdentifierData<'a>);

#[derive(Clone, Debug)]
pub struct PackageInstanceName<'a>(IdentifierData<'a>);

#[derive(Clone, Debug)]
pub struct GameName<'a>(IdentifierData<'a>);

#[derive(Clone, Debug)]
pub struct GameInstanceName<'a>(IdentifierData<'a>);

#[derive(Clone, Debug)]
pub struct TheoremName<'a>(IdentifierData<'a>);

#[derive(Clone, Debug)]
pub struct AssumptionName<'a>(IdentifierData<'a>);

macro_rules! impl_ast {
    ($struct:ty) => {
        impl<'a> $struct {
            pub fn new(ast: Pair<'a, $crate::parser::Rule>) -> Self {
                Self(IdentifierData::new(ast))
            }
        }

        impl<'a> $crate::parser::ast::Identifier<'a> for $struct {
            fn as_str(&self) -> &'a str {
                &self.0.str
            }

            fn as_span(&self) -> Span<'a> {
                self.0.span
            }
        }

        impl<'a> From<Pair<'a, $crate::parser::Rule>> for $struct {
            fn from(ast: Pair<'a, $crate::parser::Rule>) -> Self {
                Self::new(ast)
            }
        }
    };
}

impl_ast!(PackageName<'a>);
impl_ast!(PackageInstanceName<'a>);
impl_ast!(GameName<'a>);
impl_ast!(GameInstanceName<'a>);
impl_ast!(TheoremName<'a>);
impl_ast!(AssumptionName<'a>);

pub(crate) trait Identifier<'a>:
    From<Pair<'a, crate::parser::Rule>> + std::fmt::Debug
{
    fn as_str(&self) -> &'a str;
    fn as_span(&self) -> Span<'a>;
}
