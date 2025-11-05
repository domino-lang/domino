// SPDX-License-Identifier: MIT OR Apache-2.0

use miette::SourceSpan;

use crate::{
    expressions::Expression, identifier::Identifier, statement::CodeBlock, types::Type,
    writers::smt::exprs::SmtExpr,
};
use std::fmt::Write;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SplitOracleSig {
    pub name: String,
    pub args: Vec<(String, Type)>,
    pub partial_vars: Vec<(String, Type)>,
    pub path: SplitPath,
    pub ty: Type,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SplitOracleDef {
    pub sig: SplitOracleSig,
    pub code: CodeBlock,
    pub file_pos: SourceSpan,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SplitPath(Vec<SplitPathComponent>);

impl std::ops::Index<usize> for SplitPath {
    type Output = SplitPathComponent;

    fn index(&self, index: usize) -> &Self::Output {
        &self.0[index]
    }
}

impl PartialOrd for SplitPath {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for SplitPath {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let min_len = usize::min(self.len(), other.len());

        for i in 0..min_len {
            match self.path()[i].cmp(&other.path()[i]) {
                std::cmp::Ordering::Equal => continue,
                other => return other,
            }
        }

        std::cmp::Ordering::Equal
    }
}

impl SplitPath {
    pub fn empty() -> Self {
        Self(vec![])
    }

    pub fn new(comps: Vec<SplitPathComponent>) -> Self {
        Self(comps)
    }

    pub fn path(&self) -> &Vec<SplitPathComponent> {
        &self.0
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn last(&self) -> Option<&SplitPathComponent> {
        self.0.last()
    }

    pub fn split_type(&self) -> Option<&SplitType> {
        Some(&self.0.last()?.split_type)
    }

    pub fn join(&mut self, other: &Self) {
        self.0.extend(other.0.iter().cloned());
    }

    pub fn has_prefix(&self, prefix: &SplitPath) -> bool {
        if prefix.len() > self.len() {
            return false;
        }

        for i in 0..prefix.len() {
            if prefix.0[i] != self.0[i] {
                return false;
            }
        }

        true
    }

    pub fn common_prefix(&self, other: &Self) -> Self {
        let min_len = usize::min(self.len(), other.len());

        let mut out = vec![];

        for i in 0..min_len {
            if self.path()[i] == other.path()[i] {
                out.push(self.path()[i].clone())
            } else {
                break;
            }
        }

        SplitPath(out)
    }

    pub fn additional_args(&self) -> Vec<SmtExpr> {
        let mut out = vec![];
        for path_elem in self.path().iter().rev() {
            match &path_elem.split_type {
                SplitType::Invoc(_) => break,
                SplitType::ForStep(ident, _, _) => out.push((ident.ident(), Type::Integer).into()),
                _ => {}
            }
        }
        out
    }

    pub fn basename(&self) -> (Option<SplitPathComponent>, Self) {
        let mut result = self.clone();
        let tail = result.0.pop();
        (tail, result)
    }

    pub fn extended(&self, component: SplitPathComponent) -> Self {
        let mut result = self.clone();
        result.0.push(component);
        result
    }

    pub fn smt_name(&self) -> String {
        let mut result = String::new();
        //write!(result, "{}", self.gamename).unwrap();
        for component in &self.0 {
            write!(
                result,
                "{:?}_{}/",
                component.split_range, component.split_type,
            )
            .unwrap();
        }
        result.pop();
        result
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SplitPathComponent {
    pub pkg_inst_name: String,
    pub oracle_name: String,
    pub split_type: SplitType,
    pub split_range: std::ops::Range<usize>,
}

impl PartialOrd for SplitPathComponent {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for SplitPathComponent {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // ranges can't overlap, so this is sufficient
        self.split_range.start.cmp(&other.split_range.start)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct InvocTargetData {
    pub pkg_inst_name: String,
    pub oracle_name: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum SplitType {
    Plain,                                       // before anything interesting happens
    Invoc(InvocTargetData),                      // called a child oracle
    ForStep(Identifier, Expression, Expression), // in a loop
    IfCondition(Expression),
    IfBranch,
    ElseBranch,
}

impl std::fmt::Display for SplitType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        match self {
            SplitType::ForStep(var, _, _) => write!(f, "ForStep{}", var.ident()),
            SplitType::IfCondition(_) => write!(f, "IfCondition"),
            _ => write!(f, "{:?}", &self),
        }
    }
}

impl SplitPathComponent {
    pub fn new(
        pkg_inst_name: &str,
        oracle_name: &str,
        split_type: SplitType,
        split_range: std::ops::Range<usize>,
    ) -> Self {
        SplitPathComponent {
            pkg_inst_name: pkg_inst_name.to_string(),
            oracle_name: oracle_name.to_string(),
            split_type,
            split_range,
        }
    }

    pub fn split_type(&self) -> &SplitType {
        &self.split_type
    }

    pub fn pkg_inst_name(&self) -> &str {
        &self.pkg_inst_name
    }

    pub fn oracle_name(&self) -> &str {
        &self.oracle_name
    }

    pub fn split_range(&self) -> &std::ops::Range<usize> {
        &self.split_range
    }
}
