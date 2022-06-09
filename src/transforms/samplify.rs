use std::iter::FromIterator;
use crate::package::Composition;
use crate::types::Type;
use crate::statement::{CodeBlock, Statement};
use std::collections::HashSet;

#[derive(Debug, Clone)]
pub struct Error(pub String);

pub struct Transformation<'a>(pub &'a Composition);

pub struct SampleInfo {
    pub tipes: Vec<Type>,
    pub count: u32
}

impl<'a> super::Transformation for Transformation<'a> {
    type Err = Error;
    type Aux = SampleInfo;

    fn transform(&self) -> Result<(Composition, SampleInfo), Error> {
        let mut ctr = 1u32;
        let mut samplings = HashSet::new();

        let insts: Result<Vec<_>, _> = self
            .0
            .pkgs
            .iter()
            .map(|inst| {
                let mut newinst = inst.clone();
                for (i, oracle) in newinst.pkg.oracles.clone().iter().enumerate() {
                    newinst.pkg.oracles[i].code = samplify(&oracle.code, &mut ctr, &mut samplings)?;
                }
                Ok(newinst)
            })
            .collect();
        Ok((
            Composition {
                pkgs: insts?,
                ..self.0.clone()
            },
            SampleInfo{tipes: Vec::from_iter(samplings), count: ctr},
        ))
    }
}

pub fn samplify(cb: &CodeBlock, ctr: &mut u32, sampletypes: &mut HashSet<Type>) -> Result<CodeBlock, Error> {
    let mut newcode = Vec::new();
    for stmt in cb.0.clone() {
        match stmt {
            Statement::IfThenElse(expr, ifcode, elsecode) => {
                newcode.push(Statement::IfThenElse(
                    expr,
                    samplify(&ifcode, ctr, sampletypes)?,
                    samplify(&elsecode, ctr, sampletypes)?,
                ));
            },
            Statement::Sample(id, expr, None, tipe) => {
                sampletypes.insert(tipe.clone());
                newcode.push(Statement::Sample(id.clone(), expr, Some(*ctr), tipe.clone()));
                *ctr = *ctr+1;
            },
            _ => newcode.push(stmt)
        }
    }
    Ok(CodeBlock(newcode))
}
