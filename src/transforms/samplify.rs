use crate::expressions::Expression;
use crate::package::Composition;
use crate::statement::{CodeBlock, IfThenElse, Statement};
use crate::types::Type;
use std::collections::HashSet;
use std::convert::Infallible;
use std::iter::FromIterator;

#[derive(Debug, Clone)]

pub struct Transformation<'a>(pub &'a Composition);

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Position {
    pub game_name: String,
    pub inst_name: String,
    pub pkg_name: String,
    pub oracle_name: String,

    pub dst_name: String,
    pub dst_index: Option<Expression>,

    pub sample_id: usize,
    pub ty: Type,
    pub sample_name: String,
}

#[derive(Clone, Debug)]
pub struct SampleInfo {
    pub tys: Vec<Type>,
    pub count: usize,
    pub positions: Vec<Position>,
}

impl super::Transformation for Transformation<'_> {
    type Err = Infallible;
    type Aux = SampleInfo;

    fn transform(&self) -> Result<(Composition, SampleInfo), Infallible> {
        let mut ctr = 0usize;
        let mut samplings = HashSet::new();
        let mut positions = vec![];

        let game_name = self.0.name.as_str();

        let insts: Result<Vec<_>, Infallible> = self
            .0
            .pkgs
            .iter()
            .map(|inst| {
                let inst_name = inst.name.as_str();
                let pkg_name = inst.pkg.name.as_str();

                let mut newinst = inst.clone();
                for (i, oracle) in newinst.pkg.oracles.clone().iter().enumerate() {
                    let mut oracle_ctr = 1usize;
                    newinst.pkg.oracles[i].code = samplify(
                        &oracle.code,
                        game_name,
                        pkg_name,
                        inst_name,
                        &oracle.sig.name,
                        &mut ctr,
                        &mut oracle_ctr,
                        &mut samplings,
                        &mut positions,
                    )?;
                }
                Ok(newinst)
            })
            .collect();
        Ok((
            Composition {
                pkgs: insts?,
                ..self.0.clone()
            },
            SampleInfo {
                tys: Vec::from_iter(samplings),
                count: ctr,
                positions,
            },
        ))
    }
}

pub fn samplify(
    cb: &CodeBlock,
    game_name: &str,
    pkg_name: &str,
    inst_name: &str,
    oracle_name: &str,
    ctr: &mut usize,
    oracle_ctr: &mut usize,
    sampletypes: &mut HashSet<Type>,
    positions: &mut Vec<Position>,
) -> Result<CodeBlock, Infallible> {
    let mut newcode = Vec::new();
    for stmt in cb.0.clone() {
        match stmt {
            Statement::IfThenElse(ite) => {
                newcode.push(Statement::IfThenElse(IfThenElse {
                    then_block: samplify(
                        &ite.then_block,
                        game_name,
                        pkg_name,
                        inst_name,
                        oracle_name,
                        ctr,
                        oracle_ctr,
                        sampletypes,
                        positions,
                    )?,
                    else_block: samplify(
                        &ite.else_block,
                        game_name,
                        pkg_name,
                        inst_name,
                        oracle_name,
                        ctr,
                        oracle_ctr,
                        sampletypes,
                        positions,
                    )?,
                    ..ite
                }));
            }
            Statement::For(iter, start, end, code, file_pos) => newcode.push(Statement::For(
                iter,
                start,
                end,
                samplify(
                    &code,
                    game_name,
                    pkg_name,
                    inst_name,
                    oracle_name,
                    ctr,
                    oracle_ctr,
                    sampletypes,
                    positions,
                )?,
                file_pos,
            )),

            Statement::Sample(id, expr, None, ty, sample_name, file_pos) => {
                let sample_name = sample_name.unwrap_or(format!("{oracle_ctr}"));
                let pos = Position {
                    game_name: game_name.to_string(),
                    inst_name: inst_name.to_string(),
                    pkg_name: pkg_name.to_string(),
                    oracle_name: oracle_name.to_string(),
                    dst_name: id.ident(),
                    dst_index: expr.clone(),
                    sample_id: *ctr,
                    ty: ty.clone(),
                    sample_name: sample_name.clone(),
                };
                sampletypes.insert(ty.clone());
                positions.push(pos);
                newcode.push(Statement::Sample(
                    id.clone(),
                    expr,
                    Some(*ctr),
                    ty.clone(),
                    Some(sample_name),
                    file_pos,
                ));
                *ctr += 1;
                *oracle_ctr += 1;
            }
            _ => newcode.push(stmt),
        }
    }
    Ok(CodeBlock(newcode))
}

#[cfg(test)]
mod test {
    use std::collections::HashSet;

    use miette::SourceSpan;

    use crate::{
        block,
        identifier::{
            pkg_ident::{PackageIdentifier, PackageLocalIdentifier},
            Identifier,
        },
        statement::{CodeBlock, Statement},
        types::Type,
    };

    use super::samplify;

    fn test_run_samplify(cb: &CodeBlock) -> CodeBlock {
        let mut ctr = 0usize;
        let mut oracle_ctr = 1usize;
        let mut sampletypes = HashSet::new();
        let mut positions = vec![];

        samplify(
            cb,
            "test",
            "test",
            "test",
            "test",
            &mut ctr,
            &mut oracle_ctr,
            &mut sampletypes,
            &mut positions,
        )
        .unwrap()
    }

    fn local_ident(name: &str, ty: Type) -> Identifier {
        Identifier::PackageIdentifier(PackageIdentifier::Local(PackageLocalIdentifier {
            pkg_name: "TestPackage".to_string(),
            oracle_name: "TestOracle".to_string(),
            name: name.to_string(),
            ty: ty,
            pkg_inst_name: None,
            game_name: None,
            game_inst_name: None,
            theorem_name: None,
        }))
    }

    #[test]
    fn name_and_id_set() {
        let pos: SourceSpan = (0..0).into();
        let d = local_ident("d", Type::Integer);

        let code = block! {
            Statement::Sample(d.clone(),     // identifier
                              None,          // tableindex
                              None,          // sample-id
                              Type::Integer, // type
                              None,          // sample-name
                              pos)           // source-position

        };
        let new_code = test_run_samplify(&code);

        assert!(matches!(new_code.0[0], Statement::Sample(_, _, _, _, _, _)));
        if let Statement::Sample(_, _, sample_id, _, sample_name, _) = &new_code.0[0] {
            assert_eq!(sample_id, &Some(0usize));
            assert_eq!(sample_name, &Some("1".to_string()));
        } else {
            unreachable!()
        };
    }

    #[test]
    fn name_counts_named() {
        let pos: SourceSpan = (0..0).into();
        let d = local_ident("d", Type::Integer);

        let code = block! {
            Statement::Sample(d.clone(),             // identifier
                              None,                  // tableindex
                              None,                  // sample-id
                              Type::Integer,         // type
                              Some("a".to_string()), // sample-name
                              pos),                  // source-position
            Statement::Sample(d.clone(),     // identifier
                              None,          // tableindex
                              None,          // sample-id
                              Type::Integer, // type
                              None,          // sample-name
                              pos)           // source-position
        };
        let new_code = test_run_samplify(&code);

        assert!(matches!(new_code.0[0], Statement::Sample(_, _, _, _, _, _)));
        assert!(matches!(new_code.0[1], Statement::Sample(_, _, _, _, _, _)));
        if let Statement::Sample(_, _, sample_id, _, sample_name, _) = &new_code.0[0] {
            assert_eq!(sample_id, &Some(0usize));
            assert_eq!(sample_name, &Some("a".to_string()));
        } else {
            unreachable!()
        };
        if let Statement::Sample(_, _, sample_id, _, sample_name, _) = &new_code.0[1] {
            assert_eq!(sample_id, &Some(1usize));
            assert_eq!(sample_name, &Some("2".to_string()));
        } else {
            unreachable!()
        };
    }
}
