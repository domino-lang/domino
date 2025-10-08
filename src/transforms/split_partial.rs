use std::collections::HashMap;
use std::convert::Infallible;

use crate::expressions::Expression;
use crate::identifier::pkg_ident::{PackageIdentifier, PackageLocalIdentifier};
use crate::identifier::Identifier;
use crate::package::{Composition, Edge, Export, OracleDef, OracleSig, SplitExport};
use crate::statement::{CodeBlock, InvokeOracleStatement, Statement};
use crate::types::Type;

pub struct SplitPartial;

pub type Error = Infallible;

type Result<T> = std::result::Result<T, Error>;

/*

adv -> A:O1 -> B:O2 -> C:O3

A:O1:Invoc(locals)
A:O1:Invoc(locals)/B:O2:Invoc(locals)

 */

/*
 * ForStep/ForStep/IfBranch/{locals1}Invoc , {inner_locals}
 * |---------locals1-------|
 */

use crate::split::{
    InvocTargetData, SplitOracleDef, SplitOracleSig, SplitPath, SplitPathComponent, SplitType,
};

#[derive(Clone, Debug)]
pub struct SplitInfoEntry {
    pkg_inst_name: String,
    oracle_name: String,
    path: SplitPath,
    locals: Vec<(String, Type)>,
    branches: Vec<(Expression, SplitPath)>,
    original_sig: OracleSig,
}

impl SplitInfoEntry {
    pub fn path(&self) -> &SplitPath {
        &self.path
    }
    pub fn locals(&self) -> &Vec<(String, Type)> {
        &self.locals
    }

    pub fn pkg_inst_name(&self) -> &str {
        self.pkg_inst_name.as_ref()
    }

    pub fn oracle_name(&self) -> &str {
        self.oracle_name.as_ref()
    }

    pub fn branches(&self) -> &Vec<(Expression, SplitPath)> {
        &self.branches
    }

    pub fn split_type(&self) -> Option<&SplitType> {
        Some(self.path.last()?.split_type())
    }

    pub fn original_sig(&self) -> &OracleSig {
        &self.original_sig
    }
}

pub type SplitInfo = Vec<SplitInfoEntry>;

impl super::GameTransform for SplitPartial {
    type Err = Error;

    type Aux = SplitInfo;

    fn transform_game(
        &self,
        game: &Composition,
    ) -> std::result::Result<(crate::package::Composition, Self::Aux), Self::Err> {
        let mut new_game = game.clone();
        let mut sig_mapping: HashMap<
            (String, OracleSig),
            Vec<(Vec<Identifier>, SplitPath, SplitOracleSig)>,
        > = Default::default();

        // dependencies is the game graph in a form where we can start processing the call graph
        // from the leaves, and then remove that leave from this map.
        // We add all called oracles, first the edges and then the exports.
        let mut dependencies: HashMap<(usize, OracleSig), Vec<usize>> = HashMap::new();

        for Edge(from, to, sig) in &game.edges {
            dependencies
                .entry((*to, sig.clone()))
                .or_default()
                .push(*from);
        }

        for Export(pkg_offs, sig) in &game.exports {
            dependencies.entry((*pkg_offs, sig.clone())).or_default();
        }

        // as long as we haven't processed all called oracles, we keep going.
        while !dependencies.is_empty() {
            let keys: Vec<_> = dependencies.keys().cloned().collect();

            for key in &keys {
                let (pkg_inst_offs, sig) = key;
                let pkg_inst = &game.pkgs[*pkg_inst_offs];
                if dependencies[key].is_empty() {
                    // found an oracle that doesn't have unprocessed callees.
                    // transform it!
                    transform_oracle(&mut new_game, *pkg_inst_offs, sig, &mut sig_mapping)?;

                    // of the oracle needed transformation, update the game
                    let mapping_key = (pkg_inst.name.clone(), sig.clone());
                    if let Some(mapping) = sig_mapping.get(&mapping_key) {
                        // remove the old oracle from the exports
                        if let Some(export_position) = new_game
                            .exports
                            .iter()
                            .position(|Export(_, exported_sig)| exported_sig == sig)
                        {
                            new_game.exports.remove(export_position);
                        }

                        // export all new split oracles
                        // note that this is always needed, even if the oracle was not exported
                        // before
                        for split_spec in mapping {
                            let (_, _, split_sig) = split_spec;
                            new_game
                                .split_exports
                                .push(SplitExport(*pkg_inst_offs, split_sig.clone()))
                        }
                    }

                    // remove current oracle from all other oracles dependency lists
                    for dep_list in dependencies.values_mut() {
                        if let Some(pos) = dep_list.iter().position(|x| x == pkg_inst_offs) {
                            dep_list.remove(pos);
                        }
                    }

                    // remove oracle from map to mark it as processed
                    dependencies.remove(key);
                }
            }
        }

        println!("sig mapping after splitting: {sig_mapping:?}");
        for (place, info) in sig_mapping.iter() {
            for (_, split_path, _) in info {
                println!("{place:?} :: {split_path:?} --> {}", split_path.smt_name());
            }
        }

        /* build Aux data structure
         *
         * TODO
         */

        /*
         *
         *
         *
         * [
         *   (cond1, path1)
         *   (cond2, path2)
         *   (true, path3)
         * ]
         *
         * -> (ite cond1 code_path1 (ite cond2 code_path2 code_path3))
         *
         *
         *
         * /Plain
         * /ForStep_i/Plain
         * /ForStep_i/Invoke
         * /ForStep_i/Invoke/ForStep_j/Plain
         *
         *
         *
         *
         */

        let mut partials = vec![];
        for Export(pkg_offs, sig) in &game.exports {
            let pkg_inst_name = &game.pkgs[*pkg_offs].name;
            if let Some(mapping) = sig_mapping.get(&(pkg_inst_name.clone(), sig.clone())) {
                let mut oracle_partials: Vec<_> = mapping
                    .iter()
                    .map(|(_loopvars, path, partial_sig)| {
                        println!("QQQQQ {sig:?}");
                        SplitInfoEntry {
                            pkg_inst_name: pkg_inst_name.clone(),
                            oracle_name: partial_sig.name.clone(),
                            path: path.clone(),
                            locals: partial_sig.partial_vars.clone(),
                            branches: vec![],
                            // next: None,
                            // elsenext: None,
                            original_sig: sig.clone(),
                        }
                    })
                    .collect();

                for i in 0..oracle_partials.len() {
                    let mut new_branches = determine_branches(&oracle_partials, i);
                    oracle_partials[i].branches.append(&mut new_branches);
                }

                partials.extend(oracle_partials.into_iter());
            }
        }

        Ok((new_game, partials))
    }
}

impl Statement {
    fn needs_split(
        &self,
        sig_mapping: &HashMap<
            (String, OracleSig),
            Vec<(Vec<Identifier>, SplitPath, SplitOracleSig)>,
        >,
    ) -> bool {
        match self {
            Statement::For(_, _, _, _, _) => true,
            Statement::IfThenElse(_cond, ifcode, elsecode, _) => {
                ifcode.0.iter().any(|stmt| stmt.needs_split(sig_mapping))
                    || elsecode.0.iter().any(|stmt| stmt.needs_split(sig_mapping))
            }
            Statement::InvokeOracle(InvokeOracleStatement {
                name,
                target_inst_name: Some(target_inst_name),
                ..
            }) => sig_mapping
                .keys()
                .any(|(inst_name, osig)| inst_name == target_inst_name && &osig.name == name),
            Statement::InvokeOracle(InvokeOracleStatement {
                target_inst_name: None,
                ..
            }) => unreachable!(),
            _ => false,
        }
    }
}

fn is_actually_not_split(
    transformed: &[(Vec<Identifier>, SplitPath, CodeBlock, Vec<(String, Type)>)],
) -> bool {
    if transformed.len() == 1 {
        let (_, path, _, _) = &transformed[0];
        *path[0].split_type() == SplitType::Plain
    } else {
        false
    }
}

fn transform_oracle(
    game: &mut Composition,
    pkg_offs: usize,
    osig: &OracleSig,
    sig_mapping: &mut HashMap<
        (String, OracleSig),
        Vec<(Vec<Identifier>, SplitPath, SplitOracleSig)>,
    >,
) -> Result<()> {
    let pkg_inst = &mut game.pkgs[pkg_offs];
    let pkg_name = &pkg_inst.pkg.name;
    let pkg_inst_name = &pkg_inst.name;
    let oracle_offs = pkg_inst
        .pkg
        .oracles
        .iter()
        .position(|OracleDef { sig, .. }| sig == osig)
        .expect("there should be an oracle with this signature");
    let odef = &pkg_inst.pkg.oracles[oracle_offs];
    let oracle_name = &odef.sig.name;

    let mut new_oracles = vec![];
    let mut transformed = transform_codeblock(
        pkg_inst_name,
        pkg_name,
        oracle_name,
        &odef.code,
        SplitPath::empty(),
        vec![],
        vec![],
        sig_mapping,
    );

    // this means we are splitting into a single shard, i.e. not acutally splitting
    if is_actually_not_split(&transformed) {
        return Ok(());
    }

    let mapping_entry = sig_mapping
        .entry((pkg_inst_name.to_string(), osig.clone()))
        .or_default();

    // we treat the last item differently:
    // intermediate items get an empty return type,
    // the last item gets the original return type.
    let (last_loopvars, last_splitpath, last_code, last_locals) = transformed.pop().unwrap();

    for (loopvars, splitpath, oracle_code, oracle_locals) in transformed.clone().into_iter() {
        let new_sig = SplitOracleSig {
            name: oracle_name.clone(),
            args: osig.args.clone(),
            ty: Type::Empty, // <-- note the difference
            partial_vars: oracle_locals.clone(),
            path: splitpath.clone(),
        };

        new_oracles.push(SplitOracleDef {
            sig: new_sig.clone(),
            code: oracle_code,
        });
        mapping_entry.push((loopvars.clone(), splitpath, new_sig))
    }

    let sig = SplitOracleSig {
        name: oracle_name.clone(),
        args: osig.args.clone(),
        ty: osig.ty.clone(), // <-- note the difference
        partial_vars: last_locals.clone(),
        path: last_splitpath.clone(),
    };

    new_oracles.push(SplitOracleDef {
        sig: sig.clone(),
        code: last_code,
    });
    mapping_entry.push((last_loopvars.clone(), last_splitpath, sig));

    pkg_inst.pkg.oracles.remove(oracle_offs);
    pkg_inst.pkg.split_oracles.extend(new_oracles);

    Ok(())
}

fn transform_codeblock(
    pkg_inst_name: &str,
    pkg_name: &str,
    oracle_name: &str,
    code: &CodeBlock,
    prefix: SplitPath,
    mut locals: Vec<(String, Type)>,
    loopvars: Vec<Identifier>,
    sig_mapping: &mut HashMap<
        (String, OracleSig),
        Vec<(Vec<Identifier>, SplitPath, SplitOracleSig)>,
    >,
) -> Vec<(Vec<Identifier>, SplitPath, CodeBlock, Vec<(String, Type)>)> {
    let mut result = vec![];

    let mut split_indices = vec![];
    for i in 0..code.0.len() {
        println!("sig_mapping for {pkg_inst_name} - {oracle_name}: {sig_mapping:?}");
        if code.0[i].needs_split(sig_mapping) {
            split_indices.push((i, locals.clone()));
        }
        for (decl_name, decl_type) in get_declarations(&code.0[i]) {
            match locals
                .iter()
                .position(|(found_name, _)| found_name == &decl_name)
            {
                None => locals.push((decl_name, decl_type)),
                // we already typechecked, so this must hold:
                Some(idx) => {
                    println!("{i}: {:?}", &code.0[i]);
                    assert_eq!(locals[idx].1, decl_type)
                }
            };
        }
    }

    if split_indices.is_empty() {
        result.push((
            loopvars,
            prefix.extended(SplitPathComponent::new(
                pkg_inst_name,
                oracle_name,
                SplitType::Plain,
                0..code.0.len(),
            )),
            code.clone(),
            locals,
        ));

        return result;
    }

    let mut cur_idx = 0;

    for (split_idx, split_locals) in split_indices {
        let mk_single_split_path_component = |split_type| {
            SplitPathComponent::new(
                pkg_inst_name,
                oracle_name,
                split_type,
                split_idx..(split_idx + 1),
            )
        };

        // insert the plain oracles that contain the code between the statemnts that require a
        // split -- but only if there would be statements in that plain oracle
        if split_idx != cur_idx {
            let range = cur_idx..split_idx;
            let split_path_component = SplitPathComponent::new(
                pkg_inst_name,
                oracle_name,
                SplitType::Plain,
                range.clone(),
            );
            result.push((
                loopvars.clone(),
                prefix.extended(split_path_component),
                CodeBlock(code.0[range].to_vec()),
                split_locals.clone(),
            ))
        }

        let stmt = &code.0[split_idx];
        match stmt {
            Statement::IfThenElse(cond, ifcode, elsecode, _) => {
                result.push((
                    loopvars.clone(),
                    prefix.extended(mk_single_split_path_component(SplitType::IfCondition(
                        cond.clone(),
                    ))),
                    CodeBlock(vec![]),
                    split_locals.clone(),
                ));
                result.extend(transform_codeblock(
                    pkg_inst_name,
                    pkg_name,
                    oracle_name,
                    ifcode,
                    prefix.extended(mk_single_split_path_component(SplitType::IfBranch)),
                    split_locals.clone(),
                    loopvars.clone(),
                    sig_mapping,
                ));
                result.extend(transform_codeblock(
                    pkg_inst_name,
                    pkg_name,
                    oracle_name,
                    elsecode,
                    prefix.extended(mk_single_split_path_component(SplitType::ElseBranch)),
                    split_locals.clone(),
                    loopvars.clone(),
                    sig_mapping,
                ));
            }
            Statement::For(id_iter, from, to, code, _) => {
                let mut newloopvars = loopvars.clone();
                newloopvars.push(id_iter.clone());

                result.extend(transform_codeblock(
                    pkg_inst_name,
                    pkg_name,
                    oracle_name,
                    code,
                    prefix.extended(mk_single_split_path_component(SplitType::ForStep(
                        id_iter.clone(),
                        from.clone(),
                        to.clone(),
                    ))),
                    split_locals,
                    newloopvars,
                    sig_mapping,
                ));
            }
            Statement::InvokeOracle(InvokeOracleStatement {
                id,
                opt_idx,
                opt_dst_inst_idx,
                name,
                target_inst_name: Some(target_inst_name),
                args,
                ty,
                file_pos,
                ..
            }) => {
                let file_pos = *file_pos;
                let oracle_name = name;
                let (_, splits) = sig_mapping
                    .iter()
                    .find(|((inst_name, sig), _)| {
                        inst_name == target_inst_name && &sig.name == name
                    })
                    .unwrap();

                let (_, last_splitpath, last_sig) = splits.last().unwrap();

                result.extend(splits.iter().take(splits.len() - 1).map(
                    |(loopvars, splitpath, split_sig)| {
                        let name = &split_sig.name;
                        let invoc_target_data = InvocTargetData {
                            pkg_inst_name: target_inst_name.to_string(),
                            oracle_name: oracle_name.to_string(),
                        };
                        let mut newpath = prefix.extended(mk_single_split_path_component(
                            SplitType::Invoc(invoc_target_data),
                        ));
                        newpath.join(splitpath);
                        (
                            loopvars.clone(),
                            newpath,
                            CodeBlock(vec![Statement::InvokeOracle(InvokeOracleStatement {
                                // TODO: I am not sure if we maybe have to fill out the optional fields,
                                //       but unfortunately this function does not ahve sufficent information.
                                //       If it is needed, we can add it later, but have to pass more context
                                //       into this function.
                                id: Identifier::PackageIdentifier(PackageIdentifier::Local(
                                    PackageLocalIdentifier {
                                        pkg_name: pkg_name.to_string(),
                                        oracle_name: oracle_name.clone(),
                                        name: "_".to_string(),
                                        ty: Type::Empty,
                                        pkg_inst_name: None,
                                        game_name: None,
                                        game_inst_name: None,
                                        theorem_name: None,
                                    },
                                )),
                                name: name.to_string(),
                                opt_idx: None,
                                opt_dst_inst_idx: None,
                                args: args.clone(),
                                target_inst_name: Some(target_inst_name.to_string()),
                                ty: None,
                                file_pos,
                            })]),
                            split_locals.clone(),
                        )
                    },
                ));

                let invoc_target_data = InvocTargetData {
                    pkg_inst_name: target_inst_name.to_string(),
                    oracle_name: oracle_name.to_string(),
                };

                let mut newpath = prefix.extended(mk_single_split_path_component(
                    SplitType::Invoc(invoc_target_data),
                ));
                newpath.join(last_splitpath);
                result.push((
                    loopvars.clone(),
                    newpath,
                    CodeBlock(vec![Statement::InvokeOracle(InvokeOracleStatement {
                        id: id.clone(),
                        opt_idx: opt_idx.clone(),
                        opt_dst_inst_idx: opt_dst_inst_idx.clone(),
                        name: last_sig.name.clone(),
                        args: args.clone(),
                        target_inst_name: Some(target_inst_name.to_string()),
                        ty: ty.clone(),
                        file_pos,
                    })]),
                    split_locals,
                ))
            }
            _ => unreachable!(),
        }

        cur_idx = split_idx;
    }

    let rest = &code.0[cur_idx + 1..];
    if !rest.is_empty() {
        result.push((
            loopvars.clone(),
            prefix.extended(SplitPathComponent::new(
                pkg_inst_name,
                oracle_name,
                SplitType::Plain,
                (cur_idx + 1)..code.0.len(),
            )),
            CodeBlock(rest.to_vec()),
            locals,
        ));
    }

    result
}

fn get_declarations(stmt: &Statement) -> Vec<(String, Type)> {
    match stmt {
        Statement::Parse(ids, expr, _) => {
            let Type::Tuple(types) = expr.get_type() else {
                panic!("value to parse should have been a tuple, we already typechecked. But it is {expr:?}");
            };

            assert_eq!(
                ids.len(),
                types.len(),
                "ids and exprs must be of same length"
            );

            let names = ids.iter().map(Identifier::ident);
            names.zip(types).collect()
        }
        Statement::Assign(Identifier::Generated(id_name, _), Some(idx), expr, _) => vec![(
            id_name.to_string(),
            Type::Table(Box::new(idx.get_type().clone()), {
                let expr_outer_type = expr.get_type();
                let expr_inner_type = match expr_outer_type {
                    Type::Maybe(inner) => inner,
                    other => unreachable!("assignment to table must be a maybe, got {:?}", other),
                };

                expr_inner_type.clone()
            }),
        )],
        Statement::Assign(Identifier::Generated(id_name, _), None, expr, _) => {
            vec![(id_name.to_string(), expr.get_type().clone())]
        }
        Statement::InvokeOracle(InvokeOracleStatement {
            id: Identifier::Generated(id_name, _),
            ty: Some(ty),
            opt_idx: Some(idx),
            ..
        })
        | Statement::Sample(Identifier::Generated(id_name, _), Some(idx), _, ty, _) => vec![(
            id_name.to_string(),
            Type::Table(Box::new(idx.get_type().clone()), Box::new(ty.clone())),
        )],
        Statement::InvokeOracle(InvokeOracleStatement {
            id: Identifier::Generated(id_name, _),
            ty: Some(ty),
            opt_idx: None,
            ..
        })
        | Statement::Sample(Identifier::Generated(id_name, _), None, _, ty, _) => {
            vec![(id_name.to_string(), ty.clone())]
        }
        _ => vec![],
    }
}

/*
 * fn strip_plain(path) -> Option<path>;
 *
 * fn determine_what_to_do(partials[i], partials[i+1]) -> (next, elsenext);
 *
 * for i in 0..(len-1)  {
 *   (next, elsenext) = determine_what_to_do(oracle_partials[i], oracle_partials[i+1])
 *   oracle_partials[i].next = next;
 *   oracle_partials[i].elsenext = elsenext;
 *
 * }
 *
 * */

/*
 * /Plain
 *   ->
 * /Plain/ForStep/Plain
 *
 *
 * /Plain/ForStep/Plain
 *   ->
 * /Plain/IfCondition
 *
 *
 * /Plain/ForStep/Plain
 *   ->
 * /Plain/Invoc
 *
 *
 * /Plain/Invoc/callee_path
 *
 *
 * PRF.Eval:
 *   k<-Get()
 *   return f(k)
 *   ->
 *   Invoc/Invoc/Invoc/Forstep/Plain
 *   Invoc/Invoc/Plain
 *   Invoc/Plain
 *   Plain
 *
 *
 * KeyFilter.Get():
 *   k<-Get()
 *   if k == 0:
 *     k' <-$ rand();
 *     return k'
 *   ->
 *   Invoc/Invoc/Forstep/Plain
 *   Invoc/Plain
 *   Plain
 *
 *  Key.Get():
 *    Log()
 *    return k
 *    ->
 *    Invoc/ForStep/Plain
 *    Invoc/Plain
 *    Plain
 *
 *
 * Log.Log():
 *   for {...}
 *   return
 *   ->
 *   ForStep/Plain
 *   Plain
 * */

fn determine_branches(entries: &[SplitInfoEntry], i: usize) -> Vec<(Expression, SplitPath)> {
    let entry = &entries[i];
    let path = entry.path();

    let mut out = vec![];

    for (j, path_elem) in path.path().iter().enumerate().rev() {
        match path_elem.split_type() {
            SplitType::Plain => {}
            SplitType::Invoc(_) => {}
            SplitType::ForStep(loopvar, _loopfrom, loopto) => {
                let cond = Expression::And(vec![Expression::Equals(vec![
                    Expression::Identifier(loopvar.clone()),
                    loopto.clone(),
                ])]);
                let first_path_of_for = entries
                    .iter()
                    .find(|entry| &entry.path().path()[j] == path_elem)
                    .unwrap()
                    .path
                    .clone();
                out.push((cond, first_path_of_for))
            }
            SplitType::IfCondition(cond) => {
                let (ifcond_component, ifpath) = path.clone().basename();
                let ifcond_component = ifcond_component.unwrap();
                let ifpath = ifpath.extended(SplitPathComponent {
                    split_type: SplitType::IfBranch,
                    ..ifcond_component.clone()
                });

                let (_, elsepath) = path.clone().basename();
                let elsepath = elsepath.extended(SplitPathComponent {
                    split_type: SplitType::ElseBranch,
                    ..ifcond_component
                });

                out.push((cond.clone(), ifpath));
                out.push((Expression::BooleanLiteral("true".to_string()), elsepath));
            }
            SplitType::IfBranch => {
                let remaining_entries = &entries[i + 1..];
                let first_non_else = remaining_entries
                    .iter()
                    .find(|entry| !matches!(entry.split_type(), Some(SplitType::ElseBranch)));
                if let Some(first_non_else) = first_non_else {
                    out.push((
                        Expression::BooleanLiteral("true".to_string()),
                        first_non_else.path().clone(),
                    ));
                }
            }
            SplitType::ElseBranch => {
                let remaining_entries = &entries[i + 1..];
                let first_non_if = remaining_entries
                    .iter()
                    .find(|entry| !matches!(entry.split_type(), Some(SplitType::IfBranch)));
                if let Some(first_non_if) = first_non_if {
                    out.push((
                        Expression::BooleanLiteral("true".to_string()),
                        first_non_if.path().clone(),
                    ));
                }
            }
        }
    }

    if entries.len() > i + 1 {
        out.push((
            Expression::BooleanLiteral("true".to_string()),
            entries[i + 1].path().clone(),
        ))
    }

    // println!(
    //     "entries[{}]: {entries:#?} i: {i} out: {out:?}",
    //     entries.len()
    // );

    out
}

#[cfg(test)]
mod test {
    // use std::default::Default;
    //
    // use crate::{
    //     expressions::Expression,
    //     identifier::Identifier,
    //     statement::{CodeBlock, Statement},
    // };
    //
    // use super::*;
    //
    // #[test]
    // fn oracle_transform_splits_around_for() {
    //     let id_i = Identifier::new_scalar("i");
    //     let id_foo = Identifier::new_scalar("foo");
    //     let expr_i = Expression::Identifier(id_i.clone());
    //     let expr_foo = Expression::Identifier(id_foo.clone());
    //
    //     let code = CodeBlock(vec![
    //         Statement::Assign(
    //             id_foo.clone(),
    //             None,
    //             Expression::IntegerLiteral("2".to_string()),
    //         ),
    //         Statement::For(
    //             id_i.clone(),
    //             Expression::IntegerLiteral("0".to_string()),
    //             Expression::IntegerLiteral("10".to_string()),
    //             CodeBlock(vec![Statement::Assign(
    //                 Identifier::new_scalar("foo"),
    //                 None,
    //                 Expression::Add(Box::new(expr_i.clone()), Box::new(expr_foo.clone())),
    //             )]),
    //         ),
    //         Statement::Return(Some(expr_foo.clone())),
    //     ]);
    //
    //     let mut sig_mapping = Default::default();
    //
    //     let out = transform_codeblock(
    //         "the-pkg",
    //         "TheOracle",
    //         &code,
    //         SplitPath::empty(),
    //         vec![],
    //         &mut sig_mapping,
    //     );
    //
    //     println!("{out:#?}");
    // }
}
