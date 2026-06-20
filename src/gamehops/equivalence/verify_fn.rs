// SPDX-License-Identifier: MIT OR Apache-2.0

use itertools::Itertools;
use rayon::iter::{IntoParallelRefIterator, ParallelIterator};
use std::io::Write as _;
use std::sync::{Arc, Mutex};

use crate::{
    gamehops::equivalence::{
        error::{Error, Result},
        Equivalence,
    },
    package::Export,
    project::Project,
    theorem::Theorem,
    transforms::{theorem_transforms::EquivalenceTransform, TheoremTransform},
    ui::TheoremUI,
    util::smtsolver::{SmtSolver, SmtSolverBackend, SmtSolverResponse},
    writers::smt::{contexts::EquivalenceContext, exprs::SmtExpr},
};

fn verify_oracle<UI: TheoremUI>(
    project: &impl Project,
    ui: Arc<Mutex<&mut UI>>,
    eqctx: &EquivalenceContext,
    backend: &impl SmtSolverBackend,
    transcript: bool,
    req_oracles: &[&Export],
) -> Result<()> {
    let eq = eqctx.equivalence();
    let proofstep_name = format!("{} == {}", eq.left_name(), eq.right_name());
    let mut smt = Vec::new();

    //std::thread::sleep(std::time::Duration::from_millis(20));

    log::debug!(
        "emitting base declarations for {}-{}",
        eq.left_name,
        eq.right_name
    );
    smt.push(SmtExpr::Comment("\n".to_string()));
    smt.push(SmtExpr::Comment("base declarations:\n".to_string()));
    smt.append(&mut eqctx.emit_base_declarations());
    log::debug!(
        "emitting theorem paramfuncs for {}-{}",
        eq.left_name,
        eq.right_name
    );
    smt.push(SmtExpr::Comment("\n".to_string()));
    smt.push(SmtExpr::Comment("theorem param funcs:\n".to_string()));
    smt.append(&mut eqctx.emit_theorem_paramfuncs());
    log::debug!(
        "emitting game definitions for {}-{}",
        eq.left_name,
        eq.right_name
    );
    smt.push(SmtExpr::Comment("\n".to_string()));
    smt.push(SmtExpr::Comment("game definitions:\n".to_string()));
    smt.append(&mut eqctx.emit_game_definitions());

    log::debug!(
        "emitting const declarations for {}-{}",
        eq.left_name,
        eq.right_name
    );
    smt.append(&mut eqctx.emit_constant_declarations());

    for export in req_oracles {
        let mut smt = smt.clone();

        let claims = eqctx.equivalence().proof_tree_by_oracle_name(export.name());
        ui.lock().unwrap().start_oracle(
            &eqctx.theorem().name,
            &proofstep_name,
            export.name(),
            claims.len().try_into().unwrap(),
        );

        log::info!("verify: oracle:{export:?}");
        smt.append(&mut eqctx.emit_return_value_helpers(export.name()));
        smt.append(&mut eqctx.emit_auto_randomness(export.name()));
        smt.append(&mut eqctx.emit_invariant(export.name()));

        for claim in claims {
            ui.lock().unwrap().start_lemma(
                &eqctx.theorem().name,
                &proofstep_name,
                export.name(),
                claim.name(),
            );

            if !claim.is_admitted() {
                let mut smt = smt.clone();
                let mut solver = {
                    if transcript {
                        let transcript_file: std::fs::File = project
                            .get_joined_smt_file(
                                eq.left_name(),
                                eq.right_name(),
                                export.name(),
                                claim.name(),
                            )
                            .unwrap();

                        backend.new_smtsolver_with_transcript(transcript_file)?
                    } else {
                        backend.new_smtsolver()?
                    }
                };
                std::thread::sleep(std::time::Duration::from_millis(20));

                smt.append(&mut eqctx.emit_claim_assert(export.name(), &claim));
                for entry in smt {
                    solver.write_smt(entry)?;
                }

                match solver.check_sat()? {
                    SmtSolverResponse::Unsat => {}
                    response => {
                        let modelfile = solver.get_model().map(|(modelstring, _model)| {
                            let mut modelfile =
                                tempfile::Builder::new().suffix(".smt2").tempfile().unwrap();
                            modelfile.write_all(modelstring.as_bytes()).unwrap();
                            let (_, fname) = modelfile.keep().unwrap();
                            fname
                        });
                        solver.close();
                        return Err(Error::ClaimTheoremFailed {
                            claim_name: claim.name().to_string(),
                            oracle_name: export.name().to_string(),
                            response,
                            modelfile,
                        });
                    }
                }
            }
            ui.lock().unwrap().finish_lemma(
                &eqctx.theorem().name,
                &proofstep_name,
                export.name(),
                claim.name(),
            );
        }
        ui.lock()
            .unwrap()
            .finish_oracle(&eqctx.theorem().name, &proofstep_name, export.name());
    }
    Ok(())
}

pub fn verify<UI: TheoremUI>(
    project: &impl Project,
    ui: &mut UI,
    eq: &Equivalence,
    orig_theorem: &Theorem,
    backend: &impl SmtSolverBackend,
    transcript: bool,
    req_oracle: &Option<String>,
) -> Result<()> {
    let (theorem, auxs) = EquivalenceTransform
        .transform_theorem(orig_theorem)
        .unwrap();

    let mut eqctx = EquivalenceContext::new(eq, &theorem, &auxs);
    eqctx.load_invariants(project)?;

    let export_difference = eqctx.verify_exports_match();
    if !export_difference.0.is_empty() || !export_difference.1.is_empty() {
        return Err(Error::CompositionExportsMismatch {
            left_game_inst_name: eq.left_name.clone(),
            right_game_inst_name: eq.right_name.clone(),
            mismatching_export_name: format!(
                "left: {}, right: {}",
                export_difference
                    .0
                    .into_iter()
                    .map(|sig| format!("{sig}"))
                    .join(", "),
                export_difference
                    .1
                    .into_iter()
                    .map(|sig| format!("{sig}"))
                    .join(", "),
            ),
        });
    }

    let proofstep_name = format!("{} == {}", eq.left_name(), eq.right_name());
    let oracle_sequence: Vec<_> = eqctx
        .oracle_sequence()
        .into_iter()
        .filter(|export| {
            if let Some(name) = req_oracle {
                export.name() == *name
            } else {
                true
            }
        })
        .collect();

    ui.proofstep_set_oracles(
        &theorem.name,
        &proofstep_name,
        oracle_sequence.len().try_into().unwrap(),
    );

    let ui = Arc::new(Mutex::new(ui));

    verify_oracle(project, ui, &eqctx, backend, transcript, &oracle_sequence)?;

    Ok(())
}

pub fn verify_parallel<UI: TheoremUI + std::marker::Send>(
    project: &(impl Project + Sync),
    ui: &mut UI,
    eq: &Equivalence,
    orig_theorem: &Theorem,
    backend: &(impl SmtSolverBackend + Sync),
    transcript: bool,
    parallel: usize,
    req_oracle: &Option<String>,
) -> Result<()> {
    let (theorem, auxs) = EquivalenceTransform
        .transform_theorem(orig_theorem)
        .unwrap();

    let mut eqctx = EquivalenceContext::new(eq, &theorem, &auxs);
    eqctx.load_invariants(project)?;

    let export_difference = eqctx.verify_exports_match();
    if !export_difference.0.is_empty() || !export_difference.1.is_empty() {
        return Err(Error::CompositionExportsMismatch {
            left_game_inst_name: eq.left_name.clone(),
            right_game_inst_name: eq.right_name.clone(),
            mismatching_export_name: format!(
                "left: {}, right: {}",
                export_difference
                    .0
                    .into_iter()
                    .map(|sig| format!("{sig}"))
                    .join(", "),
                export_difference
                    .1
                    .into_iter()
                    .map(|sig| format!("{sig}"))
                    .join(", "),
            ),
        });
    }

    let proofstep_name = format!("{} == {}", eq.left_name(), eq.right_name());
    let oracle_sequence: Vec<_> = eqctx
        .oracle_sequence()
        .into_iter()
        .filter(|export| {
            if let Some(name) = req_oracle {
                export.name() == *name
            } else {
                true
            }
        })
        .collect();

    ui.proofstep_set_oracles(
        &theorem.name,
        &proofstep_name,
        oracle_sequence.len().try_into().unwrap(),
    );

    let ui = Arc::new(Mutex::new(ui));

    rayon::ThreadPoolBuilder::new()
        .num_threads(parallel + 1) // one process is reserved for the "main" method
        .build()
        .unwrap()
        .install(|| -> Result<()> {
            let failed_oracles: Vec<_> = oracle_sequence
                .par_iter()
                .map(|export| -> (&str, Result<()>) {
                    let result =
                        verify_oracle(project, ui.clone(), &eqctx, backend, transcript, &[*export]);
                    if let Err(ref e) = result {
                        ui.lock().unwrap().println(&format!("{e}")).unwrap();
                    }
                    (export.name(), result)
                })
                .filter_map(|(name, res)| {
                    if let Err(err) = res {
                        Some((name.to_string(), err))
                    } else {
                        None
                    }
                })
                .collect();
            if failed_oracles.is_empty() {
                Ok(())
            } else {
                Err(Error::ParallelEquivalenceError {
                    left_game_inst_name: eq.left_name.clone(),
                    right_game_inst_name: eq.right_name.clone(),
                    failed_oracles,
                })
            }
        })
}
