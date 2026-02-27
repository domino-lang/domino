// SPDX-License-Identifier: MIT OR Apache-2.0

use itertools::Itertools;
use rayon::iter::{IntoParallelIterator, ParallelIterator};
use std::fmt::Write;
use std::io::Write as _;

use crate::ui::{ProveLemmaUI, ProveOracleUI, ProveProofstepUI};
use crate::{
    gamehops::equivalence::{
        error::{Error, Result},
        Equivalence,
    },
    project::Project,
    theorem::Theorem,
    transforms::{theorem_transforms::EquivalenceTransform, TheoremTransform},
    util::prover_process::{Communicator, ProverBackend, ProverResponse},
    writers::smt::exprs::SmtExpr,
};

use super::EquivalenceContext;

fn verify_oracles(
    project: &Project,
    eqctx: &EquivalenceContext,
    backend: ProverBackend,
    transcript: bool,
    req_oracles: Vec<(&str, impl ProveOracleUI)>,
) -> Result<()> {
    let eq = eqctx.equivalence();

    let mut prover = if transcript {
        let oracle = if req_oracles.len() == 1 {
            Some(req_oracles[0].0)
        } else {
            None
        };

        let transcript_file: std::fs::File = project
            .get_joined_smt_file(eq.left_name(), eq.right_name(), oracle)
            .unwrap();

        Communicator::new_with_transcript(backend, transcript_file)?
    } else {
        Communicator::new(backend)?
    };
    std::thread::sleep(std::time::Duration::from_millis(20));

    log::debug!(
        "emitting base declarations for {}-{}",
        eq.left_name,
        eq.right_name
    );
    prover.write_smt(SmtExpr::Comment("\n".to_string()))?;
    prover.write_smt(SmtExpr::Comment("base declarations:\n".to_string()))?;
    eqctx.emit_base_declarations(&mut prover)?;
    log::debug!(
        "emitting theorem paramfuncs for {}-{}",
        eq.left_name,
        eq.right_name
    );
    prover.write_smt(SmtExpr::Comment("\n".to_string()))?;
    prover.write_smt(SmtExpr::Comment("theorem param funcs:\n".to_string()))?;
    eqctx.emit_theorem_paramfuncs(&mut prover)?;
    log::debug!(
        "emitting game definitions for {}-{}",
        eq.left_name,
        eq.right_name,
    );
    prover.write_smt(SmtExpr::Comment("\n".to_string()))?;
    prover.write_smt(SmtExpr::Comment("game definitions:\n".to_string()))?;
    eqctx.emit_game_definitions(&mut prover)?;
    log::debug!(
        "emitting const declarations for {}-{}",
        eq.left_name,
        eq.right_name
    );
    eqctx.emit_constant_declarations(&mut prover)?;

    for (export, ref mut ui) in req_oracles {
        ui.start();
        let claims = eqctx.equivalence.proof_tree_by_oracle_name(export);

        log::info!("verify: oracle:{export:?}");
        writeln!(prover, "(push 1)").unwrap();
        eqctx.emit_return_value_helpers(&mut prover, export)?;
        eqctx.emit_invariant(&mut prover, export)?;

        for (claim, mut ui) in claims
            .iter()
            .map(|claim| (claim, ui.start_lemma(claim.name())))
            .collect::<Vec<_>>()
        {
            ui.start();
            writeln!(prover, "(push 1)").unwrap();
            eqctx.emit_claim_assert(&mut prover, export, claim)?;
            match prover.check_sat()? {
                ProverResponse::Unsat => {}
                response => {
                    let modelfile = prover.get_model().map(|(modelstring, _model)| {
                        let mut modelfile =
                            tempfile::Builder::new().suffix(".smt2").tempfile().unwrap();
                        modelfile.write_all(modelstring.as_bytes()).unwrap();
                        let (_, fname) = modelfile.keep().unwrap();
                        fname
                    });
                    prover.close();
                    return Err(Error::ClaimTheoremFailed {
                        claim_name: claim.name().to_string(),
                        oracle_name: export.to_string(),
                        response,
                        modelfile,
                    });
                }
            }
            writeln!(prover, "(pop 1)").unwrap();
            ui.finish();
        }

        writeln!(prover, "(pop 1)").unwrap();
        ui.finish();
    }
    Ok(())
}

pub fn verify(
    project: &Project,
    ui: &impl ProveProofstepUI,
    eq: &Equivalence,
    orig_theorem: &Theorem,
    backend: ProverBackend,
    transcript: bool,
    req_oracle: &Option<String>,
) -> Result<()> {
    let (theorem, auxs) = EquivalenceTransform
        .transform_theorem(orig_theorem)
        .unwrap();

    let eqctx = EquivalenceContext {
        equivalence: eq,
        theorem: &theorem,
        auxs: &auxs,
    };

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

    let oracle_sequence: Vec<_> = eqctx
        .oracle_sequence()
        .into_iter()
        .filter_map(|export| {
            if let Some(name) = req_oracle {
                if export.name() == *name {
                    Some((export.name(), ui.start_oracle(export.name().to_string())))
                } else {
                    None
                }
            } else {
                None
            }
        })
        .collect();

    verify_oracles(project, &eqctx, backend, transcript, oracle_sequence)?;

    Ok(())
}

pub fn verify_parallel(
    project: &Project,
    ui: &impl ProveProofstepUI,
    eq: &Equivalence,
    orig_theorem: &Theorem,
    backend: ProverBackend,
    transcript: bool,
    parallel: usize,
    req_oracle: &Option<String>,
) -> Result<()> {
    let (theorem, auxs) = EquivalenceTransform
        .transform_theorem(orig_theorem)
        .unwrap();

    let eqctx = EquivalenceContext {
        equivalence: eq,
        theorem: &theorem,
        auxs: &auxs,
    };

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

    let oracle_sequence: Vec<_> = eqctx
        .oracle_sequence()
        .iter()
        .filter_map(|export| {
            if let Some(name) = req_oracle {
                if export.name() == *name {
                    Some((export.name(), ui.start_oracle(export.name().to_string())))
                } else {
                    None
                }
            } else {
                Some((export.name(), ui.start_oracle(export.name().to_string())))
            }
        })
        .collect();

    rayon::ThreadPoolBuilder::new()
        .num_threads(parallel)
        .build()
        .unwrap()
        .install(|| -> Result<()> {
            let failed_oracles: Vec<_> = oracle_sequence
                .into_par_iter()
                .map(|export| -> (&str, Result<()>) {
                    let name = export.0;
                    let result = verify_oracles(project, &eqctx, backend, transcript, vec![export]);
                    if let Err(ref e) = result {
                        ui.println(&format!("{e}")).unwrap();
                    }
                    (name, result)
                })
                .filter_map(|(name, res): (&str, Result<()>)| {
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
