// SPDX-License-Identifier: MIT OR Apache-2.0

//! `domino easycrypt debug` (story 19 §4.5): lockstep execution on the EasyCrypt listing,
//! for every equivalence proofstep of an exported theorem and every exported oracle.
//!
//! Selection is exactly that of `check-alignment` and `prove`: `--proofstep` and
//! `--oracle` narrow it. Each oracle is one call of
//! [`run_lockstep_command`], the call `prove` makes, with the options `prove` uses
//! ([`LockstepDebugOptions::easycrypt`]), so the two cannot drift. **Claims have no meaning
//! here**: EasyCrypt has no `no-abort` and no project lemmas, so the claim set is the
//! no-dependency one and there is no `--claim`.
//!
//! The artifacts of an oracle sit beside the export they describe:
//! `<out>/<theorem>/!debug!/<left>-<right>/<oracle>/`.

use std::path::Path;
use std::sync::atomic::AtomicBool;

use thiserror::Error;

use crate::debug::driver::DebugError;
use crate::debug::lockstep_run::{run_lockstep_command, LockstepDebugOptions};
use crate::debug::progress::NopObserver;
use crate::debug::sweep::{is_interrupted, SweepEntry, Target};
use crate::easycrypt::check::{equivalence_setup, CheckError};
use crate::project::Project;
use crate::theorem::Theorem;
use crate::transforms::theorem_transforms::EasyCryptTransform;
use crate::transforms::TheoremTransform;
use crate::util::smtsolver::SmtSolverBackend;
use crate::writers::easycrypt::export::ExportedTheorem;

use super::tactics::debug_dir;

#[derive(Debug, Error)]
pub enum EcDebugError {
    #[error(transparent)]
    Check(#[from] CheckError),
    #[error(transparent)]
    Debug(#[from] DebugError),
}

#[derive(Debug, Clone, Default)]
pub struct EcDebugOptions {
    /// Only this proofstep (index into the theorem's game hops).
    pub proofstep: Option<usize>,
    /// Only this exported oracle.
    pub oracle: Option<String>,
    /// Per-query solver timeout in milliseconds; a timeout counts as `unknown`.
    pub timeout_ms: Option<u64>,
}

/// Run lockstep execution on every selected oracle of `exported` (the export of `theorem`,
/// already written to `theorem_out`, the theorem's own output directory). `on_finished` sees
/// each oracle's entry as it completes. A `Ctrl-C` (`stop`) ends the sweep after the oracle in
/// flight; what finished is returned.
pub fn debug_theorem<P, B>(
    theorem: &Theorem<'_>,
    project: &P,
    exported: &ExportedTheorem,
    theorem_out: &Path,
    backend: &B,
    options: &EcDebugOptions,
    stop: Option<&AtomicBool>,
    on_finished: &mut dyn FnMut(&SweepEntry),
) -> Result<Vec<SweepEntry>, EcDebugError>
where
    P: Project,
    B: SmtSolverBackend,
{
    let (theorem_ec, _aux) = EasyCryptTransform
        .transform_theorem(theorem)
        .map_err(CheckError::from)?;
    let mut entries = Vec::new();
    for eq in &exported.equivalences {
        if options.proofstep.is_some_and(|p| p != eq.proofstep) {
            continue;
        }
        let setup = equivalence_setup(&theorem_ec, eq)?;
        if let Some(wanted) = &options.oracle {
            if !setup.oracles.iter().any(|(name, _)| name == wanted) {
                return Err(CheckError::NoSuchOracle {
                    oracle: wanted.clone(),
                    file: eq.proof_file.clone(),
                }
                .into());
            }
        }
        for (oracle, _) in &setup.oracles {
            if options.oracle.as_deref().is_some_and(|w| w != oracle) {
                continue;
            }
            let run = run_lockstep_command(
                project,
                &theorem.name,
                eq.proofstep,
                oracle,
                &LockstepDebugOptions::easycrypt(options.timeout_ms),
                backend,
                Some(debug_dir(theorem_out, &eq.left_name, &eq.right_name, oracle)),
                &mut NopObserver,
                stop,
            )?;
            let entry = SweepEntry::from_lockstep(
                Target {
                    theorem: theorem.name.clone(),
                    proofstep: eq.proofstep,
                    left: eq.left_name.clone(),
                    right: eq.right_name.clone(),
                    oracle: oracle.clone(),
                },
                &run,
            );
            on_finished(&entry);
            let interrupted = is_interrupted(&entry);
            entries.push(entry);
            if interrupted {
                return Ok(entries);
            }
        }
    }
    Ok(entries)
}
