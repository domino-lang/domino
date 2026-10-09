use crate::util::smtsolver::SmtSolverBackend;

pub trait ProveConfiguration {
    type SolverBackend: SmtSolverBackend;

    fn solver_backend(&self) -> Self::SolverBackend;

    fn transcript(&self) -> bool;

    fn parallel(&self) -> usize;

    fn theorem_requested(&self, theorem: &str) -> bool;

    fn gamehop_requested(&self, gamehop: usize) -> bool;

    fn claim_requested(&self, claim: &str) -> bool;

    fn oracle_requested(&self, export: &str) -> bool;

    fn invariant_start_requested(&self) -> bool;

    fn injectivity_requested(&self) -> bool;

    fn restricted_requests(&self) -> bool;
}

#[cfg(test)]
pub(crate) mod test {
    use super::ProveConfiguration;
    use crate::util::smtsolver::process::{ProcessSmtSolverBackend, SolverVariant};

    pub(crate) struct TestProveConfiguration;

    impl ProveConfiguration for TestProveConfiguration {
        type SolverBackend = ProcessSmtSolverBackend;

        fn solver_backend(&self) -> Self::SolverBackend {
            ProcessSmtSolverBackend::new(SolverVariant::Cvc5)
        }

        fn transcript(&self) -> bool {
            false
        }

        fn parallel(&self) -> usize {
            1
        }

        fn theorem_requested(&self, _theorem: &str) -> bool {
            true
        }

        fn gamehop_requested(&self, _gamehop: usize) -> bool {
            true
        }

        fn claim_requested(&self, _claim: &str) -> bool {
            true
        }

        fn oracle_requested(&self, _export: &str) -> bool {
            true
        }

        fn invariant_start_requested(&self) -> bool {
            true
        }

        fn injectivity_requested(&self) -> bool {
            true
        }

        fn restricted_requests(&self) -> bool {
            false
        }
    }
}
