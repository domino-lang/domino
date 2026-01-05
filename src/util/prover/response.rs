use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProverResponse {
    Sat,
    Unsat,
    Unknown,
}

impl ProverResponse {
    /// Returns `true` if the prover response is [`Sat`].
    ///
    /// [`Sat`]: ProverResponse::Sat
    #[must_use]
    pub fn is_sat(&self) -> bool {
        matches!(self, Self::Sat)
    }

    /// Returns `true` if the prover response is [`Unsat`].
    ///
    /// [`Unsat`]: ProverResponse::Unsat
    #[must_use]
    pub fn is_unsat(&self) -> bool {
        matches!(self, Self::Unsat)
    }

    /// Returns `true` if the prover response is [`Unknown`].
    ///
    /// [`Unknown`]: ProverResponse::Unknown
    #[must_use]
    pub fn is_unknown(&self) -> bool {
        matches!(self, Self::Unknown)
    }
}

impl fmt::Display for ProverResponse {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ProverResponse::Sat => write!(f, "sat"),
            ProverResponse::Unsat => write!(f, "unsat"),
            ProverResponse::Unknown => write!(f, "unknown"),
        }
    }
}
