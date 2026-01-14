use thiserror::Error;

use crate::util::prover::ProverResponse;
use crate::writers::smt::exprs::SmtExpr;
use std::fmt::Write;
use wasm_bindgen::prelude::wasm_bindgen;

#[derive(Clone, Debug, Copy)]
pub enum ProverBackend {
    Cvc5,
}

#[wasm_bindgen(module = "/crates/domino-web/static/cvc.js")]
extern "C" {
    type CVC;

    #[wasm_bindgen]
    fn get_cvc() -> CVC;

    type Solver;

    #[wasm_bindgen(constructor)]
    fn new(module: &CVC) -> Solver;

    #[wasm_bindgen(method)]
    fn check_sat(this: &Solver) -> String;

    #[wasm_bindgen(method)]
    fn get_model(this: &Solver) -> String;

    #[wasm_bindgen(method)]
    fn add_smt(this: &Solver, content: &str);
}

pub struct Communicator {
    cvc: Solver,
}

#[derive(Debug, Error)]
pub enum Error {
    #[error("error writing to prover process: {0}")]
    WriteError(#[from] std::fmt::Error),
    #[error("prover error: {0}")]
    ProverError(String),
}

pub type Result<T> = std::result::Result<T, Error>;

impl Communicator {
    pub fn new(backend: ProverBackend) -> Result<Self> {
        Ok(Communicator {
            cvc: Solver::new(&get_cvc()),
        })
    }

    pub fn new_with_transcript<W: std::io::Write + Send + Sync + 'static>(
        backend: ProverBackend,
        transcript: W,
    ) -> Result<Self> {
        Ok(Communicator {
            cvc: Solver::new(&get_cvc()),
        })
    }

    pub fn write_smt<I: Into<SmtExpr>>(&mut self, expr: I) -> Result<()> {
        let mut buffer = String::new();
        write!(buffer, "{}", expr.into())?;

        self.cvc.add_smt(&buffer);
        Ok(())
    }

    pub fn get_model(&mut self) -> Result<String> {
        Ok(self.cvc.get_model())
    }

    pub fn check_sat(&mut self) -> Result<ProverResponse> {
        Ok(match self.cvc.check_sat().as_ref() {
            "sat" => ProverResponse::Sat,
            "unsat" => ProverResponse::Unsat,
            "unknown" => ProverResponse::Unknown,
            _ => unreachable!(),
        })
    }
}

impl std::fmt::Write for Communicator {
    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        self.cvc.add_smt(s);
        Ok(())
    }
}
