use sspverif::util::prover::ProverResponse;
use sspverif::util::smtmodel::SmtModel;
use sspverif::util::smtparser::parse_model;
use sspverif::writers::smt::exprs::SmtExpr;

use std::fmt::Write;
use wasm_bindgen::prelude::wasm_bindgen;

use sspverif::util::prover::{Error, Prover, ProverFactory, Result};

#[wasm_bindgen(module = "/static/cvc.js")]
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

pub struct WebProverFactory;

impl ProverFactory for WebProverFactory {
    fn new_prover(&self) -> Result<impl Prover> {
        Ok(Communicator {
            cvc: Solver::new(&get_cvc()),
        })
    }
    fn new_prover_with_transcript<W: std::io::Write + Send + Sync + 'static>(
        &self,
        _writer: W,
    ) -> Result<impl Prover> {
        Ok(Communicator {
            cvc: Solver::new(&get_cvc()),
        })
    }
    fn transcript_enabled(&self) -> bool {
        false
    }
}

pub struct Communicator {
    cvc: Solver,
}

impl Prover for Communicator {
    fn write_smt<I: Into<SmtExpr>>(&mut self, expr: I) -> Result<()> {
        let mut buffer = String::new();
        write!(buffer, "{}", expr.into())?;

        self.cvc.add_smt(&buffer);
        Ok(())
    }

    fn get_model(&mut self) -> Result<(String, SmtModel)> {
        let data = self.cvc.get_model();
        let (model, _) = parse_model(&data).unwrap();
        Ok((data, model))
    }

    fn check_sat(&mut self) -> Result<ProverResponse> {
        Ok(match self.cvc.check_sat().as_ref() {
            "sat" => ProverResponse::Sat,
            "unsat" => ProverResponse::Unsat,
            "unknown" => ProverResponse::Unknown,
            _ => unreachable!(),
        })
    }
    fn close(&mut self) {}
}

impl std::fmt::Write for Communicator {
    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        self.cvc.add_smt(s);
        Ok(())
    }
}
