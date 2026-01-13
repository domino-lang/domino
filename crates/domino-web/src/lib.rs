use std::io::Cursor;
use wasm_bindgen::prelude::wasm_bindgen;

use sspverif::util::prover::ProverBackend;
use web_sys::console::{error_1, log_1};

#[wasm_bindgen(module = "/static/cvc.js")]
extern "C" {
    type CVC;

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

#[wasm_bindgen]
pub fn proofsteps(zipfile: &[u8]) -> String {
    let zipfile = Cursor::new(zipfile);
    let files = sspverif::project::Files::load_zip(zipfile).unwrap();
    let project = match sspverif::project::Project::load(&files) {
        Ok(project) => project,
        Err(e) => {
            error_1(&format!("{}", e).into());
            unreachable!()
        }
    };

    let mut out = String::new();

    project.proofsteps(&mut out).unwrap();
    out
}

#[wasm_bindgen]
pub fn prove(zipfile: &[u8]) {
    let ui = sspverif::ui::webui::WebBaseUI::new();
    let zipfile = Cursor::new(zipfile);
    let files = sspverif::project::Files::load_zip(zipfile).unwrap();
    let project = match sspverif::project::Project::load(&files) {
        Ok(project) => project,
        Err(e) => {
            error_1(&format!("{}", e).into());
            unreachable!()
        }
    };
    project
        .prove(ui, ProverBackend::Cvc5, false, 1, &None, None, &None)
        .unwrap();
}

#[wasm_bindgen]
pub fn helloworld() -> String {
    "Hello World".to_string()
}

#[wasm_bindgen]
pub fn test(module: &CVC) -> String {
    let solver = Solver::new(module);

    solver.add_smt("(declare-const a Int)");
    solver.add_smt("(declare-const b Int)");
    solver.add_smt("(declare-const c Int)");
    solver.add_smt("(declare-const d Int)");
    solver.add_smt("(assert (< a b c d))");
    solver.add_smt("(assert (= a (* 5 d)))");
    solver.add_smt("(assert (= b (* 3 c)))");
    solver.check_sat();
    solver.get_model()
}
