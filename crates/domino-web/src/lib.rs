use std::io::Cursor;
use wasm_bindgen::prelude::wasm_bindgen;

use sspverif::project::Project;
use sspverif::util::prover::ProverBackend;
use web_sys::console::{error_1, log_1};

use sspverif::project::error::Result;

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

#[wasm_bindgen(start)]
pub fn start() {
    wasm_logger::init(wasm_logger::Config::default());
}

#[wasm_bindgen]
pub fn proofsteps(zipfile: &[u8]) -> Result<String> {
    let zipfile = Cursor::new(zipfile);

    let files = sspverif::project::ZipProject::load(zipfile.clone())?;
    let project = sspverif::project::ZipProject::new(&files)?;
    log::warn!("{:?}", project);
    log::warn!("{:?}", files);

    let mut out = "test".to_string();
    project.proofsteps(&mut out)?;

    Ok(out)
}

#[wasm_bindgen]
pub fn prove(zipfile: &[u8]) -> Result<()> {
    let ui = sspverif::ui::webui::WebBaseUI::new();
    let zipfile = Cursor::new(zipfile);

    let files = sspverif::project::ZipProject::load(zipfile.clone())?;
    let project = sspverif::project::ZipProject::new(&files)?;

    project.prove(ui, ProverBackend::Cvc5, false, 1, &None, None, &None)
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
