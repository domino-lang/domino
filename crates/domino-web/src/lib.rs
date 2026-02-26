use std::io::Cursor;
use wasm_bindgen::prelude::wasm_bindgen;
use wasm_bindgen::JsError;

use sspverif::project::Project;
use web_sys::console::{error_1, log_1};
type Result<T> = std::result::Result<T, JsError>;

use prover::WebProverFactory;

mod prover;

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

    let files = sspverif::project::ZipFiles::load(zipfile.clone())?;
    let project = sspverif::project::ZipProject::load(&files)?;
    log::warn!("{:?}", project);
    log::warn!("{:?}", files);

    let mut out = "test".to_string();
    project.proofsteps()?;

    Ok(out)
}

#[wasm_bindgen]
pub fn prove(zipfile: &[u8]) -> Result<()> {
    let zipfile = Cursor::new(zipfile);

    let files = sspverif::project::ZipFiles::load(zipfile.clone())?;
    let project = sspverif::project::ZipProject::load(&files)?;

    project.prove(&WebProverFactory, false, 1, &None, None, &None)?;
    Ok(())
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
