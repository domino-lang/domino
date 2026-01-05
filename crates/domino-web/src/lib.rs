use std::io::Cursor;
use wasm_bindgen::prelude::wasm_bindgen;

use sspverif::util::prover::process::ProverBackend;
use web_sys::console::{error_1, log_1};

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
