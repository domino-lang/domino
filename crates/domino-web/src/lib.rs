use std::io::Cursor;
use wasm_bindgen::prelude::wasm_bindgen;
use wasm_bindgen::JsError;

use uuid::Uuid;

use sspverif::{project::Project, ui::UI};
use web_sys::console::{error_1, log_1};
type Result<T> = std::result::Result<T, JsError>;

use smtsolver::WebSmtSolverBackend;

mod smtsolver;
mod ui;

#[wasm_bindgen]
pub struct ZipFilesWrapper {
    files: sspverif::project::ZipFiles,
}

#[wasm_bindgen(start)]
pub fn start() {
    wasm_logger::init(wasm_logger::Config::default());
}

#[wasm_bindgen]
pub fn load(zipfile: &[u8]) -> Result<ZipFilesWrapper> {
    let zipfile = Cursor::new(zipfile);
    let files = sspverif::project::ZipFiles::load(zipfile.clone())?;

    Ok(ZipFilesWrapper { files })
}

#[wasm_bindgen]
pub fn list_packages(zipfiles: &ZipFilesWrapper) -> Result<Vec<String>> {
    let ZipFilesWrapper { files } = zipfiles;
    Ok(files.packages().cloned().collect())
}
#[wasm_bindgen]
pub fn package(zipfiles: &ZipFilesWrapper, name: &str) -> Result<Option<String>> {
    let ZipFilesWrapper { files } = zipfiles;
    Ok(files.package(name).cloned())
}
#[wasm_bindgen]
pub fn list_games(zipfiles: &ZipFilesWrapper) -> Result<Vec<String>> {
    let ZipFilesWrapper { files } = zipfiles;
    Ok(files.games().cloned().collect())
}
#[wasm_bindgen]
pub fn game(zipfiles: &ZipFilesWrapper, name: &str) -> Result<Option<String>> {
    let ZipFilesWrapper { files } = zipfiles;
    Ok(files.game(name).cloned())
}
#[wasm_bindgen]
pub fn list_theorems(zipfiles: &ZipFilesWrapper) -> Result<Vec<String>> {
    let ZipFilesWrapper { files } = zipfiles;
    Ok(files.theorems().cloned().collect())
}
#[wasm_bindgen]
pub fn theorem(zipfiles: &ZipFilesWrapper, name: &str) -> Result<Option<String>> {
    let ZipFilesWrapper { files } = zipfiles;
    Ok(files.theorem(name).cloned())
}

#[wasm_bindgen]
pub fn proofsteps(uuid: &str, zipfiles: &ZipFilesWrapper) -> Result<()> {
    let ZipFilesWrapper { files } = zipfiles;

    let uuid = Uuid::parse_str(uuid).unwrap();
    let project = sspverif::project::ZipProject::load(&files)?;

    project.proofsteps(ui::WebUI::new_named("ProofstepUI", Some(&uuid), None))?;

    Ok(())
}

#[wasm_bindgen]
pub fn prove(uuid: &str, zipfiles: &ZipFilesWrapper, proof_name: String) -> Result<()> {
    let ZipFilesWrapper { files } = zipfiles;

    let uuid = Uuid::parse_str(uuid).unwrap();
    let project = sspverif::project::ZipProject::load(&files)?;

    project.prove(
        ui::WebUI::new_named("ProveUI", Some(&uuid), None),
        &WebSmtSolverBackend,
        false,
        1,
        &Some(proof_name),
        None,
        &None,
    )?;
    Ok(())
}
