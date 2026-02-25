use js_sys::{Map, Object};
use web_sys::js_sys;

use std::io::Cursor;
use wasm_bindgen::prelude::wasm_bindgen;
use wasm_bindgen::{JsError, JsValue};

use uuid::Uuid;

use sspverif::{project::Project, ui::UI, writers::html::graph::composition_graph};
use web_sys::console::{error_1, log_1};
type Result<T> = std::result::Result<T, JsError>;

use smtsolver::WebSmtSolverBackend;

mod smtsolver;
mod ui;
mod util;

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
pub fn get_package(zipfiles: &ZipFilesWrapper, name: &str) -> Result<Option<String>> {
    let ZipFilesWrapper { files } = zipfiles;
    Ok(files.package(name).cloned())
}
#[wasm_bindgen]
pub fn list_games(zipfiles: &ZipFilesWrapper) -> Result<Vec<String>> {
    let ZipFilesWrapper { files } = zipfiles;
    Ok(files.games().cloned().collect())
}
#[wasm_bindgen]
pub fn get_game(zipfiles: &ZipFilesWrapper, name: &str) -> Result<Option<String>> {
    let ZipFilesWrapper { files } = zipfiles;
    Ok(files.game(name).cloned())
}
#[wasm_bindgen]
pub fn list_theorems(zipfiles: &ZipFilesWrapper) -> Result<Vec<String>> {
    let ZipFilesWrapper { files } = zipfiles;
    Ok(files.theorems().cloned().collect())
}
#[wasm_bindgen]
pub fn get_theorem(zipfiles: &ZipFilesWrapper, name: &str) -> Result<Option<String>> {
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
pub fn projectdetails(zipfiles: &ZipFilesWrapper) -> Result<Object> {
    let ZipFilesWrapper { files } = zipfiles;
    let project = sspverif::project::ZipProject::load(&files)?;

    let gamegraphs = util::to_js_map(project.games().filter_map(|gamename| {
        composition_graph(&WebSmtSolverBackend, project.get_game(gamename).unwrap())
            .map(|graph| (gamename.as_str(), graph.into_string()))
    }));

    let theorems = util::to_js_map(project.theorems().map(|theoremname| {
        let theorem = project.get_theorem(theoremname).unwrap();
        let proofs = util::to_js_map(theorem.proofs.iter().map(|proof| {
            (
                proof.name.as_str(),
                proof
                    .instances()
                    .map(|inst| inst.game_name().into())
                    .collect::<Vec<JsValue>>(),
            )
        }));
        (theoremname.as_str(), proofs)
    }));

    let resp = js_sys::Map::new();
    resp.set(&"gamegraphs".into(), &gamegraphs.into());
    resp.set(&"theorems".into(), &theorems.into());
    Ok(resp.into())
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
