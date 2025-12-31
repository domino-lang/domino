use std::io::Cursor;
use wasm_bindgen::prelude::wasm_bindgen;

#[wasm_bindgen]
extern "C" {
    #[wasm_bindgen(js_namespace = console)]
    fn log(s: &str);
}

#[wasm_bindgen]
pub fn proofsteps(zipfile: &[u8]) -> String {
    let zipfile = Cursor::new(zipfile);
    let files = sspverif::project::Files::load_zip(zipfile).unwrap();
    let project = match sspverif::project::Project::load(&files) {
        Ok(project) => project,
        Err(e) => {
            log(&format!("{}", e));
            unreachable!()
        }
    };

    let mut out = String::new();

    project.proofsteps(&mut out).unwrap();
    out
}

#[wasm_bindgen]
pub fn helloworld() -> String {
    "Hello World".to_string()
}
