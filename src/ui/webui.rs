use super::{BaseUI, TheoremUI};

use js_sys::Object;
use wasm_bindgen::prelude::wasm_bindgen;
use web_sys::console::{log, log_1};

#[wasm_bindgen]
extern "C" {
    fn postMessage(msg: js_sys::Object);
}

pub struct WebTheoremUI {}

impl TheoremUI for WebTheoremUI {
    fn println(&self, line: &str) -> std::io::Result<()> {
        //let line: JsValue = line.into()
        log_1(&line.into());
        Ok(())
    }

    fn start_theorem(&mut self, theorem_name: &str, num_proofsteps: u64) {
        let resp = js_sys::Map::new();
        resp.set(&"func".into(), &"domino-ui".into());
        resp.set(&"stage".into(), &"start-theorem".into());
        resp.set(&"theorem-name".into(), &theorem_name.into());
        resp.set(&"proofsteps".into(), &num_proofsteps.into());

        postMessage(Object::from_entries(&resp).unwrap());
    }

    fn finish_theorem(&mut self, theorem_name: &str) {
        let resp = js_sys::Map::new();
        resp.set(&"func".into(), &"domino-ui".into());
        resp.set(&"stage".into(), &"finish-theorem".into());
        resp.set(&"theorem-name".into(), &theorem_name.into());

        postMessage(Object::from_entries(&resp).unwrap());
    }

    fn start_proofstep(&mut self, theorem_name: &str, proofstep_name: &str) {
        let resp = js_sys::Map::new();
        resp.set(&"func".into(), &"domino-ui".into());
        resp.set(&"stage".into(), &"start-proofstep".into());
        resp.set(&"theorem-name".into(), &theorem_name.into());
        resp.set(&"proofstep-name".into(), &proofstep_name.into());

        postMessage(Object::from_entries(&resp).unwrap());
    }

    fn proofstep_is_reduction(&mut self, theorem_name: &str, proofstep_name: &str) {
        let resp = js_sys::Map::new();
        resp.set(&"func".into(), &"domino-ui".into());
        resp.set(&"stage".into(), &"proofstep-is-reduction".into());
        resp.set(&"theorem-name".into(), &theorem_name.into());
        resp.set(&"proofstep-name".into(), &proofstep_name.into());

        postMessage(Object::from_entries(&resp).unwrap());
    }

    fn proofstep_set_oracles(
        &mut self,
        theorem_name: &str,
        proofstep_name: &str,
        num_oracles: u64,
    ) {
        let resp = js_sys::Map::new();
        resp.set(&"func".into(), &"domino-ui".into());
        resp.set(&"stage".into(), &"set-oracles".into());
        resp.set(&"theorem-name".into(), &theorem_name.into());
        resp.set(&"proofstep-name".into(), &proofstep_name.into());
        resp.set(&"oracles".into(), &num_oracles.into());

        postMessage(Object::from_entries(&resp).unwrap());
    }

    fn finish_proofstep(&mut self, theorem_name: &str, proofstep_name: &str) {
        let resp = js_sys::Map::new();
        resp.set(&"func".into(), &"domino-ui".into());
        resp.set(&"stage".into(), &"finish-proofstep".into());
        resp.set(&"theorem-name".into(), &theorem_name.into());
        resp.set(&"proofstep-name".into(), &proofstep_name.into());

        postMessage(Object::from_entries(&resp).unwrap());
    }

    fn start_oracle(
        &mut self,
        theorem_name: &str,
        proofstep_name: &str,
        oracle_name: &str,
        num_lemmata: u64,
    ) {
        let resp = js_sys::Map::new();
        resp.set(&"func".into(), &"domino-ui".into());
        resp.set(&"stage".into(), &"start-oracle".into());
        resp.set(&"theorem-name".into(), &theorem_name.into());
        resp.set(&"proofstep-name".into(), &proofstep_name.into());
        resp.set(&"oracle".into(), &oracle_name.into());
        resp.set(&"lemmata".into(), &num_lemmata.into());

        postMessage(Object::from_entries(&resp).unwrap());
    }

    fn finish_oracle(&mut self, theorem_name: &str, proofstep_name: &str, oracle_name: &str) {
        let resp = js_sys::Map::new();
        resp.set(&"func".into(), &"domino-ui".into());
        resp.set(&"stage".into(), &"finish-oracle".into());
        resp.set(&"theorem-name".into(), &theorem_name.into());
        resp.set(&"proofstep-name".into(), &proofstep_name.into());
        resp.set(&"oracle".into(), &oracle_name.into());

        postMessage(Object::from_entries(&resp).unwrap());
    }

    fn start_lemma(
        &mut self,
        theorem_name: &str,
        proofstep_name: &str,
        oracle_name: &str,
        lemma_name: &str,
    ) {
        let resp = js_sys::Map::new();
        resp.set(&"func".into(), &"domino-ui".into());
        resp.set(&"stage".into(), &"start-lemma".into());
        resp.set(&"theorem-name".into(), &theorem_name.into());
        resp.set(&"proofstep-name".into(), &proofstep_name.into());
        resp.set(&"oracle".into(), &oracle_name.into());
        resp.set(&"lemma".into(), &lemma_name.into());

        postMessage(Object::from_entries(&resp).unwrap());
    }

    fn finish_lemma(
        &mut self,
        theorem_name: &str,
        proofstep_name: &str,
        oracle_name: &str,
        lemma_name: &str,
    ) {
        let resp = js_sys::Map::new();
        resp.set(&"func".into(), &"domino-ui".into());
        resp.set(&"stage".into(), &"finish-lemma".into());
        resp.set(&"theorem-name".into(), &theorem_name.into());
        resp.set(&"proofstep-name".into(), &proofstep_name.into());
        resp.set(&"oracle".into(), &oracle_name.into());
        resp.set(&"lemma".into(), &lemma_name.into());

        postMessage(Object::from_entries(&resp).unwrap());
    }
}

pub struct WebBaseUI {}

impl WebBaseUI {
    pub fn new() -> Self {
        WebBaseUI {}
    }
}

impl BaseUI for WebBaseUI {
    fn into_theorem_ui(self, num_theorems: u64) -> impl TheoremUI {
        WebTheoremUI {}
    }
}
