use js_sys::Object;
use sspverif::ui::{
    LatexUI, ProofstepUI, ProveLemmaUI, ProveOracleUI, ProveProofstepUI, ProveTheoremUI, ProveUI,
    UI,
};
use uuid::Uuid;
use wasm_bindgen::prelude::wasm_bindgen;
use web_sys::js_sys;

#[wasm_bindgen]
extern "C" {
    fn postMessage(msg: js_sys::Object);
}

#[derive(Clone)]
pub struct WebUI {
    uuid: Uuid,
}

impl WebUI {
    pub fn new(name: &str) -> Self {
        Self::new_named("UI", None, Some(name))
    }

    pub fn new_named(sort: &str, parent: Option<&Uuid>, extra: Option<&str>) -> Self {
        let resp = js_sys::Map::new();
        let uuid = Uuid::new_v4();
        let uuid_str: String = uuid.into();

        resp.set(&"func".into(), &"domino-ui".into());
        resp.set(&"new_uuid".into(), &uuid_str.into());
        resp.set(&"method".into(), &"new".into());
        resp.set(&"sort".into(), &sort.into());

        if let Some(parent_uuid) = parent {
            let parent_uuid: String = (*parent_uuid).into();
            resp.set(&"uuid".into(), &parent_uuid.into());
        }
        if let Some(extra) = extra {
            resp.set(&"extra".into(), &extra.into());
        }

        postMessage(Object::from_entries(&resp).unwrap());
        WebUI { uuid }
    }
}

impl UI for WebUI {
    fn println(&self, line: &str) -> std::io::Result<()> {
        let resp = js_sys::Map::new();
        let uuid: String = self.uuid.into();
        resp.set(&"func".into(), &"domino-ui".into());
        resp.set(&"uuid".into(), &uuid.into());
        resp.set(&"method".into(), &"println".into());
        resp.set(&"line".into(), &line.into());

        postMessage(Object::from_entries(&resp).unwrap());
        Ok(())
    }

    fn prove_ui(&self) -> impl ProveUI {
        WebUI::new_named("ProveUI", Some(&self.uuid), None)
    }
    fn latex_ui(&self) -> impl LatexUI {
        WebUI::new_named("LatexUI", Some(&self.uuid), None)
    }
    fn proofstep_ui(&self) -> impl ProofstepUI {
        WebUI::new_named("ProofstepUI", Some(&self.uuid), None)
    }
}

impl ProveUI for WebUI {
    fn println(&self, line: &str) -> std::io::Result<()> {
        let resp = js_sys::Map::new();
        let uuid: String = self.uuid.into();
        resp.set(&"func".into(), &"domino-ui".into());
        resp.set(&"uuid".into(), &uuid.into());
        resp.set(&"method".into(), &"println".into());
        resp.set(&"line".into(), &line.into());

        postMessage(Object::from_entries(&resp).unwrap());
        Ok(())
    }

    fn start(&self) {
        let resp = js_sys::Map::new();
        let uuid: String = self.uuid.into();
        resp.set(&"func".into(), &"domino-ui".into());
        resp.set(&"uuid".into(), &uuid.into());
        resp.set(&"method".into(), &"start".into());

        postMessage(Object::from_entries(&resp).unwrap());
    }

    fn finish(&self) {
        let resp = js_sys::Map::new();
        let uuid: String = self.uuid.into();
        resp.set(&"func".into(), &"domino-ui".into());
        resp.set(&"uuid".into(), &uuid.into());
        resp.set(&"method".into(), &"finish".into());

        postMessage(Object::from_entries(&resp).unwrap());
    }

    fn start_theorem(&self, theorem_name: &str) -> impl ProveTheoremUI {
        WebUI::new_named("ProveTheoremUI", Some(&self.uuid), Some(theorem_name))
    }
}

impl ProveTheoremUI for WebUI {
    fn println(&self, line: &str) -> std::io::Result<()> {
        let resp = js_sys::Map::new();
        let uuid: String = self.uuid.into();
        resp.set(&"func".into(), &"domino-ui".into());
        resp.set(&"uuid".into(), &uuid.into());
        resp.set(&"method".into(), &"println".into());
        resp.set(&"line".into(), &line.into());

        postMessage(Object::from_entries(&resp).unwrap());
        Ok(())
    }

    fn start(&mut self) {
        let resp = js_sys::Map::new();
        let uuid: String = self.uuid.into();
        resp.set(&"func".into(), &"domino-ui".into());
        resp.set(&"uuid".into(), &uuid.into());
        resp.set(&"method".into(), &"start".into());

        postMessage(Object::from_entries(&resp).unwrap());
    }

    fn finish(&self) {
        let resp = js_sys::Map::new();
        let uuid: String = self.uuid.into();
        resp.set(&"func".into(), &"domino-ui".into());
        resp.set(&"uuid".into(), &uuid.into());
        resp.set(&"method".into(), &"finish".into());

        postMessage(Object::from_entries(&resp).unwrap());
    }

    fn start_proofstep(&self, proofstep_name: String) -> impl ProveProofstepUI {
        WebUI::new_named("ProveProofstepUI", Some(&self.uuid), Some(&proofstep_name))
    }
}

impl ProveProofstepUI for WebUI {
    fn println(&self, line: &str) -> std::io::Result<()> {
        let resp = js_sys::Map::new();
        let uuid: String = self.uuid.into();
        resp.set(&"func".into(), &"domino-ui".into());
        resp.set(&"uuid".into(), &uuid.into());
        resp.set(&"method".into(), &"println".into());
        resp.set(&"line".into(), &line.into());

        postMessage(Object::from_entries(&resp).unwrap());
        Ok(())
    }

    fn start(&mut self) {
        let resp = js_sys::Map::new();
        let uuid: String = self.uuid.into();
        resp.set(&"func".into(), &"domino-ui".into());
        resp.set(&"uuid".into(), &uuid.into());
        resp.set(&"method".into(), &"start".into());

        postMessage(Object::from_entries(&resp).unwrap());
    }

    fn finish(&self) {
        let resp = js_sys::Map::new();
        let uuid: String = self.uuid.into();
        resp.set(&"func".into(), &"domino-ui".into());
        resp.set(&"uuid".into(), &uuid.into());
        resp.set(&"method".into(), &"finish".into());

        postMessage(Object::from_entries(&resp).unwrap());
    }

    fn is_reduction(&self) {}

    fn start_oracle(&self, oracle_name: String) -> impl ProveOracleUI {
        WebUI::new_named("ProveOracleUI", Some(&self.uuid), Some(&oracle_name))
    }
}

impl ProveOracleUI for WebUI {
    fn println(&self, line: &str) -> std::io::Result<()> {
        let resp = js_sys::Map::new();
        let uuid: String = self.uuid.into();
        resp.set(&"func".into(), &"domino-ui".into());
        resp.set(&"uuid".into(), &uuid.into());
        resp.set(&"method".into(), &"println".into());
        resp.set(&"line".into(), &line.into());

        postMessage(Object::from_entries(&resp).unwrap());
        Ok(())
    }

    fn start(&mut self) {
        let resp = js_sys::Map::new();
        let uuid: String = self.uuid.into();
        resp.set(&"func".into(), &"domino-ui".into());
        resp.set(&"uuid".into(), &uuid.into());
        resp.set(&"method".into(), &"start".into());

        postMessage(Object::from_entries(&resp).unwrap());
    }

    fn finish(&self) {
        let resp = js_sys::Map::new();
        let uuid: String = self.uuid.into();
        resp.set(&"func".into(), &"domino-ui".into());
        resp.set(&"uuid".into(), &uuid.into());
        resp.set(&"method".into(), &"finish".into());

        postMessage(Object::from_entries(&resp).unwrap());
    }

    fn start_lemma(&self, lemma_name: &str) -> impl ProveLemmaUI {
        WebUI::new_named("ProveLemmaUI", Some(&self.uuid), Some(lemma_name))
    }
}

impl ProveLemmaUI for WebUI {
    fn println(&self, line: &str) -> std::io::Result<()> {
        let resp = js_sys::Map::new();
        let uuid: String = self.uuid.into();
        resp.set(&"func".into(), &"domino-ui".into());
        resp.set(&"uuid".into(), &uuid.into());
        resp.set(&"method".into(), &"println".into());
        resp.set(&"line".into(), &line.into());

        postMessage(Object::from_entries(&resp).unwrap());
        Ok(())
    }

    fn start(&mut self) {
        let resp = js_sys::Map::new();
        let uuid: String = self.uuid.into();
        resp.set(&"func".into(), &"domino-ui".into());
        resp.set(&"uuid".into(), &uuid.into());
        resp.set(&"method".into(), &"start".into());

        postMessage(Object::from_entries(&resp).unwrap());
    }

    fn finish(&self) {
        let resp = js_sys::Map::new();
        let uuid: String = self.uuid.into();
        resp.set(&"func".into(), &"domino-ui".into());
        resp.set(&"uuid".into(), &uuid.into());
        resp.set(&"method".into(), &"finish".into());

        postMessage(Object::from_entries(&resp).unwrap());
    }
}

impl ProofstepUI for WebUI {
    fn println(&self, line: &str) -> std::io::Result<()> {
        let resp = js_sys::Map::new();
        let uuid: String = self.uuid.into();
        resp.set(&"func".into(), &"domino-ui".into());
        resp.set(&"uuid".into(), &uuid.into());
        resp.set(&"method".into(), &"proofstep".into());
        resp.set(&"line".into(), &format!("{line}\n").into());

        postMessage(Object::from_entries(&resp).unwrap());
        Ok(())
    }
}

impl LatexUI for WebUI {
    fn game_iterator<Item>(
        &self,
        iter: impl ExactSizeIterator<Item = Item>,
        _caption: String,
    ) -> impl Iterator<Item = Item> {
        iter
    }
}
