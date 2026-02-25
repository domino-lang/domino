use wasm_bindgen::{JsError, JsValue};
use web_sys::js_sys::{Map, Object};

pub(crate) fn to_js_map<'a>(from: impl Iterator<Item = (&'a str, impl Into<JsValue>)>) -> Map {
    let result = Map::new();
    for (name, value) in from {
        result.set(&name.into(), &value.into());
    }
    result
}
