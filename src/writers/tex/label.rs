use crate::{
    gamehops::reduction::{Assumption, Reduction},
    parser::ast::Identifier,
    proof::Proof,
};

pub(crate) trait LatexLabel {
    fn latex_label(&self, sort: &str) -> String;
}

impl LatexLabel for Reduction<'_> {
    fn latex_label(&self, sort: &str) -> String {
        let assumption = self.assumption_name();
        let left = self.left().construction_game_instance_name().as_str();
        let right = self.right().construction_game_instance_name().as_str();
        format!("{sort}:reduction:{assumption}:{left}:{right}")
    }
}

impl LatexLabel for Assumption {
    fn latex_label(&self, sort: &str) -> String {
        let name = &self.name;
        let left = &self.left_name;
        let right = &self.right_name;
        format!("{sort}:assumption:{name}:{left}:{right}")
    }
}

impl LatexLabel for Proof<'_> {
    fn latex_label(&self, sort: &str) -> String {
        let name = self.name();
        let left = self.left_name();
        let right = self.right_name();
        format!("{sort}:theorem:{name}:{left}:{right}")
    }
}
