use crate::gamehops::reduction::Reduction;
use crate::parser::ast::Identifier;

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
