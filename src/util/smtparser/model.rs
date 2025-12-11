use super::SmtParser;
use crate::util::smtmodel::{SmtModel, SmtModelEntry};
use crate::writers::smt::exprs::SmtExpr;

enum ModelExtractorState {
    SmtExpr(SmtExpr),
    Integer(i32),
    Boolean(bool),
    // SmtModelEntry(SmtModelEntry),
    Empty,
}

impl SmtParser<ModelExtractorState> for SmtModel {
    fn handle_sexp(&mut self, _parsed: ModelExtractorState) {}

    fn handle_atom(&mut self, content: &str) -> ModelExtractorState {
        ModelExtractorState::SmtExpr(SmtExpr::Atom(content.to_string()))
    }

    fn handle_list(&mut self, content: Vec<ModelExtractorState>) -> ModelExtractorState {
        ModelExtractorState::SmtExpr(SmtExpr::List(
            content
                .into_iter()
                .filter_map(|entry| match entry {
                    ModelExtractorState::SmtExpr(expr) => Some(expr),
                    ModelExtractorState::Integer(int) => Some(SmtExpr::Atom(int.to_string())),
                    ModelExtractorState::Boolean(bo) => Some(SmtExpr::Atom(bo.to_string())),
                    _ => None,
                })
                .collect(),
        ))
    }

    fn handle_integer(&mut self, content: &str) -> ModelExtractorState {
        ModelExtractorState::Integer(content.parse().unwrap())
    }

    fn handle_boolean(&mut self, content: &str) -> ModelExtractorState {
        ModelExtractorState::Boolean(content == "true")
    }

    fn handle_definefun(
        &mut self,
        funname: &str,
        _args: Vec<ModelExtractorState>,
        ty: &str,
        body: ModelExtractorState,
    ) -> ModelExtractorState {
        match body {
            ModelExtractorState::Integer(int) => {
                debug_assert_eq!(ty, "Int");
                self.values.push(SmtModelEntry::IntEntry {
                    name: funname.to_string(),
                    value: int,
                });
            }
            ModelExtractorState::Boolean(bo) => {
                debug_assert_eq!(ty, "Bool");
                self.values.push(SmtModelEntry::BoolEntry {
                    name: funname.to_string(),
                    value: bo,
                });
            }
            ModelExtractorState::SmtExpr(expr) => {
                self.values.push(SmtModelEntry::UnknownEntry {
                    name: funname.to_string(),
                    ty: ty.to_string(),
                    value: expr,
                });
            }
            ModelExtractorState::Empty => {
                todo!()
            }
        }

        ModelExtractorState::Empty
    }
}

pub fn parse(content: &str) -> (SmtModel, usize) {
    let mut model = SmtModel { values: Vec::new() };
    let length = model.parse_sexp(content);

    (model, length)
}
