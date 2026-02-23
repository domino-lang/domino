use super::{Result, SmtParser};

use crate::writers::smt::exprs::SmtExpr;

use itertools::Itertools;

#[derive(Debug)]
pub struct ExtractedFunction {
    pub smtfunname: String,
    pub smttype: String,
    pub smtargs: Vec<(String, String)>,
}

impl std::fmt::Display for ExtractedFunction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let ExtractedFunction {
            smtfunname,
            smttype,
            smtargs,
        } = self;
        write!(
            f,
            "(define-fun {smtfunname} ({}) {smttype} ...)",
            smtargs
                .iter()
                .map(|(name, ty)| format!("({name} {ty})"))
                .join(" ")
        )
    }
}

struct FunctionExtractor {
    functions: Vec<ExtractedFunction>,
}

impl FunctionExtractor {
    fn new() -> Self {
        Self {
            functions: Vec::new(),
        }
    }
}

impl SmtParser<Option<SmtExpr>> for FunctionExtractor {
    fn handle_atom(&mut self, content: &str) -> Result<Option<SmtExpr>> {
        Ok(Some(SmtExpr::Atom(content.to_string())))
    }

    fn handle_list(&mut self, content: Vec<Option<SmtExpr>>) -> Result<Option<SmtExpr>> {
        Ok(Some(SmtExpr::List(content.into_iter().flatten().collect())))
    }

    fn handle_sexp(&mut self, mut _parsed: Option<SmtExpr>) -> Result<()> {
        Ok(())
    }

    fn handle_definefun(
        &mut self,
        smtfunname: &str,
        args: Vec<Option<SmtExpr>>,
        smttype: &str,
        _body: Option<SmtExpr>,
    ) -> Result<Option<SmtExpr>> {
        let smtargs = args
            .into_iter()
            .filter_map(|expr| {
                if let Some(SmtExpr::List(ref l)) = expr {
                    if l.len() == 2 {
                        if let [SmtExpr::Atom(argname), SmtExpr::Atom(typename)] = &l[..] {
                            return Some((argname.clone(), typename.clone()));
                        }
                    }
                }
                log::warn!("Could not properly parse argument of definefun: {expr:?}!");
                None
            })
            .collect();

        self.functions.push(ExtractedFunction {
            smtfunname: smtfunname.to_string(),
            smtargs,
            smttype: smttype.to_string(),
        });
        Ok(None)
    }
}

pub fn extract(content: &str) -> Vec<ExtractedFunction> {
    let mut extractor = FunctionExtractor::new();
    if extractor.parse_sexps(content).is_err() {
        Vec::new()
    } else {
        extractor.functions
    }
}
