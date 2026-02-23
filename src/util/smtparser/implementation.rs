use crate::debug_assert_matches;
pub use pest::error::Error;
use pest::iterators::Pair;
use pest::Parser;
extern crate pest;

#[derive(Parser)]
#[grammar = "util/smtparser/smt.pest"]
struct PestSmtParser;

pub(crate) trait SmtParser<T, E = Error<Rule>>
where
    E: std::convert::From<Error<Rule>>,
{
    fn handle_sexp(&mut self, parsed: T) -> Result<(), E>;

    fn handle_atom(&mut self, content: &str) -> Result<T, E>;

    fn handle_list(&mut self, content: Vec<T>) -> Result<T, E>;

    fn handle_integer(&mut self, content: &str) -> Result<T, E> {
        self.handle_atom(content)
    }

    fn handle_boolean(&mut self, content: &str) -> Result<T, E> {
        self.handle_atom(content)
    }

    fn handle_string(&mut self, content: &str) -> Result<T, E> {
        self.handle_atom(&format!("\"{content}\""))
    }

    fn handle_define_state_relation(
        &mut self,
        funname: &str,
        args: Vec<T>,
        body: T,
    ) -> Result<T, E> {
        let funname = self.handle_atom(funname)?;
        let args = self.handle_list(args)?;
        let defun = self.handle_atom("define-state-relation")?;

        self.handle_list(vec![defun, funname, args, body])
    }

    fn handle_define_lemma(&mut self, funname: &str, args: Vec<T>, body: T) -> Result<T, E> {
        let funname = self.handle_atom(funname)?;
        let args = self.handle_list(args)?;
        let defun = self.handle_atom("define-lemma")?;

        self.handle_list(vec![defun, funname, args, body])
    }

    fn handle_definefun(&mut self, funname: &str, args: Vec<T>, ty: &str, body: T) -> Result<T, E> {
        let funname = self.handle_atom(funname)?;
        let args = self.handle_list(args)?;
        let ty = self.handle_atom(ty)?;
        let defun = self.handle_atom("define-fun")?;

        self.handle_list(vec![defun, funname, args, ty, body])
    }

    fn handle_sampleid(
        &mut self,
        pkgname: &str,
        oraclename: &str,
        samplename: &str,
    ) -> Result<T, E> {
        let pkgname = self.handle_string(pkgname)?;
        let oraclename = self.handle_string(oraclename)?;
        let samplename = self.handle_string(samplename)?;
        let sampleid = self.handle_atom("sample-id")?;

        let list = vec![sampleid, pkgname, oraclename, samplename];
        self.handle_list(list)
    }

    fn parse_sexp(&mut self, from: &str) -> Result<usize, E> {
        let parse_result = PestSmtParser::parse(Rule::sexp, from)?.next().unwrap();
        let parsed = self.rule_sexp(&parse_result)?;

        self.handle_sexp(parsed)?;

        Ok(parse_result.as_span().end())
    }

    fn parse_sexps(&mut self, from: &str) -> Result<(), E> {
        let sexps = PestSmtParser::parse(Rule::sexps, from)?.next().unwrap();
        for sexp in sexps.into_inner() {
            if !matches!(sexp.as_rule(), Rule::sexp) {
                continue;
            };

            let parsed = self.rule_sexp(&sexp)?;

            self.handle_sexp(parsed)?;
        }

        Ok(())
    }

    fn rule_sexp(&mut self, p: &Pair<Rule>) -> Result<T, E> {
        debug_assert_matches!(p.as_rule(), Rule::sexp);
        let inner = p.clone().into_inner().next().unwrap();
        match inner.as_rule() {
            Rule::atom => self.handle_atom(inner.as_str()),
            Rule::integer => self.handle_integer(inner.as_str()),
            Rule::boolean => self.handle_boolean(inner.as_str()),
            Rule::string => self.handle_string(inner.as_str()),
            Rule::list => {
                let list = inner
                    .into_inner()
                    .map(|x| self.rule_sexp(&x))
                    .collect::<Result<Vec<_>, _>>()?;
                self.handle_list(list)
            }
            Rule::sampleid => {
                let mut inner = inner.into_inner();
                let pkgname = inner.next().unwrap().as_str();
                let oraclename = inner.next().unwrap().as_str();
                let samplename = inner.next().unwrap().as_str();
                self.handle_sampleid(pkgname, oraclename, samplename)
            }
            Rule::defun => {
                let mut inner = inner.into_inner();
                let funname = inner.next().unwrap().as_str();
                let args = inner.next().unwrap();
                debug_assert_matches!(args.as_rule(), Rule::list);
                let args = args
                    .into_inner()
                    .map(|sexp| self.rule_sexp(&sexp))
                    .collect::<Result<Vec<_>, _>>()?;
                let ty = inner.next().unwrap().as_str();
                let body = self.rule_sexp(&inner.next().unwrap())?;

                self.handle_definefun(funname, args, ty, body)
            }
            Rule::define_state_relation => {
                let mut inner = inner.into_inner();
                let funname = inner.next().unwrap().as_str();
                let args = inner.next().unwrap();
                debug_assert_matches!(args.as_rule(), Rule::list);
                let args = args
                    .into_inner()
                    .map(|sexp| self.rule_sexp(&sexp))
                    .collect::<Result<Vec<_>, _>>()?;
                let body = self.rule_sexp(&inner.next().unwrap())?;

                self.handle_define_state_relation(funname, args, body)
            }
            Rule::define_lemma => {
                let mut inner = inner.into_inner();
                let funname = inner.next().unwrap().as_str();
                let args = inner.next().unwrap();
                debug_assert_matches!(args.as_rule(), Rule::list);
                let args = args
                    .into_inner()
                    .map(|sexp| self.rule_sexp(&sexp))
                    .collect::<Result<Vec<_>, _>>()?;
                let body = self.rule_sexp(&inner.next().unwrap())?;

                self.handle_define_lemma(funname, args, body)
            }
            _ => {
                todo!("{inner}")
            }
        }
    }
}
