use crate::debug_assert_matches;
use pest::error::Error;
use pest::iterators::Pair;
use pest::Parser;
extern crate pest;

#[derive(Parser)]
#[grammar = "util/smtparser/smt.pest"]
struct PestSmtParser;

pub(crate) trait SmtParser<T> {
    fn handle_sexp(&mut self, parsed: T);

    fn handle_atom(&mut self, content: &str) -> T;

    fn handle_list(&mut self, content: Vec<T>) -> T;

    fn handle_integer(&mut self, content: &str) -> T {
        self.handle_atom(content)
    }

    fn handle_boolean(&mut self, content: &str) -> T {
        self.handle_atom(content)
    }

    fn handle_string(&mut self, content: &str) -> T {
        self.handle_atom(&format!("\"{content}\""))
    }

    fn handle_definefun(&mut self, funname: &str, args: Vec<T>, ty: &str, body: T) -> T {
        let funname = self.handle_atom(funname);
        let args = self.handle_list(args);
        let ty = self.handle_atom(ty);
        let defun = self.handle_atom("define-fun");

        self.handle_list(vec![defun, funname, args, ty, body])
    }

    fn handle_sampleid(&mut self, pkgname: &str, oraclename: &str, samplename: &str) -> T {
        let pkgname = self.handle_string(pkgname);
        let oraclename = self.handle_string(oraclename);
        let samplename = self.handle_string(samplename);
        let sampleid = self.handle_atom("sample-id");

        let list = vec![sampleid, pkgname, oraclename, samplename];
        self.handle_list(list)
    }

    fn parse_sexp(&mut self, from: &str) -> Result<usize, Error<Rule>> {
        let parse_result = PestSmtParser::parse(Rule::sexp, from)?.next().unwrap();
        let parsed = self.rule_sexp(&parse_result);

        self.handle_sexp(parsed);

        Ok(parse_result.as_span().end())
    }

    fn parse_sexps(&mut self, from: &str) -> Result<(), Error<Rule>> {
        let sexps = PestSmtParser::parse(Rule::sexps, from)?.next().unwrap();
        for sexp in sexps.into_inner() {
            if !matches!(sexp.as_rule(), Rule::sexp) {
                continue;
            };

            let parsed = self.rule_sexp(&sexp);

            self.handle_sexp(parsed);
        }

        Ok(())
    }

    fn rule_sexp(&mut self, p: &Pair<Rule>) -> T {
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
                    .collect::<Vec<T>>();
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
                let args: Vec<_> = args
                    .into_inner()
                    .map(|sexp| self.rule_sexp(&sexp))
                    .collect();
                let ty = inner.next().unwrap().as_str();
                let body = self.rule_sexp(&inner.next().unwrap());

                self.handle_definefun(funname, args, ty, body)
            }
            _ => {
                todo!("{inner}")
            }
        }
    }
}
