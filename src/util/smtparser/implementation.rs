use crate::debug_assert_matches;
pub use pest::error::Error;
use pest::iterators::Pair;
use pest::Parser;
extern crate pest;

#[derive(Parser)]
#[grammar = "util/smtparser/smt.pest"]
struct PestSmtParser;

pub(crate) trait SmtParser<E = Error<Rule>>
where
    E: std::convert::From<Error<Rule>>,
{
    type Expr;
    type Stmt: From<Self::Expr>;

    fn handle_sexp(&mut self, parsed: Self::Stmt) -> Result<(), E>;

    fn handle_atom(&mut self, content: &str) -> Result<Self::Expr, E>;

    fn handle_list(&mut self, content: Vec<Self::Expr>) -> Result<Self::Expr, E>;

    fn handle_integer(&mut self, content: &str) -> Result<Self::Expr, E> {
        self.handle_atom(content)
    }

    fn handle_boolean(&mut self, content: &str) -> Result<Self::Expr, E> {
        self.handle_atom(content)
    }

    fn handle_string(&mut self, content: &str) -> Result<Self::Expr, E> {
        self.handle_atom(&format!("\"{content}\""))
    }

    fn handle_define_game_invariant(&mut self, body: Self::Expr) -> Result<Self::Stmt, E> {
        let defun = self.handle_atom("define-game-invariant")?;
        self.handle_list(vec![defun, body]).map(Into::into)
    }

    fn handle_define_package_invariant(&mut self, body: Self::Expr) -> Result<Self::Stmt, E> {
        let defun = self.handle_atom("define-package-invariant")?;
        self.handle_list(vec![defun, body]).map(Into::into)
    }

    fn handle_define_state_relation(
        &mut self,
        funname: &str,
        args: Vec<Self::Expr>,
        body: Self::Expr,
    ) -> Result<Self::Stmt, E> {
        let funname = self.handle_atom(funname)?;
        let args = self.handle_list(args)?;
        let defun = self.handle_atom("define-state-relation")?;

        self.handle_list(vec![defun, funname, args, body])
            .map(Into::into)
    }

    fn handle_define_lemma(
        &mut self,
        funname: &str,
        args: Vec<Self::Expr>,
        body: Self::Expr,
    ) -> Result<Self::Stmt, E> {
        let funname = self.handle_atom(funname)?;
        let args = self.handle_list(args)?;
        let defun = self.handle_atom("define-lemma")?;

        self.handle_list(vec![defun, funname, args, body])
            .map(Into::into)
    }

    fn handle_definefun(
        &mut self,
        funname: &str,
        args: Vec<Self::Expr>,
        ty: &str,
        body: Self::Expr,
    ) -> Result<Self::Stmt, E> {
        let funname = self.handle_atom(funname)?;
        let args = self.handle_list(args)?;
        let ty = self.handle_atom(ty)?;
        let defun = self.handle_atom("define-fun")?;

        self.handle_list(vec![defun, funname, args, ty, body])
            .map(Into::into)
    }

    fn handle_sampleid(
        &mut self,
        pkgname: &str,
        oraclename: &str,
        samplename: &str,
    ) -> Result<Self::Expr, E> {
        let pkgname = self.handle_string(pkgname)?;
        let oraclename = self.handle_string(oraclename)?;
        let samplename = self.handle_string(samplename)?;
        let sampleid = self.handle_atom("sample-id")?;

        let list = vec![sampleid, pkgname, oraclename, samplename];
        self.handle_list(list)
    }

    fn parse_stmt_list(&mut self, from: &str) -> Result<usize, E> {
        let parse_result = PestSmtParser::parse(Rule::stmtlist, from)?.next().unwrap();
        let end = parse_result.as_span().end();

        for stmt in parse_result.into_inner() {
            let stmt = self.rule_stmt(stmt)?;
            self.handle_sexp(stmt)?;
        }

        Ok(end)
    }

    fn parse_stmts(&mut self, from: &str) -> Result<(), E> {
        let sexps = PestSmtParser::parse(Rule::stmts, from)?.next().unwrap();
        for sexp in sexps.into_inner() {
            if !matches!(sexp.as_rule(), Rule::stmt) {
                continue;
            };

            let parsed = self.rule_stmt(sexp.into_inner().next().unwrap())?;

            self.handle_sexp(parsed)?;
        }

        Ok(())
    }

    fn rule_stmt(&mut self, p: Pair<Rule>) -> Result<Self::Stmt, E> {
        match p.as_rule() {
            Rule::defun => {
                let mut p = p.into_inner();
                let funname = p.next().unwrap().as_str();
                let args = p.next().unwrap();
                debug_assert_matches!(args.as_rule(), Rule::list);
                let args = args
                    .into_inner()
                    .map(|sexp| self.rule_expr(sexp))
                    .collect::<Result<Vec<_>, _>>()?;
                let ty = p.next().unwrap().as_str();
                let body = self.rule_expr(p.next().unwrap())?;

                self.handle_definefun(funname, args, ty, body)
            }
            Rule::define_package_invariant => {
                let mut p = p.into_inner();
                let body = self.rule_expr(p.next().unwrap())?;

                self.handle_define_package_invariant(body)
            }
            Rule::define_game_invariant => {
                let mut p = p.into_inner();
                let body = self.rule_expr(p.next().unwrap())?;

                self.handle_define_game_invariant(body)
            }
            Rule::define_state_relation => {
                let mut p = p.into_inner();
                let funname = p.next().unwrap().as_str();
                let args = p.next().unwrap();
                debug_assert_matches!(args.as_rule(), Rule::list);
                let args = args
                    .into_inner()
                    .map(|sexp| self.rule_expr(sexp))
                    .collect::<Result<Vec<_>, _>>()?;
                let body = self.rule_expr(p.next().unwrap())?;

                self.handle_define_state_relation(funname, args, body)
            }
            Rule::define_lemma => {
                let mut p = p.into_inner();
                let funname = p.next().unwrap().as_str();
                let args = p.next().unwrap();
                debug_assert_matches!(args.as_rule(), Rule::list);
                let args = args
                    .into_inner()
                    .map(|sexp| self.rule_expr(sexp))
                    .collect::<Result<Vec<_>, _>>()?;
                let body = self.rule_expr(p.next().unwrap())?;

                self.handle_define_lemma(funname, args, body)
            }
            Rule::stmt => self.rule_stmt(p.into_inner().next().unwrap()),
            _ => self.rule_expr(p).map(Into::into),
        }
    }

    fn rule_expr(&mut self, p: Pair<Rule>) -> Result<Self::Expr, E> {
        match p.as_rule() {
            Rule::atom => self.handle_atom(p.as_str()),
            Rule::integer => self.handle_integer(p.as_str()),
            Rule::boolean => self.handle_boolean(p.as_str()),
            Rule::string => self.handle_string(p.as_str()),
            Rule::list => {
                let list = p
                    .into_inner()
                    .map(|x| self.rule_expr(x))
                    .collect::<Result<Vec<_>, _>>()?;
                self.handle_list(list)
            }
            Rule::sampleid => {
                let mut p = p.into_inner();
                let pkgname = p.next().unwrap().as_str();
                let oraclename = p.next().unwrap().as_str();
                let samplename = p.next().unwrap().as_str();
                self.handle_sampleid(pkgname, oraclename, samplename)
            }
            _ => {
                todo!("{p:?}")
            }
        }
    }
}
