// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::syntax::{
    s_expr::{SExpr, SpecConstant},
    tokens::{ReservedWord, Symbol},
};

pub type Result<T> = core::result::Result<T, std::fmt::Error>;

pub struct SExprWriter<'a, W: std::fmt::Write> {
    w: &'a mut W,
    alignment: usize,
    max_width: usize,
}

impl<W: std::fmt::Write> SExprWriter<'_, W> {
    pub fn write(&mut self, s_expr: &SExpr) -> Result<(usize, usize, bool)> {
        self.write_inner(s_expr, 0, 0, None, false, false)
    }

    pub fn write_inner(
        &mut self,
        s_expr: &SExpr,
        mut col: usize,
        parent_col: usize,
        prev_col: Option<usize>,
        needs_delimiter: bool,
        force_newline: bool,
    ) -> Result<(usize, usize, bool)> {
        if needs_delimiter {
            col = self.write_whitespace(col, parent_col, prev_col, force_newline)?;
        }
        let (start, end, needed_newline) = match s_expr {
            //SExpr::HintNewline => Err(alloc::fmt::Error),
            SExpr::Symbol(sym) => self.write_symbol(col, sym),
            SExpr::Const(c) => self.write_const(col, c),
            SExpr::Reserved(res) => self.write_reserved(col, res),

            SExpr::SExpr(exprs) => self.write_sexpr(col, exprs),

            SExpr::HintComment(comment) => {
                self.write_newline(parent_col, prev_col)?;

                for line in comment.lines() {
                    col = self.write_raw(col, "; ")?.1;
                    self.write_raw(col, line)?;
                    self.write_newline(parent_col, prev_col)?;
                }

                Ok((col, col, true))
            }
        }?;

        Ok((start, end, needed_newline))
    }

    /// determines whether that expression needs a newline.
    fn expr_needs_newline(&self, expr: &SExpr) -> bool {
        match expr {
            SExpr::SExpr(exprs) => exprs
                .first()
                .map(|expr| {
                    let len = match expr {
                        SExpr::Const(c) => c.to_string().len(),
                        SExpr::Symbol(sym) => sym.to_string().len(),
                        SExpr::Reserved(res) => res.to_string().len(),
                        SExpr::SExpr(_) => return true,
                        SExpr::HintComment(_) => 0,
                    };
                    len > 2 * self.alignment
                })
                .unwrap_or(false),
            SExpr::HintComment(_) => true,
            _ => false,
        }
    }

    fn write_sexpr(&mut self, col: usize, exprs: &[SExpr]) -> Result<(usize, usize, bool)> {
        if exprs.is_empty() {
            return self.write_raw(col, "()");
        }

        let (_, inner_col, _) = self.write_raw(col, "(")?;

        let mut prev_col = None;
        let mut needs_newline = false;
        let mut needs_delimiter = false;
        let mut cur_col = inner_col;

        for expr in exprs {
            needs_newline |= self.expr_needs_newline(expr);
            let needs_wrap = cur_col - col > self.max_width;

            let (start, end, needed_newline) = self.write_inner(
                expr,
                cur_col,
                col,
                prev_col,
                needs_delimiter,
                needs_newline || needs_wrap,
            )?;

            needs_delimiter = true;
            needs_newline |= needed_newline;
            cur_col = end;
            prev_col = Some(start);
        }

        let (_, end) = self.write_closing_paren(inner_col)?;

        Ok((col, end, needs_newline))
    }

    fn _align_col(col: usize, alignment: usize) -> usize {
        let rest = col % alignment;
        if rest == 0 {
            col
        } else {
            col + alignment - rest
        }
    }

    fn align_col(&self, col: usize) -> usize {
        Self::_align_col(col, self.alignment)
    }

    fn write_newline(&mut self, parent_col: usize, prev_col: Option<usize>) -> Result<usize> {
        let target_col = match prev_col {
            Some(col) => self.align_col(col),
            None => self.align_col(parent_col + 1),
        };

        let spaces = " ".repeat(target_col);
        write!(self.w, "\n{spaces}",).map(|_| target_col)
    }

    fn write_whitespace(
        &mut self,
        col: usize,
        parent_col: usize,
        prev_col: Option<usize>,
        needs_newline: bool,
    ) -> Result<usize> {
        let (maybe_newline, cur_col, target_col) = if needs_newline {
            let target_col = match prev_col {
                Some(prev_col) => self.align_col(prev_col),
                _ => self.align_col(parent_col + self.alignment),
            };

            ("\n", 0, target_col)
        } else {
            let target_col = self.align_col(col + 1);
            ("", col, target_col)
        };

        let spaces = " ".repeat(target_col - cur_col);
        write!(self.w, "{maybe_newline}{spaces}",).map(|_| target_col)
    }

    fn write_const(&mut self, col: usize, c: &SpecConstant) -> Result<(usize, usize, bool)> {
        self.write_raw(col, &c.to_string())
    }

    fn write_symbol(&mut self, col: usize, sym: &Symbol) -> Result<(usize, usize, bool)> {
        self.write_raw(col, &sym.to_string())
    }

    fn write_reserved(&mut self, col: usize, res: &ReservedWord) -> Result<(usize, usize, bool)> {
        self.write_raw(col, &res.to_string())
    }

    fn write_raw(&mut self, col: usize, text: &str) -> Result<(usize, usize, bool)> {
        write!(self.w, "{text}")?;

        Ok((col, col + text.len(), false))
    }

    /// like write_raw, but doesn't add delimiters
    fn write_closing_paren(&mut self, col: usize) -> Result<(usize, usize)> {
        write!(self.w, ")")?;
        Ok((col, 1 + col))
    }
}

#[cfg(test)]
mod test {
    use crate::{
        syntax::{
            command::Command,
            term::{Term, VarBinding},
        },
        theories::core::eq,
    };

    use crate::syntax::{
        fmt::SExprWriter,
        s_expr::SExpr,
        tokens::{Numeral, Symbol},
    };

    #[test]
    fn write_simple() {
        let expr: SExpr = Command::Assert(eq(vec![
            Term::Let(
                vec![VarBinding(
                    Symbol::parse("foo").unwrap(),
                    Numeral(23).into_const().into(),
                )],
                Box::new("foo".into()),
            ),
            Numeral(42).into_const().into(),
        ]))
        .into();

        let mut out = String::new();

        SExprWriter {
            alignment: 3,
            w: &mut out,
            max_width: 30,
        }
        .write(&expr)
        .unwrap();

        println!("{out}");
    }

    #[test]
    fn alignment() {
        let tests = [(13, 1, 13), (12, 2, 12), (15, 4, 16)];

        for (col, al, want) in tests {
            let got = SExprWriter::<String>::_align_col(col, al);
            println!("align({col}, {al}) = {got} / want: {want}");
            assert_eq!(got, want);
        }
    }
}
