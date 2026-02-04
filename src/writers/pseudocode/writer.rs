// SPDX-License-Identifier: MIT OR Apache-2.0

use std::io::Write;

use crate::expressions::{Expression, ExpressionKind};
use crate::identifier::Identifier;
use crate::package::{OracleDef, OracleSig, Package};
use crate::statement::{CodeBlock, InvokeOracleStatement, Statement};
use crate::types::{CountSpec, Type, TypeKind};

type Result = std::io::Result<()>;

pub struct Writer<W: Write> {
    w: W,
    indent_lvl: usize,
}

impl<W: Write> Writer<W> {
    pub fn new(w: W) -> Self {
        Writer { w, indent_lvl: 0 }
    }

    pub fn write_identifier(&mut self, id: &Identifier) -> Result {
        match id {
            Identifier::Generated(x, _) => {
                self.write_string(x)?;
                self.write_string(" /* generated identifier */ ")?;
            }
            Identifier::PackageIdentifier(_) => todo!(),
            Identifier::GameIdentifier(_) => todo!(),
            Identifier::TheoremIdentifier(_) => todo!(),
        }

        Ok(())
    }

    pub fn write_countspec(&mut self, countspec: &CountSpec) -> Result {
        match countspec {
            CountSpec::Identifier(identifier) => self.write_string(identifier.ident_ref()),
            CountSpec::Literal(num) => self.write_string(&format!("{num}")),
            CountSpec::Any => self.write_string("*"),
        }
    }

    pub fn write_type(&mut self, t: &Type) -> Result {
        match t.kind() {
            TypeKind::String => self.write_string("String"),
            TypeKind::Integer => self.write_string("Integer"),
            TypeKind::Boolean => self.write_string("Boolean"),
            TypeKind::Empty => self.write_string("()"),
            TypeKind::Bits(n) => {
                self.write_string("Bits(")?;
                self.write_string(&format!("{n}"))?;
                self.write_string(")")
            }
            TypeKind::Maybe(t) => {
                self.write_string("Maybe(")?;
                self.write_type(t)?;
                self.write_string(")")
            }
            TypeKind::Tuple(types) => {
                self.write_string("(")?;
                let mut maybe_comma = "";
                for ty in types {
                    self.write_string(maybe_comma)?;
                    self.write_type(ty)?;
                    maybe_comma = ", ";
                }
                self.write_string(")")
            }
            TypeKind::Table(t_key, t_value) => {
                self.write_string("Table(")?;
                self.write_type(t_key)?;
                self.write_string(", ")?;
                self.write_type(t_value)?;
                self.write_string(")")
            }
            TypeKind::Unknown => self.write_string("Unknown"),
            TypeKind::Fn(args, ret) => {
                self.write_string("fn ")?;
                let mut maybe_comma = "";
                for ty in args {
                    self.write_string(maybe_comma)?;
                    self.write_type(ty)?;
                    maybe_comma = ", ";
                }
                self.write_string(" -> ")?;
                self.write_type(ret)
            }
            _ => todo!("`{t:?}'"),
        }
    }

    pub fn write_string(&mut self, string: &str) -> Result {
        write!(&mut self.w, "{string}")
    }

    pub fn write_call(&mut self, name: &str, args: &[Expression]) -> Result {
        self.write_string(name)?;
        self.write_string("(")?;
        let mut maybe_comma = "";
        for arg in args {
            self.write_string(maybe_comma)?;
            self.write_expression(arg)?;
            maybe_comma = ", ";
        }
        self.write_string(")")?;

        Ok(())
    }

    pub fn write_expression(&mut self, expr: &Expression) -> Result {
        match expr.kind() {
            ExpressionKind::EmptyTable(ty) => match ty.kind() {
                TypeKind::Table(t_k, t_v) => {
                    self.write_string("new Table(")?;
                    self.write_type(t_k)?;
                    self.write_string(", ")?;
                    self.write_type(t_v)?;
                    self.write_string(")")?;
                    self.write_string(" /* of type ")?;
                    self.write_type(ty)?;
                    self.write_string(" */ ")?;
                }
                invalid_type => {
                    panic!("invalid type in EmptyTable expression: {invalid_type:?}");
                }
            },

            ExpressionKind::BooleanLiteral(x) => {
                self.write_string(x)?;
            }
            ExpressionKind::IntegerLiteral(x) => {
                self.write_string(&format!("{x}"))?;
            }
            ExpressionKind::StringLiteral(x) => {
                self.write_string(x)?;
            }
            ExpressionKind::Identifier(id) => {
                self.write_identifier(id)?;
            }
            ExpressionKind::Tuple(exprs) => {
                self.write_string("(")?;
                let mut maybe_comma = "";
                for expr in exprs {
                    self.write_string(maybe_comma)?;
                    self.write_expression(expr)?;
                    maybe_comma = ", ";
                }
                self.write_string(")")?;
            }
            ExpressionKind::FnCall(id, args) => {
                self.write_call(id.ident_ref(), args.as_slice())?;
            }
            ExpressionKind::Equals(exprs) => {
                assert_eq!(exprs.len(), 2);

                let left = &exprs[0];
                let right = &exprs[1];

                self.write_expression(left)?;
                self.write_string(" == ")?;
                self.write_expression(right)?;
            }
            ExpressionKind::And(exprs) => {
                assert_eq!(exprs.len(), 2);

                let left = &exprs[0];
                let right = &exprs[1];

                self.write_expression(left)?;
                self.write_string(" and ")?;
                self.write_expression(right)?;
            }
            ExpressionKind::Or(exprs) => {
                assert_eq!(exprs.len(), 2);

                let left = &exprs[0];
                let right = &exprs[1];

                self.write_expression(left)?;
                self.write_string(" or ")?;
                self.write_expression(right)?;
            }
            ExpressionKind::Add(left, right) => {
                self.write_expression(left)?;
                self.write_string(" + ")?;
                self.write_expression(right)?;
            }
            ExpressionKind::Sub(left, right) => {
                self.write_expression(left)?;
                self.write_string(" - ")?;
                self.write_expression(right)?;
            }
            ExpressionKind::Unwrap(expr) => {
                self.write_string("Unwrap(")?;
                self.write_expression(expr)?;
                self.write_string(")")?;
            }
            ExpressionKind::None(_) => {
                self.write_string("None")?;
            }
            ExpressionKind::Some(expr) => {
                self.write_string("Some(")?;
                self.write_expression(expr)?;
                self.write_string(")")?;
            }
            ExpressionKind::Not(expr) => {
                self.write_string("!")?;
                self.write_expression(expr)?;
            }
            ExpressionKind::TableAccess(id, idx) => {
                self.write_identifier(id)?;
                self.write_string("[")?;
                self.write_expression(idx)?;
                self.write_string("]")?;
            }
            _ => {
                todo!("{:#?}", expr)
            }
        }

        Ok(())
    }

    pub fn write_statement(&mut self, stmt: &Statement) -> Result {
        self.write_string(&"\t".repeat(self.indent_lvl))?;

        match stmt {
            Statement::Assign(id, idx, expr, _) => {
                self.write_identifier(id)?;

                if let Some(idx) = idx {
                    self.write_string("[")?;
                    self.write_expression(idx)?;
                    self.write_string("]")?;
                }

                self.write_string(" <- ")?;
                self.write_expression(expr)?;
                self.write_string(";\n")?;
            }
            Statement::Return(expr, _) => {
                if let Some(expr) = expr {
                    self.write_string("return ")?;
                    self.write_expression(expr)?;
                    self.write_string(";\n")?;
                } else {
                    self.write_string("return;\n")?;
                }
            }
            Statement::Sample(id, idx, sample_id, t, _, _) => {
                self.write_identifier(id)?;

                if let Some(idx) = idx {
                    self.write_string("[")?;
                    self.write_expression(idx)?;
                    self.write_string("]")?;
                }

                self.write_string(" <-$ ")?;
                self.write_type(t)?;
                if let Some(sample_id) = sample_id {
                    self.write_string(&format!("; /* with sample_id {sample_id} */\n"))?;
                } else {
                    self.write_string("; /* sample_id not assigned */\n")?;
                }
            }
            Statement::InvokeOracle(InvokeOracleStatement {
                id,
                opt_idx,
                name,
                args,
                target_inst_name,
                ty: opt_ty,
                ..
            }) => {
                self.write_identifier(id)?;

                if let Some(idx) = opt_idx {
                    self.write_string("[")?;
                    self.write_expression(idx)?;
                    self.write_string("]")?;
                }

                self.write_string(" <- invoke ")?;
                self.write_call(name, args.as_slice())?;
                if let Some(target_inst_name) = target_inst_name {
                    self.write_string(&format!(
                        "; /* with target instance name {target_inst_name} */"
                    ))?;
                } else {
                    self.write_string("; /* target instance name not assigned */")?;
                }
                if let Some(ty) = opt_ty {
                    self.write_string(&format!(" /* return type {ty:?} */"))?;
                } else {
                    self.write_string(" /* return type unknown */")?;
                }
                self.write_string("\n")?;
            }
            Statement::IfThenElse(ite) => {
                // check if this an assert
                if ite.then_block.0.is_empty()
                    && ite.else_block.0.len() == 1
                    && matches!(ite.else_block.0[0], Statement::Abort(_))
                {
                    self.write_string("assert (")?;
                    self.write_expression(&ite.cond)?;
                    self.write_string(");\n")?;
                    return Ok(());
                }

                self.write_string("if (")?;
                self.write_expression(&ite.cond)?;
                self.write_string(") ")?;
                self.write_codeblock(&ite.then_block)?;

                if !ite.else_block.0.is_empty() {
                    self.write_string(" else ")?;
                    self.write_codeblock(&ite.else_block)?;
                }

                self.write_string("\n")?;
            }
            Statement::For(_, _, _, _, _) => todo!(),
            Statement::Abort(_) => {
                self.write_string("abort;\n")?;
            }
            Statement::Parse(ids, expr, _) => {
                self.write_string("(")?;
                let mut maybe_comma = "";
                for id in ids {
                    self.write_string(maybe_comma)?;
                    self.write_identifier(id)?;
                    maybe_comma = ", ";
                }
                self.write_string(")")?;

                self.write_string(" <- parse ")?;
                self.write_expression(expr)?;
                self.write_string(";\n")?;
            }
        }

        Ok(())
    }

    pub fn write_codeblock(&mut self, cb: &CodeBlock) -> Result {
        let CodeBlock(stmts) = cb;

        self.write_string("{\n")?;
        self.indent_lvl += 1;

        for stmt in stmts {
            self.write_statement(stmt)?;
        }

        self.indent_lvl -= 1;
        self.write_string(&format!("{}}}", "\t".repeat(self.indent_lvl)))?;

        Ok(())
    }

    pub fn write_oraclesig(&mut self, sig: &OracleSig) -> Result {
        let OracleSig { name, args, ty, .. } = sig;

        self.write_string(name)?;
        self.write_string("(")?;

        let mut maybe_comma = "";
        for (arg_name, arg_type) in args {
            self.write_string(maybe_comma)?;
            self.write_string(&format!("{arg_name}: "))?;
            self.write_type(arg_type)?;
            maybe_comma = ", ";
        }

        self.write_string(")")?;
        self.write_string(" -> ")?;
        self.write_type(ty)?;

        Ok(())
    }

    pub fn write_oracledef(&mut self, odef: &OracleDef) -> Result {
        let OracleDef { sig, code, .. } = odef;

        self.write_oraclesig(sig)?;
        self.write_string(" ")?;
        self.write_codeblock(code)?;

        Ok(())
    }

    pub fn write_package(&mut self, pkg: &Package) -> Result {
        for odef in &pkg.oracles {
            self.write_oracledef(odef)?;
            self.write_string("\n")?;
        }

        Ok(())
    }
}
