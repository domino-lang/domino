// SPDX-License-Identifier: MIT OR Apache-2.0

//! Implements `domino inline`.
//!
//! Given an equivalence proofstep and one of the oracle names it proves equivalent, this renders
//! the code of that oracle for both the left and the right game instance, with:
//!
//!   - package parameters resolved to their concrete value (either a literal from the
//!     composition, or, if the value ultimately comes from a theorem constant, the name of that
//!     constant),
//!   - every oracle invocation recursively replaced by the body of the invoked oracle, so the
//!     reader doesn't have to jump between package definitions to see what a game actually does.
//!
//! The two renderings are then displayed side by side so they can be compared directly.

use std::fmt::Write as _;

use crate::{
    expressions::{Expression, ExpressionKind},
    gamehops::GameHop,
    identifier::{game_ident::GameIdentifier, pkg_ident::PackageIdentifier, Identifier},
    package::{Composition, Edge, OracleSig},
    statement::{Assignment, AssignmentRhs, CodeBlock, InvokeOracle, Pattern, Statement},
    theorem::Theorem,
    transforms::{resolveoracles, Transformation as _},
    types::{CountSpec, Type, TypeKind},
};

/// Recursion is bounded so that a malformed (cyclic) composition can't make us loop forever.
const MAX_INLINE_DEPTH: usize = 128;

#[derive(Debug, thiserror::Error, miette::Diagnostic)]
pub enum Error {
    #[error("theorem `{0}` not found")]
    TheoremNotFound(String),

    #[error(
        "theorem `{theorem}` has no proofstep {index} (it has {len} proofstep(s), numbered starting at 0)"
    )]
    ProofstepNotFound {
        theorem: String,
        index: usize,
        len: usize,
    },

    #[error(
        "proofstep {index} of theorem `{theorem}` is a {kind}, but `domino inline` only supports equivalence proofsteps"
    )]
    NotAnEquivalence {
        theorem: String,
        index: usize,
        kind: &'static str,
    },

    #[error("oracle `{oracle}` is not exported by game instance `{game_inst}`")]
    OracleNotExported { oracle: String, game_inst: String },

    #[error("failed to resolve oracle invocations in game instance `{game_inst}`: {detail}")]
    UnresolvedOracles { game_inst: String, detail: String },
}

pub type Result<T> = std::result::Result<T, Error>;

/// Renders the inlined code of `oracle_name` for both sides of the equivalence proved at
/// `proofstep` of `theorem`, side by side.
pub fn render(theorem: &Theorem, proofstep: usize, oracle_name: &str) -> Result<String> {
    let game_hop = theorem
        .game_hops
        .get(proofstep)
        .ok_or_else(|| Error::ProofstepNotFound {
            theorem: theorem.name.clone(),
            index: proofstep,
            len: theorem.game_hops.len(),
        })?;

    let eq = match game_hop {
        GameHop::Equivalence(eq) => eq,
        GameHop::Reduction(_) => {
            return Err(Error::NotAnEquivalence {
                theorem: theorem.name.clone(),
                index: proofstep,
                kind: "reduction",
            })
        }
        GameHop::Conjecture(_) => {
            return Err(Error::NotAnEquivalence {
                theorem: theorem.name.clone(),
                index: proofstep,
                kind: "conjecture",
            })
        }
        GameHop::Hybrid(_) => {
            return Err(Error::NotAnEquivalence {
                theorem: theorem.name.clone(),
                index: proofstep,
                kind: "hybrid",
            })
        }
    };

    let left_inst = theorem
        .find_game_instance(eq.left_name())
        .expect("equivalence must reference a valid left game instance");
    let right_inst = theorem
        .find_game_instance(eq.right_name())
        .expect("equivalence must reference a valid right game instance");

    let left_code = render_game_instance_oracle(left_inst.game(), left_inst.name(), oracle_name)?;
    let right_code =
        render_game_instance_oracle(right_inst.game(), right_inst.name(), oracle_name)?;

    let mut out = String::new();
    let _ = writeln!(
        out,
        "theorem {}, proofstep {proofstep} ({} == {}), oracle {oracle_name}\n",
        theorem.name,
        eq.left_name(),
        eq.right_name(),
    );
    out.push_str(&side_by_side(&left_code, &right_code));

    Ok(out)
}

fn render_game_instance_oracle(
    comp: &Composition,
    game_inst_name: &str,
    oracle_name: &str,
) -> Result<String> {
    let (comp, _) =
        resolveoracles::Transformation(comp)
            .transform()
            .map_err(|resolveoracles::ResolutionError(unresolved)| Error::UnresolvedOracles {
                game_inst: game_inst_name.to_string(),
                detail: format!("{unresolved:?}"),
            })?;

    let export = comp
        .exports
        .iter()
        .find(|export| export.name() == oracle_name)
        .ok_or_else(|| Error::OracleNotExported {
            oracle: oracle_name.to_string(),
            game_inst: game_inst_name.to_string(),
        })?;

    let pkg_inst = &comp.pkgs[export.to()];
    let odef = pkg_inst
        .pkg
        .oracles
        .iter()
        .find(|odef| odef.sig.name == export.sig().name)
        .expect("export must reference an oracle defined in its target package instance");

    let writer = Writer { comp: &comp };

    let mut out = String::new();
    let _ = writeln!(
        out,
        "// game instance: {game_inst_name}   (package instance: {}, package type: {})",
        pkg_inst.name,
        pkg_inst.pkg.name
    );
    writer.write_signature(&mut out, &odef.sig);
    out.push(' ');
    writer.write_codeblock(&mut out, 0, &odef.code, &ReturnMode::TopLevel, 0);
    out.push('\n');

    Ok(out)
}

/// Puts `left` and `right` next to each other, one line at a time, separated by a `|`.
fn side_by_side(left: &str, right: &str) -> String {
    let left_lines: Vec<&str> = left.lines().collect();
    let right_lines: Vec<&str> = right.lines().collect();

    let width = left_lines
        .iter()
        .map(|line| line.chars().count())
        .max()
        .unwrap_or(0);

    let n = left_lines.len().max(right_lines.len());

    let mut out = String::new();
    for i in 0..n {
        let l = left_lines.get(i).copied().unwrap_or("");
        let r = right_lines.get(i).copied().unwrap_or("");
        let _ = writeln!(out, "{l:width$} | {r}");
    }
    out
}

/// Distinguishes rendering the oracle that was originally asked for (where `return` really does
/// return from the whole invocation) from rendering an oracle that got inlined into a call site
/// (where `return` instead means "bind the invocation's result and continue after this block").
enum ReturnMode<'a> {
    TopLevel,
    Inlined {
        /// The pattern the invocation's result is bound to, or `None` if the invocation's result
        /// is discarded (a bare `invoke Oracle(...);` statement).
        pattern: Option<&'a Pattern>,
        /// `PkgInstanceName.OracleName`, used purely for the trailing comment.
        label: String,
    },
}

struct Writer<'a> {
    comp: &'a Composition,
}

fn pad(indent: usize) -> String {
    "    ".repeat(indent)
}

impl<'a> Writer<'a> {
    fn write_signature(&self, out: &mut String, sig: &OracleSig) {
        let _ = write!(out, "{}(", sig.name);
        let mut first = true;
        for (name, ty) in &sig.args {
            if !first {
                let _ = write!(out, ", ");
            }
            first = false;
            let _ = write!(out, "{name}: ");
            self.write_type(out, ty);
        }
        let _ = write!(out, ") -> ");
        self.write_type(out, &sig.ty);
    }

    fn write_codeblock(
        &self,
        out: &mut String,
        indent: usize,
        cb: &CodeBlock,
        return_mode: &ReturnMode<'_>,
        depth: usize,
    ) {
        out.push_str("{\n");
        for stmt in &cb.0 {
            self.write_statement(out, indent + 1, stmt, return_mode, depth);
        }
        let _ = write!(out, "{}}}", pad(indent));
    }

    fn write_statement(
        &self,
        out: &mut String,
        indent: usize,
        stmt: &Statement,
        return_mode: &ReturnMode<'_>,
        depth: usize,
    ) {
        let p = pad(indent);

        match stmt {
            Statement::Abort(_) => {
                let _ = writeln!(out, "{p}abort;");
            }

            Statement::Return(expr, _) => match return_mode {
                ReturnMode::TopLevel => match expr {
                    Some(e) => {
                        let _ = write!(out, "{p}return ");
                        self.write_expr(out, e);
                        let _ = writeln!(out, ";");
                    }
                    None => {
                        let _ = writeln!(out, "{p}return;");
                    }
                },
                ReturnMode::Inlined { pattern, label } => match (pattern, expr) {
                    (Some(pattern), Some(e)) => {
                        let _ = write!(out, "{p}");
                        self.write_pattern(out, pattern);
                        let _ = write!(out, " <- ");
                        self.write_expr(out, e);
                        let _ = writeln!(out, ";  // return from {label}, exits inlined block");
                    }
                    (Some(pattern), None) => {
                        let _ = write!(out, "{p}");
                        self.write_pattern(out, pattern);
                        let _ =
                            writeln!(out, " <- ();  // return from {label}, exits inlined block");
                    }
                    (None, Some(e)) => {
                        let _ = write!(out, "{p}// return ");
                        self.write_expr(out, e);
                        let _ = writeln!(
                            out,
                            ";  // from {label}, exits inlined block (result discarded)"
                        );
                    }
                    (None, None) => {
                        let _ = writeln!(
                            out,
                            "{p}// return;  from {label}, exits inlined block (result discarded)"
                        );
                    }
                },
            },

            Statement::Assignment(Assignment { pattern, rhs }, _) => match rhs {
                AssignmentRhs::Expression(e) => {
                    let _ = write!(out, "{p}");
                    self.write_pattern(out, pattern);
                    let _ = write!(out, " <- ");
                    self.write_expr(out, e);
                    let _ = writeln!(out, ";");
                }
                AssignmentRhs::Sample {
                    ty, sample_name, ..
                } => {
                    let _ = write!(out, "{p}");
                    self.write_pattern(out, pattern);
                    let _ = write!(out, " <-$ ");
                    self.write_type(out, ty);
                    if let Some(name) = sample_name {
                        let _ = write!(out, " sample-name {name}");
                    }
                    let _ = writeln!(out, ";");
                }
                AssignmentRhs::Invoke {
                    oracle_name,
                    args,
                    edge,
                    ..
                } => {
                    self.write_invoke(
                        out,
                        indent,
                        Some(pattern),
                        oracle_name,
                        args,
                        edge.as_ref(),
                        depth,
                    );
                }
            },

            Statement::InvokeOracle(InvokeOracle {
                oracle_name,
                args,
                edge,
                ..
            }) => {
                self.write_invoke(out, indent, None, oracle_name, args, edge.as_ref(), depth);
            }

            Statement::IfThenElse(ite) => {
                // an `if (cond) {} else { abort; }` is how the language spells `assert (cond)`
                if ite.then_block.0.is_empty()
                    && ite.else_block.0.len() == 1
                    && matches!(ite.else_block.0[0], Statement::Abort(_))
                {
                    let _ = write!(out, "{p}assert (");
                    self.write_expr(out, &ite.cond);
                    let _ = writeln!(out, ");");
                    return;
                }

                let _ = write!(out, "{p}if (");
                self.write_expr(out, &ite.cond);
                let _ = write!(out, ") ");
                self.write_codeblock(out, indent, &ite.then_block, return_mode, depth);

                if !ite.else_block.0.is_empty() {
                    let _ = write!(out, " else ");
                    self.write_codeblock(out, indent, &ite.else_block, return_mode, depth);
                }
                let _ = writeln!(out);
            }

            Statement::For(var, lower, upper, body, _) => {
                let _ = write!(out, "{p}for ");
                out.push_str(&ident_repr(var));
                let _ = write!(out, " from ");
                self.write_expr(out, lower);
                let _ = write!(out, " to ");
                self.write_expr(out, upper);
                let _ = write!(out, " ");
                self.write_codeblock(out, indent, body, return_mode, depth);
                let _ = writeln!(out);
            }
        }
    }

    fn write_invoke(
        &self,
        out: &mut String,
        indent: usize,
        pattern: Option<&Pattern>,
        oracle_name: &str,
        args: &[Expression],
        edge: Option<&Edge>,
        depth: usize,
    ) {
        let p = pad(indent);

        let Some(edge) = edge else {
            // Shouldn't happen: we ran the resolveoracles transform successfully, which fails
            // outright if any invocation can't be resolved to an edge.
            let _ = write!(out, "{p}");
            if let Some(pattern) = pattern {
                self.write_pattern(out, pattern);
                let _ = write!(out, " <- ");
            }
            let _ = writeln!(out, "invoke {oracle_name}(...);  // BUG: unresolved edge");
            return;
        };

        let target_offs = edge.to();
        let target_pkg_inst = &self.comp.pkgs[target_offs];
        let target_inst_name = &target_pkg_inst.name;
        let target_sig = edge.sig();
        let label = format!("{target_inst_name}.{}", target_sig.name);

        let _ = write!(out, "{p}");
        if let Some(pattern) = pattern {
            self.write_pattern(out, pattern);
            let _ = write!(out, " <- ");
        }
        let _ = write!(out, "invoke {oracle_name}(");
        let mut first = true;
        for arg in args {
            if !first {
                let _ = write!(out, ", ");
            }
            first = false;
            self.write_expr(out, arg);
        }
        let _ = writeln!(out, ")  // {label}");

        let Some(target_odef) = target_pkg_inst
            .pkg
            .oracles
            .iter()
            .find(|odef| odef.sig.name == target_sig.name)
        else {
            let _ = writeln!(
                out,
                "{p}// <could not find the definition of {label} to inline it>"
            );
            return;
        };

        if depth >= MAX_INLINE_DEPTH {
            let _ = writeln!(out, "{p}// <not inlining {label}: max inline depth reached>");
            return;
        }

        let _ = writeln!(out, "{p}{{");
        let inner = pad(indent + 1);
        for ((arg_name, arg_ty), arg_expr) in target_sig.args.iter().zip(args) {
            let _ = write!(out, "{inner}{arg_name} <- ");
            self.write_expr(out, arg_expr);
            let _ = write!(out, ";  // : ");
            self.write_type(out, arg_ty);
            let _ = writeln!(out);
        }

        let child_mode = ReturnMode::Inlined { pattern, label };
        for stmt in &target_odef.code.0 {
            self.write_statement(out, indent + 1, stmt, &child_mode, depth + 1);
        }

        let _ = writeln!(out, "{p}}}");
    }

    fn write_pattern(&self, out: &mut String, pattern: &Pattern) {
        match pattern {
            Pattern::Ident(id) => out.push_str(&ident_repr(id)),
            Pattern::Table { ident, index } => {
                out.push_str(&ident_repr(ident));
                out.push('[');
                self.write_expr(out, index);
                out.push(']');
            }
            Pattern::Tuple(ids) => {
                out.push('(');
                let mut first = true;
                for id in ids {
                    if !first {
                        out.push_str(", ");
                    }
                    first = false;
                    out.push_str(&ident_repr(id));
                }
                out.push(')');
            }
        }
    }

    fn write_expr(&self, out: &mut String, expr: &Expression) {
        // Package (and, transitively, game) constants carry the concrete expression they were
        // instantiated with. Follow that chain down to either a literal or a theorem constant
        // (which has no further assignment, since its value isn't fixed by the composition).
        let expr = resolve_const(expr);

        match expr.kind() {
            ExpressionKind::Bot => out.push('\u{22a5}'),
            ExpressionKind::Sample(ty) => {
                out.push_str("Sample(");
                self.write_type(out, ty);
                out.push(')');
            }
            ExpressionKind::StringLiteral(s) => {
                let _ = write!(out, "{s:?}");
            }
            ExpressionKind::IntegerLiteral(i) => {
                let _ = write!(out, "{i}");
            }
            ExpressionKind::BooleanLiteral(s) => out.push_str(s),
            ExpressionKind::BitsLiteral(s, _) => out.push_str(s),
            ExpressionKind::Identifier(ident) => out.push_str(&ident_repr(ident)),
            ExpressionKind::EmptyTable(ty) => {
                out.push_str("EmptyTable(");
                self.write_type(out, ty);
                out.push(')');
            }
            ExpressionKind::TableAccess(ident, index) => {
                out.push_str(&ident_repr(ident));
                out.push('[');
                self.write_expr(out, index);
                out.push(']');
            }
            ExpressionKind::Tuple(exprs) => self.write_list(out, "(", exprs, ")"),
            ExpressionKind::List(exprs) => self.write_list(out, "[", exprs, "]"),
            ExpressionKind::Set(exprs) => self.write_list(out, "{", exprs, "}"),
            ExpressionKind::Concat(exprs) => {
                out.push_str("concat(");
                self.write_joined(out, exprs, ", ");
                out.push(')');
            }
            ExpressionKind::FnCall(ident, args) => {
                self.write_ident(out, ident);
                out.push('(');
                self.write_joined(out, args, ", ");
                out.push(')');
            }
            ExpressionKind::None(_) => out.push_str("None"),
            ExpressionKind::Some(e) => self.write_wrapped(out, "Some(", e, ")"),
            ExpressionKind::Unwrap(e) => self.write_wrapped(out, "Unwrap(", e, ")"),
            ExpressionKind::Not(e) => self.write_wrapped(out, "not (", e, ")"),
            ExpressionKind::Neg(e) => self.write_wrapped(out, "-(", e, ")"),
            ExpressionKind::Inv(e) => self.write_wrapped(out, "(1 / ", e, ")"),
            ExpressionKind::Sum(e) => self.write_wrapped(out, "sum(", e, ")"),
            ExpressionKind::Prod(e) => self.write_wrapped(out, "prod(", e, ")"),
            ExpressionKind::Any(e) => self.write_wrapped(out, "any(", e, ")"),
            ExpressionKind::All(e) => self.write_wrapped(out, "all(", e, ")"),
            ExpressionKind::Union(e) => self.write_wrapped(out, "union(", e, ")"),
            ExpressionKind::Cut(e) => self.write_wrapped(out, "cut(", e, ")"),
            ExpressionKind::SetDiff(e) => self.write_wrapped(out, "setdiff(", e, ")"),
            ExpressionKind::Add(l, r) => self.write_infix(out, l, " + ", r),
            ExpressionKind::Sub(l, r) => self.write_infix(out, l, " - ", r),
            ExpressionKind::Mul(l, r) => self.write_infix(out, l, " * ", r),
            ExpressionKind::Div(l, r) => self.write_infix(out, l, " / ", r),
            ExpressionKind::Pow(l, r) => self.write_infix(out, l, " ^ ", r),
            ExpressionKind::Mod(l, r) => self.write_infix(out, l, " % ", r),
            ExpressionKind::LessThen(l, r) => self.write_infix(out, l, " < ", r),
            ExpressionKind::GreaterThen(l, r) => self.write_infix(out, l, " > ", r),
            ExpressionKind::LessThenEq(l, r) => self.write_infix(out, l, " <= ", r),
            ExpressionKind::GreaterThenEq(l, r) => self.write_infix(out, l, " >= ", r),
            ExpressionKind::Equals(exprs) => self.write_joined_paren(out, exprs, " == "),
            ExpressionKind::And(exprs) => self.write_joined_paren(out, exprs, " and "),
            ExpressionKind::Or(exprs) => self.write_joined_paren(out, exprs, " or "),
            ExpressionKind::Xor(exprs) => self.write_joined_paren(out, exprs, " xor "),
        }
    }

    fn write_list(&self, out: &mut String, open: &str, exprs: &[Expression], close: &str) {
        out.push_str(open);
        self.write_joined(out, exprs, ", ");
        out.push_str(close);
    }

    fn write_joined(&self, out: &mut String, exprs: &[Expression], sep: &str) {
        let mut first = true;
        for e in exprs {
            if !first {
                out.push_str(sep);
            }
            first = false;
            self.write_expr(out, e);
        }
    }

    fn write_joined_paren(&self, out: &mut String, exprs: &[Expression], sep: &str) {
        out.push('(');
        self.write_joined(out, exprs, sep);
        out.push(')');
    }

    fn write_wrapped(&self, out: &mut String, open: &str, expr: &Expression, close: &str) {
        out.push_str(open);
        self.write_expr(out, expr);
        out.push_str(close);
    }

    fn write_infix(&self, out: &mut String, lhs: &Expression, op: &str, rhs: &Expression) {
        out.push('(');
        self.write_expr(out, lhs);
        out.push_str(op);
        self.write_expr(out, rhs);
        out.push(')');
    }

    /// Renders a type the way Domino source spells it, resolving any package/game constants
    /// nested inside (currently only possible via a `Bits(n)` length) to their concrete value,
    /// the same way [`Self::write_expr`] does for expressions.
    fn write_type(&self, out: &mut String, ty: &Type) {
        match ty.kind() {
            TypeKind::Boolean => out.push_str("Bool"),
            TypeKind::Bits(cs) => {
                out.push_str("Bits(");
                self.write_countspec(out, cs);
                out.push(')');
            }
            TypeKind::Maybe(t) => {
                out.push_str("Maybe(");
                self.write_type(out, t);
                out.push(')');
            }
            TypeKind::Tuple(types) => {
                out.push('(');
                let mut first = true;
                for t in types {
                    if !first {
                        out.push_str(", ");
                    }
                    first = false;
                    self.write_type(out, t);
                }
                out.push(')');
            }
            TypeKind::Table(key, value) => {
                out.push_str("Table(");
                self.write_type(out, key);
                out.push_str(", ");
                self.write_type(out, value);
                out.push(')');
            }
            TypeKind::Fn(args, ret) => {
                out.push_str("fn ");
                let mut first = true;
                for t in args {
                    if !first {
                        out.push_str(", ");
                    }
                    first = false;
                    self.write_type(out, t);
                }
                out.push_str(" -> ");
                self.write_type(out, ret);
            }
            // No consts to resolve inside these; the shared `Display` impl already renders them.
            _ => out.push_str(&ty.to_string()),
        }
    }

    /// Resolves a `Bits(n)` length to the concrete value it was instantiated with, following the
    /// same package/game-constant assignment chain as [`resolve_const`].
    fn write_countspec(&self, out: &mut String, cs: &CountSpec) {
        match cs {
            CountSpec::Any | CountSpec::Literal(_) => {
                let _ = write!(out, "{cs}");
            }
            CountSpec::Identifier(ident) => self.write_ident(out, ident),
        }
    }

    /// Renders an identifier standing on its own (as opposed to as the head of an
    /// `ExpressionKind::Identifier`, which [`Self::write_expr`] already resolves via
    /// [`resolve_const`] before it ever reaches [`ident_repr`]). This covers spots where a bare
    /// [`Identifier`] appears without being wrapped in an expression first - e.g. the callee of a
    /// `FnCall`, or a `Bits(n)` length - and so would otherwise print the package/game-local
    /// parameter name instead of the concrete value (or further-along name) it was instantiated
    /// with.
    fn write_ident(&self, out: &mut String, ident: &Identifier) {
        let assignment = match ident {
            Identifier::PackageIdentifier(PackageIdentifier::Const(c)) => {
                c.game_assignment.as_deref()
            }
            Identifier::GameIdentifier(GameIdentifier::Const(c)) => c.assigned_value.as_deref(),
            _ => None,
        };

        match assignment {
            Some(expr) => self.write_expr(out, expr),
            None => out.push_str(&ident_repr(ident)),
        }
    }
}

/// Follows the chain of const-identifier assignments down to either a non-const expression (a
/// literal, most of the time) or an identifier for which we have no further assignment to follow
/// (a theorem constant, or an unresolved const - which shouldn't happen post-instantiation).
fn resolve_const(expr: &Expression) -> &Expression {
    match expr.kind() {
        ExpressionKind::Identifier(Identifier::PackageIdentifier(PackageIdentifier::Const(c))) => {
            match &c.game_assignment {
                Some(inner) => resolve_const(inner),
                None => expr,
            }
        }
        ExpressionKind::Identifier(Identifier::GameIdentifier(GameIdentifier::Const(c))) => {
            match &c.assigned_value {
                Some(inner) => resolve_const(inner),
                None => expr,
            }
        }
        _ => expr,
    }
}

/// The display name of an identifier. Package state is qualified with its owning package
/// instance name (`Instance.field`) since inlining can bring identically-named state from
/// several package instances into the same block.
fn ident_repr(ident: &Identifier) -> String {
    match ident {
        Identifier::Generated(name, _) => name.clone(),

        Identifier::PackageIdentifier(PackageIdentifier::Const(c)) => c.name.clone(),
        Identifier::PackageIdentifier(PackageIdentifier::State(s)) => {
            format!("{}.{}", s.pkg_inst_name.as_deref().unwrap_or(&s.pkg_name), s.name)
        }
        Identifier::PackageIdentifier(PackageIdentifier::Local(l)) => l.name.clone(),
        Identifier::PackageIdentifier(PackageIdentifier::OracleArg(a)) => a.name.clone(),
        Identifier::PackageIdentifier(PackageIdentifier::OracleImport(o)) => o.name.clone(),
        Identifier::PackageIdentifier(PackageIdentifier::ImportsLoopVar(l)) => l.name.clone(),
        Identifier::PackageIdentifier(PackageIdentifier::CodeLoopVar(l)) => l.name.clone(),

        Identifier::GameIdentifier(GameIdentifier::Const(c)) => c.name.clone(),
        Identifier::GameIdentifier(GameIdentifier::LoopVar(l)) => l.name.clone(),

        Identifier::TheoremIdentifier(theorem_ident) => theorem_ident.ident(),
    }
}
