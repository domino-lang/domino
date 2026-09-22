// SPDX-License-Identifier: MIT OR Apache-2.0

//! `easycryptify` — lowers every early exit of an oracle body into EasyCrypt's
//! single-exit shape, without duplicating code
//! (`docs/stories/easycrypt/16-easycryptify.md`).
//!
//! This is a Domino→Domino transform. Its output is ordinary, typecheckable
//! Domino with the same observable behaviour as its input, and every oracle
//! body satisfies (§3.1 of the story):
//!
//! 1. it contains **no `Abort`** and exactly **one `Return`**, as its final
//!    statement;
//! 2. that `Return` returns the local [`EC_RESULT`];
//! 3. the oracle's signature return type is `Maybe(T)` where it was `T` —
//!    `None` is abort. Every copy of every signature (the `OracleDef`, the
//!    callers' `imports`, `Composition::edges`, `Composition::exports`, and the
//!    `Edge` embedded in each resolved `invoke`) is rewritten together.
//!
//! Unlike `treeify` (which serves the SMT writer and pushes the continuation
//! of an `if` into *both* arms), no statement is ever duplicated here: the
//! continuation of a statement that may terminate is **moved** into the one
//! branch that survives it, and only a genuine join of two live paths is
//! followed by an `if (not ec_done) { … }` guard (§3.3).
//!
//! It runs last in [`crate::transforms::theorem_transforms::EasyCryptTransform`],
//! after `tableinitialize`, which pattern-matches on `T[k] <- invoke …` — a
//! shape this transform rewrites.

use miette::{Diagnostic, SourceSpan};
use thiserror::Error;

use crate::expressions::{Expression, ExpressionKind};
use crate::identifier::Identifier;
use crate::package::{Composition, Edge, Export, OracleSig};
use crate::statement::{
    Assignment, AssignmentRhs, CodeBlock, IfThenElse, InvokeOracle, Pattern, Statement,
};
use crate::types::{Type, TypeKind};

/// The oracle-local holding the value the oracle will return: `None` (abort)
/// until a `return` sets it to `Some(v)`.
pub const EC_RESULT: &str = "ec_result";
/// The oracle-local recording that a `return` or `abort` has already
/// happened, read only by the `if (not ec_done)` guard after a join. Dropped
/// from an oracle that has no such guard.
pub const EC_DONE: &str = "ec_done";
/// Prefix of the `ec_r<N>` temporaries binding an `invoke`'s `Maybe` result.
pub const EC_INVOKE_PREFIX: &str = "ec_r";

/// Whether `name` is one of the identifiers this transform generates. The
/// EasyCrypt writer passes these through verbatim; its name mangler reserves
/// the `ec_` prefix for exactly such exporter-owned names and escapes any
/// user identifier that starts with it.
pub fn is_generated_name(name: &str) -> bool {
    name == EC_RESULT
        || name == EC_DONE
        || name
            .strip_prefix(EC_INVOKE_PREFIX)
            .is_some_and(|n| !n.is_empty() && n.chars().all(|c| c.is_ascii_digit()))
}

/// The construct named when a `for` loop reaches this transform. `loopunroll`
/// only leaves loops it could not unroll, which have no EasyCrypt translation.
pub const UNSUPPORTED_FOR: &str =
    "For (loopunroll leaves only unbounded loops, which have no EasyCrypt translation)";

/// A `for` loop survived `loopunroll` into an oracle body. The EasyCrypt
/// writer turns this into its `UnsupportedStatement` hard error, span kept.
#[derive(Debug, Clone, PartialEq, Eq, Error, Diagnostic)]
#[error("unsupported statement for EasyCrypt export: {UNSUPPORTED_FOR}")]
pub struct UnsupportedLoopError {
    #[label("this loop")]
    pub span: SourceSpan,
}

pub struct Transformation<'a>(pub &'a Composition);

impl super::Transformation for Transformation<'_> {
    type Err = UnsupportedLoopError;
    type Aux = ();

    fn transform(&self) -> Result<(Composition, ()), UnsupportedLoopError> {
        let mut comp = self.0.clone();
        for inst in &mut comp.pkgs {
            for oracle in &mut inst.pkg.oracles {
                oracle.code = lower_oracle(&oracle.code, &oracle.sig.ty, oracle.file_pos)?;
                oracle.sig = wrap_sig(&oracle.sig);
            }
            for (sig, _) in &mut inst.pkg.imports {
                *sig = wrap_sig(sig);
            }
        }
        comp.edges = comp.edges.iter().map(wrap_edge).collect();
        comp.exports = comp
            .exports
            .iter()
            .map(|e| Export::new(e.to(), wrap_sig(e.sig()), e.alias().map(str::to_string)))
            .collect();
        Ok((comp, ()))
    }
}

fn wrap_sig(sig: &OracleSig) -> OracleSig {
    OracleSig {
        ty: Type::maybe(sig.ty.clone()),
        ..sig.clone()
    }
}

fn wrap_edge(edge: &Edge) -> Edge {
    Edge::new(
        edge.from(),
        edge.to(),
        wrap_sig(edge.sig()),
        edge.alias().cloned(),
    )
}

// ---------------------------------------------------------------------------
// Terminality (§3.2)
// ---------------------------------------------------------------------------

/// "Can this terminate the oracle?", computed on the *input* statements.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Term {
    Never,
    Maybe,
    Always,
}

fn is_unwrap_assignment(rhs: &AssignmentRhs) -> bool {
    matches!(rhs, AssignmentRhs::Expression(e) if matches!(e.kind(), ExpressionKind::Unwrap(_)))
}

fn term_stmt(stmt: &Statement) -> Term {
    match stmt {
        Statement::Abort(_) | Statement::Return(_, _) => Term::Always,
        Statement::Assignment(Assignment { rhs, .. }, _) => match rhs {
            AssignmentRhs::Invoke { .. } => Term::Maybe,
            rhs if is_unwrap_assignment(rhs) => Term::Maybe,
            _ => Term::Never,
        },
        Statement::InvokeOracle(_) => Term::Maybe,
        Statement::IfThenElse(ite) => {
            match (term_block(&ite.then_block.0), term_block(&ite.else_block.0)) {
                (Term::Always, Term::Always) => Term::Always,
                (Term::Never, Term::Never) => Term::Never,
                _ => Term::Maybe,
            }
        }
        // A surviving loop is a hard error, raised when `lower` reaches it
        // (it is only unreachable if something before it always terminates,
        // in which case it is dropped like any other dead statement).
        // `Maybe` is the conservative answer until then.
        Statement::For(..) => Term::Maybe,
    }
}

/// Fold left to right: the first `Always` makes the block `Always` (anything
/// after it is unreachable); otherwise `Maybe` if any statement is `Maybe`.
fn term_block(stmts: &[Statement]) -> Term {
    let mut acc = Term::Never;
    for stmt in stmts {
        match term_stmt(stmt) {
            Term::Always => return Term::Always,
            Term::Maybe => acc = Term::Maybe,
            Term::Never => {}
        }
    }
    acc
}

// ---------------------------------------------------------------------------
// Lowering (§3.3, §3.4)
// ---------------------------------------------------------------------------

/// Lowers one oracle body: `ec_result <- None; ec_done <- false; <lower(body)>;
/// return ec_result;`, then drops `ec_done` if nothing reads it (§3.4).
fn lower_oracle(
    code: &CodeBlock,
    ret_ty: &Type,
    oracle_span: SourceSpan,
) -> Result<CodeBlock, UnsupportedLoopError> {
    let mut lowerer = Lowerer {
        ec_result: Identifier::Generated(EC_RESULT.to_string(), Type::maybe(ret_ty.clone())),
        ec_done: Identifier::Generated(EC_DONE.to_string(), Type::boolean()),
        invoke_ctr: 0,
    };

    let mut out = vec![
        assign(
            Pattern::Ident(lowerer.ec_result.clone()),
            Expression::from_kind(ExpressionKind::None(ret_ty.clone())),
            oracle_span,
        ),
        lowerer.set_done(false, oracle_span),
    ];
    let (body, _) = lowerer.lower(&code.0)?;
    out.extend(body);
    out.push(Statement::Return(
        Some(lowerer.ec_result.clone().into()),
        oracle_span,
    ));

    if !contains_done_guard(&out, &lowerer.ec_done) {
        out = drop_done(out, &lowerer.ec_done);
    }
    Ok(CodeBlock(out))
}

fn assign(pattern: Pattern, rhs: Expression, span: SourceSpan) -> Statement {
    Statement::Assignment(
        Assignment {
            pattern,
            rhs: AssignmentRhs::Expression(rhs),
        },
        span,
    )
}

fn not(e: Expression) -> Expression {
    Expression::from_kind(ExpressionKind::Not(Box::new(e)))
}

/// `not (e == None)`, for a `Maybe(T)`-typed `e`.
fn is_some(e: &Expression) -> Expression {
    let TypeKind::Maybe(inner) = e.get_type().into_kind() else {
        unreachable!("an unwrapped or invoke-bound value is always Maybe-typed: {e:?}")
    };
    not(Expression::equals(vec![
        e.clone(),
        Expression::from_kind(ExpressionKind::None(*inner)),
    ]))
}

fn if_then_else(
    cond: Expression,
    then: Vec<Statement>,
    els: Vec<Statement>,
    span: SourceSpan,
) -> Statement {
    Statement::IfThenElse(IfThenElse {
        cond,
        then_block: CodeBlock(then),
        else_block: CodeBlock(els),
        then_span: span,
        else_span: span,
        full_span: span,
    })
}

struct Lowerer {
    ec_result: Identifier,
    ec_done: Identifier,
    /// Per-oracle `ec_r<N>` counter; the first temporary is `ec_r1`.
    invoke_ctr: usize,
}

impl Lowerer {
    fn set_done(&self, value: bool, span: SourceSpan) -> Statement {
        assign(
            Pattern::Ident(self.ec_done.clone()),
            Expression::boolean(value),
            span,
        )
    }

    /// `if (not (e == None)) { <then> } else { ec_done <- true }`.
    fn guard(&self, maybe: &Expression, then: Vec<Statement>, span: SourceSpan) -> Statement {
        if_then_else(is_some(maybe), then, vec![self.set_done(true, span)], span)
    }

    /// Lowers one block. The returned statements never terminate early; the
    /// bool is true if any path through them can set `ec_done`.
    fn lower(
        &mut self,
        stmts: &[Statement],
    ) -> Result<(Vec<Statement>, bool), UnsupportedLoopError> {
        let mut out = Vec::new();
        let mut i = 0;
        while i < stmts.len() {
            let rest = &stmts[i + 1..];
            match &stmts[i] {
                Statement::Abort(span) => {
                    out.push(self.set_done(true, *span));
                    return Ok((out, true));
                }

                Statement::Return(value, span) => {
                    let value = value
                        .clone()
                        .unwrap_or_else(|| Expression::from_kind(ExpressionKind::Bot));
                    out.push(assign(
                        Pattern::Ident(self.ec_result.clone()),
                        Expression::from_kind(ExpressionKind::Some(Box::new(value))),
                        *span,
                    ));
                    out.push(self.set_done(true, *span));
                    return Ok((out, true));
                }

                Statement::Assignment(
                    Assignment {
                        rhs: AssignmentRhs::Expression(e),
                        ..
                    },
                    span,
                ) if matches!(e.kind(), ExpressionKind::Unwrap(_)) => {
                    let ExpressionKind::Unwrap(inner) = e.kind() else {
                        unreachable!()
                    };
                    // The binding stays `x <- Unwrap(e)`: it cannot abort any
                    // more, so the writer lowers it to a plain `oget e`.
                    let mut then = vec![stmts[i].clone()];
                    then.extend(self.lower(rest)?.0);
                    out.push(self.guard(inner, then, *span));
                    return Ok((out, true));
                }

                Statement::Assignment(
                    Assignment {
                        pattern,
                        rhs:
                            AssignmentRhs::Invoke {
                                oracle_name,
                                args,
                                edge,
                                return_type,
                            },
                    },
                    span,
                ) => {
                    let callee_ty = edge
                        .as_ref()
                        .map(|e| e.sig().ty.clone())
                        .or_else(|| return_type.clone())
                        .expect("an invoke's result type is known once resolveoracles has run");
                    let (temp, call) = self.bind_invoke(oracle_name, args, edge, &callee_ty, *span);
                    out.push(call);
                    let unwrapped =
                        Expression::from_kind(ExpressionKind::Unwrap(Box::new(temp.clone())));
                    // A table write stores `Maybe`s: `T[k] <- invoke O()`
                    // stores the invoke's value, so its lowering is
                    // `T[k] <- Some(Unwrap(ec_rN))`.
                    let rhs = match pattern {
                        Pattern::Table { .. } => {
                            Expression::from_kind(ExpressionKind::Some(Box::new(unwrapped)))
                        }
                        Pattern::Ident(_) | Pattern::Tuple(_) => unwrapped,
                    };
                    let mut then = vec![assign(pattern.clone(), rhs, *span)];
                    then.extend(self.lower(rest)?.0);
                    out.push(self.guard(&temp, then, *span));
                    return Ok((out, true));
                }

                Statement::InvokeOracle(InvokeOracle {
                    oracle_name,
                    args,
                    edge,
                    file_pos,
                }) => {
                    let callee_ty = edge
                        .as_ref()
                        .map(|e| e.sig().ty.clone())
                        .expect("resolveoracles attaches an Edge to every invoke");
                    let (temp, call) =
                        self.bind_invoke(oracle_name, args, edge, &callee_ty, *file_pos);
                    out.push(call);
                    let then = self.lower(rest)?.0;
                    out.push(self.guard(&temp, then, *file_pos));
                    return Ok((out, true));
                }

                Statement::IfThenElse(ite) => {
                    let then_term = term_block(&ite.then_block.0);
                    let else_term = term_block(&ite.else_block.0);
                    let rebuild = |then: Vec<Statement>, els: Vec<Statement>| {
                        Statement::IfThenElse(IfThenElse {
                            then_block: CodeBlock(then),
                            else_block: CodeBlock(els),
                            ..ite.clone()
                        })
                    };
                    match (then_term, else_term) {
                        (Term::Always, Term::Always) => {
                            let then = self.lower(&ite.then_block.0)?.0;
                            let els = self.lower(&ite.else_block.0)?.0;
                            out.push(rebuild(then, els));
                            return Ok((out, true));
                        }
                        // Only the else branch survives the `if`, so the
                        // continuation moves into it.
                        (Term::Always, _) => {
                            let then = self.lower(&ite.then_block.0)?.0;
                            let els = self.lower(&concat(&ite.else_block.0, rest))?.0;
                            out.push(rebuild(then, els));
                            return Ok((out, true));
                        }
                        // The `assert` case: `assert c; REST` becomes
                        // `if (c) { REST } else { ec_done <- true }`.
                        (_, Term::Always) => {
                            let then = self.lower(&concat(&ite.then_block.0, rest))?.0;
                            let els = self.lower(&ite.else_block.0)?.0;
                            out.push(rebuild(then, els));
                            return Ok((out, true));
                        }
                        _ => {
                            let (then, d1) = self.lower(&ite.then_block.0)?;
                            let (els, d2) = self.lower(&ite.else_block.0)?;
                            out.push(rebuild(then, els));
                            if d1 || d2 {
                                // A join of two live paths, at least one of
                                // which may already have terminated: the one
                                // shape that needs the flag.
                                if !rest.is_empty() {
                                    let guarded = self.lower(rest)?.0;
                                    out.push(if_then_else(
                                        not(self.ec_done.clone().into()),
                                        guarded,
                                        vec![],
                                        ite.full_span,
                                    ));
                                }
                                return Ok((out, true));
                            }
                            // Nothing under it can terminate: leave the rest
                            // exactly where the source had it.
                            i += 1;
                        }
                    }
                }

                Statement::For(_, _, _, _, span) => {
                    return Err(UnsupportedLoopError { span: *span });
                }

                other @ Statement::Assignment(..) => {
                    out.push(other.clone());
                    i += 1;
                }
            }
        }
        Ok((out, false))
    }

    /// `ec_rN <- invoke O(args)`, `ec_rN : Maybe(T)` for the callee's
    /// original return type `T`. Returns the temporary and the statement.
    fn bind_invoke(
        &mut self,
        oracle_name: &str,
        args: &[Expression],
        edge: &Option<Edge>,
        callee_ty: &Type,
        span: SourceSpan,
    ) -> (Expression, Statement) {
        self.invoke_ctr += 1;
        let maybe_ty = Type::maybe(callee_ty.clone());
        let temp = Identifier::Generated(
            format!("{EC_INVOKE_PREFIX}{}", self.invoke_ctr),
            maybe_ty.clone(),
        );
        let stmt = Statement::Assignment(
            Assignment {
                pattern: Pattern::Ident(temp.clone()),
                rhs: AssignmentRhs::Invoke {
                    oracle_name: oracle_name.to_string(),
                    args: args.to_vec(),
                    edge: edge.as_ref().map(wrap_edge),
                    return_type: Some(maybe_ty),
                },
            },
            span,
        );
        (temp.into(), stmt)
    }
}

fn concat(a: &[Statement], b: &[Statement]) -> Vec<Statement> {
    a.iter().chain(b).cloned().collect()
}

// ---------------------------------------------------------------------------
// Dropping an unused `ec_done` (§3.4)
// ---------------------------------------------------------------------------

fn is_done_guard(cond: &Expression, ec_done: &Identifier) -> bool {
    matches!(
        cond.kind(),
        ExpressionKind::Not(inner)
            if matches!(inner.kind(), ExpressionKind::Identifier(id) if id == ec_done)
    )
}

fn contains_done_guard(stmts: &[Statement], ec_done: &Identifier) -> bool {
    stmts.iter().any(|stmt| match stmt {
        Statement::IfThenElse(ite) => {
            is_done_guard(&ite.cond, ec_done)
                || contains_done_guard(&ite.then_block.0, ec_done)
                || contains_done_guard(&ite.else_block.0, ec_done)
        }
        _ => false,
    })
}

/// Deletes every `ec_done <- …`. An `if` whose *then* branch held nothing but
/// such an assignment (`if c { abort } else { … }` in the source) would be
/// left with an empty *then* branch; it is flipped to `if (not c) { … }` so
/// the writer never emits an empty branch. An `if` that already had an empty
/// branch in the source is left as the source had it.
fn drop_done(stmts: Vec<Statement>, ec_done: &Identifier) -> Vec<Statement> {
    stmts
        .into_iter()
        .filter(|stmt| {
            !matches!(
                stmt,
                Statement::Assignment(Assignment { pattern: Pattern::Ident(id), .. }, _) if id == ec_done
            )
        })
        .map(|stmt| match stmt {
            Statement::IfThenElse(ite) => {
                let then_was_empty = ite.then_block.0.is_empty();
                let then = drop_done(ite.then_block.0, ec_done);
                let els = drop_done(ite.else_block.0, ec_done);
                if then.is_empty() && !then_was_empty && !els.is_empty() {
                    let cond = match ite.cond.into_kind() {
                        ExpressionKind::Not(inner) => *inner,
                        other => not(Expression::from_kind(other)),
                    };
                    Statement::IfThenElse(IfThenElse {
                        cond,
                        then_block: CodeBlock(els),
                        else_block: CodeBlock(vec![]),
                        then_span: ite.else_span,
                        else_span: ite.then_span,
                        full_span: ite.full_span,
                    })
                } else {
                    Statement::IfThenElse(IfThenElse {
                        then_block: CodeBlock(then),
                        else_block: CodeBlock(els),
                        ..ite
                    })
                }
            }
            other => other,
        })
        .collect()
}

#[cfg(test)]
mod tests {
    //! `CodeBlock` in / `CodeBlock` out, no solver (§4). Expectations are
    //! written in a compact Domino-like text ([`show`]) so each test reads like
    //! the shape it pins down.

    use super::*;
    use crate::package::{OracleDef, Package};
    use crate::packageinstance::PackageInstance;
    use crate::transforms::Transformation as _;

    fn span() -> SourceSpan {
        (0, 1).into()
    }

    fn var(name: &str, ty: Type) -> Identifier {
        Identifier::Generated(name.to_string(), ty)
    }

    fn int_var(name: &str) -> Identifier {
        var(name, Type::integer())
    }

    fn bool_var(name: &str) -> Expression {
        var(name, Type::boolean()).into()
    }

    fn set(name: &str, value: i64) -> Statement {
        assign(
            Pattern::Ident(int_var(name)),
            Expression::integer(value),
            span(),
        )
    }

    fn ret(value: i64) -> Statement {
        Statement::Return(Some(Expression::integer(value)), span())
    }

    fn abort() -> Statement {
        Statement::Abort(span())
    }

    fn ite(cond: &str, then: Vec<Statement>, els: Vec<Statement>) -> Statement {
        if_then_else(bool_var(cond), then, els, span())
    }

    /// The parser's desugaring of `assert c` (`src/parser/package.rs`).
    fn assert_(cond: &str) -> Statement {
        ite(cond, vec![], vec![abort()])
    }

    /// `x <- Unwrap(m)`, `m : Maybe(Integer)` — the shape `unwrapify` leaves.
    fn unwrap(x: &str, m: &str) -> Statement {
        let m: Expression = var(m, Type::maybe(Type::integer())).into();
        assign(
            Pattern::Ident(int_var(x)),
            Expression::from_kind(ExpressionKind::Unwrap(Box::new(m))),
            span(),
        )
    }

    fn callee_sig(name: &str, ty: Type) -> OracleSig {
        OracleSig {
            name: name.to_string(),
            args: vec![],
            ty,
        }
    }

    fn edge(name: &str, ty: Type) -> Edge {
        Edge::new(0, 1, callee_sig(name, ty), None)
    }

    /// `x <- invoke O()`, `O() -> Integer`, resolved.
    fn invoke(x: &str, oracle: &str) -> Statement {
        Statement::Assignment(
            Assignment {
                pattern: Pattern::Ident(int_var(x)),
                rhs: AssignmentRhs::Invoke {
                    oracle_name: oracle.to_string(),
                    args: vec![],
                    edge: Some(edge(oracle, Type::integer())),
                    return_type: Some(Type::integer()),
                },
            },
            span(),
        )
    }

    fn lower_int_oracle(body: Vec<Statement>) -> CodeBlock {
        lower_oracle(&CodeBlock(body), &Type::integer(), span()).unwrap()
    }

    // --- a compact renderer, for readable expectations ---------------------

    fn show_expr(e: &Expression) -> String {
        match e.kind() {
            ExpressionKind::Identifier(id) => id.ident(),
            ExpressionKind::IntegerLiteral(i) => i.to_string(),
            ExpressionKind::BooleanLiteral(b) => b.clone(),
            ExpressionKind::Bot => "()".to_string(),
            ExpressionKind::None(_) => "None".to_string(),
            ExpressionKind::Some(e) => format!("Some({})", show_expr(e)),
            ExpressionKind::Unwrap(e) => format!("Unwrap({})", show_expr(e)),
            ExpressionKind::Not(e) => format!("not {}", show_expr(e)),
            ExpressionKind::Equals(es) => format!(
                "({})",
                es.iter().map(show_expr).collect::<Vec<_>>().join(" == ")
            ),
            ExpressionKind::TableAccess(id, idx) => format!("{}[{}]", id.ident(), show_expr(idx)),
            other => format!("{other:?}"),
        }
    }

    fn show_pattern(p: &Pattern) -> String {
        match p {
            Pattern::Ident(id) => id.ident(),
            Pattern::Table { ident, index } => format!("{}[{}]", ident.ident(), show_expr(index)),
            Pattern::Tuple(ids) => format!(
                "({})",
                ids.iter().map(|i| i.ident()).collect::<Vec<_>>().join(", ")
            ),
        }
    }

    fn show_into(stmts: &[Statement], indent: usize, out: &mut String) {
        let pad = "  ".repeat(indent);
        for stmt in stmts {
            match stmt {
                Statement::Abort(_) => out.push_str(&format!("{pad}abort\n")),
                Statement::Return(v, _) => out.push_str(&format!(
                    "{pad}return {}\n",
                    v.as_ref().map(show_expr).unwrap_or_default()
                )),
                Statement::Assignment(Assignment { pattern, rhs }, _) => {
                    let rhs = match rhs {
                        AssignmentRhs::Expression(e) => show_expr(e),
                        AssignmentRhs::Sample { .. } => "$".to_string(),
                        AssignmentRhs::Invoke { oracle_name, .. } => {
                            format!("invoke {oracle_name}()")
                        }
                    };
                    out.push_str(&format!("{pad}{} <- {rhs}\n", show_pattern(pattern)));
                }
                Statement::InvokeOracle(inv) => {
                    out.push_str(&format!("{pad}invoke {}()\n", inv.oracle_name))
                }
                Statement::IfThenElse(ite) => {
                    out.push_str(&format!("{pad}if {} {{\n", show_expr(&ite.cond)));
                    show_into(&ite.then_block.0, indent + 1, out);
                    if !ite.else_block.0.is_empty() {
                        out.push_str(&format!("{pad}}} else {{\n"));
                        show_into(&ite.else_block.0, indent + 1, out);
                    }
                    out.push_str(&format!("{pad}}}\n"));
                }
                Statement::For(..) => out.push_str(&format!("{pad}for\n")),
            }
        }
    }

    fn show(cb: &CodeBlock) -> String {
        let mut out = String::new();
        show_into(&cb.0, 0, &mut out);
        out
    }

    fn count_ifs(stmts: &[Statement]) -> usize {
        stmts
            .iter()
            .map(|s| match s {
                Statement::IfThenElse(ite) => {
                    1 + count_ifs(&ite.then_block.0) + count_ifs(&ite.else_block.0)
                }
                _ => 0,
            })
            .sum()
    }

    fn has_empty_then(stmts: &[Statement]) -> bool {
        stmts.iter().any(|s| match s {
            Statement::IfThenElse(ite) => {
                ite.then_block.0.is_empty()
                    || has_empty_then(&ite.then_block.0)
                    || has_empty_then(&ite.else_block.0)
            }
            _ => false,
        })
    }

    /// §3.1: no `Abort` anywhere, one `Return`, last.
    fn assert_single_exit(cb: &CodeBlock) {
        fn walk(stmts: &[Statement], returns: &mut usize) {
            for s in stmts {
                match s {
                    Statement::Abort(_) => panic!("an Abort survived easycryptify"),
                    Statement::Return(..) => *returns += 1,
                    Statement::IfThenElse(ite) => {
                        walk(&ite.then_block.0, returns);
                        walk(&ite.else_block.0, returns);
                    }
                    _ => {}
                }
            }
        }
        let mut returns = 0;
        walk(&cb.0, &mut returns);
        assert_eq!(returns, 1, "expected exactly one Return:\n{}", show(cb));
        assert!(
            matches!(cb.0.last(), Some(Statement::Return(Some(e), _))
                if matches!(e.kind(), ExpressionKind::Identifier(id) if id.ident() == EC_RESULT)),
            "the last statement must be `return ec_result`:\n{}",
            show(cb)
        );
    }

    // --- terminality -------------------------------------------------------

    #[test]
    fn term_rules() {
        assert_eq!(term_stmt(&abort()), Term::Always);
        assert_eq!(term_stmt(&ret(1)), Term::Always);
        assert_eq!(term_stmt(&unwrap("x", "m")), Term::Maybe);
        assert_eq!(term_stmt(&invoke("x", "O")), Term::Maybe);
        assert_eq!(term_stmt(&set("x", 1)), Term::Never);
        assert_eq!(
            term_stmt(&ite("c", vec![ret(1)], vec![abort()])),
            Term::Always
        );
        assert_eq!(term_stmt(&ite("c", vec![set("x", 1)], vec![])), Term::Never);
        assert_eq!(term_stmt(&assert_("c")), Term::Maybe);
        // the first `Always` ends the fold; what follows is unreachable
        assert_eq!(
            term_block(&[set("x", 1), abort(), unwrap("y", "m")]),
            Term::Always
        );
        assert_eq!(term_block(&[set("x", 1), unwrap("y", "m")]), Term::Maybe);
        assert_eq!(term_block(&[]), Term::Never);
    }

    // --- the four IfThenElse cases (§3.3) ----------------------------------

    #[test]
    fn if_both_branches_always_drops_the_continuation() {
        let out = lower_int_oracle(vec![
            ite("c", vec![ret(1)], vec![ret(2)]),
            set("dead", 3),
            ret(4),
        ]);
        assert_single_exit(&out);
        assert_eq!(
            show(&out),
            "\
ec_result <- None
if c {
  ec_result <- Some(1)
} else {
  ec_result <- Some(2)
}
return ec_result
"
        );
    }

    #[test]
    fn if_then_always_moves_the_continuation_into_the_else_branch() {
        let out = lower_int_oracle(vec![
            ite("c", vec![ret(1)], vec![set("x", 2)]),
            set("y", 3),
            ret(4),
        ]);
        assert_single_exit(&out);
        assert_eq!(
            show(&out),
            "\
ec_result <- None
if c {
  ec_result <- Some(1)
} else {
  x <- 2
  y <- 3
  ec_result <- Some(4)
}
return ec_result
"
        );
    }

    #[test]
    fn if_then_abort_flips_so_no_branch_is_empty() {
        // `if c { abort }; REST`: the then-branch is left holding only the
        // dropped `ec_done <- true`, so the `if` is flipped instead of being
        // emitted with an empty then-branch.
        let out = lower_int_oracle(vec![ite("c", vec![abort()], vec![]), ret(4)]);
        assert_single_exit(&out);
        assert!(!has_empty_then(&out.0), "{}", show(&out));
        assert_eq!(
            show(&out),
            "\
ec_result <- None
if not c {
  ec_result <- Some(4)
}
return ec_result
"
        );
    }

    #[test]
    fn if_else_always_moves_the_continuation_into_the_then_branch() {
        let out = lower_int_oracle(vec![
            ite("c", vec![set("x", 2)], vec![ret(1)]),
            set("y", 3),
            ret(4),
        ]);
        assert_single_exit(&out);
        assert_eq!(
            show(&out),
            "\
ec_result <- None
if c {
  x <- 2
  y <- 3
  ec_result <- Some(4)
} else {
  ec_result <- Some(1)
}
return ec_result
"
        );
    }

    #[test]
    fn if_neither_always_with_a_possible_exit_guards_the_join_with_the_flag() {
        let out = lower_int_oracle(vec![
            ite("c", vec![unwrap("x", "m")], vec![set("x", 2)]),
            set("y", 3),
            ret(4),
        ]);
        assert_single_exit(&out);
        assert_eq!(
            show(&out),
            "\
ec_result <- None
ec_done <- false
if c {
  if not (m == None) {
    x <- Unwrap(m)
  } else {
    ec_done <- true
  }
} else {
  x <- 2
}
if not ec_done {
  y <- 3
  ec_result <- Some(4)
  ec_done <- true
}
return ec_result
"
        );
    }

    #[test]
    fn if_neither_always_and_nothing_can_exit_leaves_the_rest_in_place() {
        let out = lower_int_oracle(vec![
            ite("c", vec![set("x", 1)], vec![set("x", 2)]),
            set("y", 3),
            ret(4),
        ]);
        assert_eq!(
            show(&out),
            "\
ec_result <- None
if c {
  x <- 1
} else {
  x <- 2
}
y <- 3
ec_result <- Some(4)
return ec_result
"
        );
    }

    // --- assert / unwrap / invoke ------------------------------------------

    #[test]
    fn assert_becomes_one_if_with_the_continuation_inside() {
        let out = lower_int_oracle(vec![assert_("c"), set("x", 1), ret(2)]);
        assert_single_exit(&out);
        assert_eq!(count_ifs(&out.0), 1);
        assert!(!has_empty_then(&out.0), "{}", show(&out));
        assert_eq!(
            show(&out),
            "\
ec_result <- None
if c {
  x <- 1
  ec_result <- Some(2)
}
return ec_result
"
        );
    }

    #[test]
    fn unwrap_guards_the_rest_of_the_block() {
        let out = lower_int_oracle(vec![set("a", 0), unwrap("x", "m"), set("y", 1), ret(2)]);
        assert_single_exit(&out);
        assert_eq!(
            show(&out),
            "\
ec_result <- None
a <- 0
if not (m == None) {
  x <- Unwrap(m)
  y <- 1
  ec_result <- Some(2)
}
return ec_result
"
        );
    }

    #[test]
    fn invoke_binds_a_maybe_temporary_and_guards_the_rest() {
        let bare = Statement::InvokeOracle(InvokeOracle {
            oracle_name: "P".to_string(),
            args: vec![],
            edge: Some(edge("P", Type::empty())),
            file_pos: span(),
        });
        let out = lower_int_oracle(vec![invoke("x", "O"), bare, ret(1)]);
        assert_single_exit(&out);
        assert_eq!(
            show(&out),
            "\
ec_result <- None
ec_r1 <- invoke O()
if not (ec_r1 == None) {
  x <- Unwrap(ec_r1)
  ec_r2 <- invoke P()
  if not (ec_r2 == None) {
    ec_result <- Some(1)
  }
}
return ec_result
"
        );

        // `ec_rN : Maybe(T)` for the callee's original `T`, and the invoke
        // itself now declares — and resolves to — the `Maybe`-typed callee.
        let Statement::Assignment(
            Assignment {
                pattern: Pattern::Ident(r1),
                rhs,
            },
            _,
        ) = &out.0[1]
        else {
            panic!("expected `ec_r1 <- invoke O()`")
        };
        assert_eq!(*r1, var("ec_r1", Type::maybe(Type::integer())));
        let AssignmentRhs::Invoke {
            edge, return_type, ..
        } = rhs
        else {
            panic!("expected an invoke")
        };
        assert_eq!(*return_type, Some(Type::maybe(Type::integer())));
        assert_eq!(
            edge.as_ref().unwrap().sig().ty,
            Type::maybe(Type::integer())
        );
    }

    #[test]
    fn invoke_into_a_table_stores_some_of_the_unwrapped_value() {
        let table = var("T", Type::table(Type::integer(), Type::integer()));
        let stmt = Statement::Assignment(
            Assignment {
                pattern: Pattern::Table {
                    ident: table,
                    index: Expression::integer(0),
                },
                rhs: AssignmentRhs::Invoke {
                    oracle_name: "O".to_string(),
                    args: vec![],
                    edge: Some(edge("O", Type::integer())),
                    return_type: Some(Type::integer()),
                },
            },
            span(),
        );
        let out = lower_int_oracle(vec![stmt, ret(1)]);
        assert!(
            show(&out).contains("T[0] <- Some(Unwrap(ec_r1))"),
            "{}",
            show(&out)
        );
    }

    #[test]
    fn nested_if_under_an_if() {
        // The `Send3` cascade in miniature: a join whose branches hold an
        // inner join, all of it followed by a tail that appears once.
        let out = lower_int_oracle(vec![
            ite(
                "c1",
                vec![
                    unwrap("s", "m"),
                    ite(
                        "c2",
                        vec![set("x", 1)],
                        vec![ite("c3", vec![set("x", 2)], vec![])],
                    ),
                ],
                vec![],
            ),
            set("tail", 9),
            ret(4),
        ]);
        assert_single_exit(&out);
        assert_eq!(
            show(&out),
            "\
ec_result <- None
ec_done <- false
if c1 {
  if not (m == None) {
    s <- Unwrap(m)
    if c2 {
      x <- 1
    } else {
      if c3 {
        x <- 2
      }
    }
  } else {
    ec_done <- true
  }
}
if not ec_done {
  tail <- 9
  ec_result <- Some(4)
  ec_done <- true
}
return ec_result
"
        );
        assert_eq!(show(&out).matches("tail <- 9").count(), 1);
    }

    #[test]
    fn an_oracle_where_nothing_can_exit_is_the_input_plus_the_wrapper() {
        let body = vec![
            set("a", 1),
            ite("c", vec![set("x", 1)], vec![]),
            ite("d", vec![], vec![set("x", 2)]),
            set("b", 2),
        ];
        let mut input = body.clone();
        input.push(ret(3));
        let out = lower_int_oracle(input);

        // statement for statement: `ec_result <- None`, the body, then the
        // lowered `return` and the single exit.
        assert_eq!(out.0.len(), body.len() + 3);
        assert_eq!(&out.0[1..=body.len()], body.as_slice());
        assert_single_exit(&out);
    }

    #[test]
    fn a_valueless_return_is_some_unit() {
        let out = lower_oracle(
            &CodeBlock(vec![Statement::Return(None, span())]),
            &Type::empty(),
            span(),
        )
        .unwrap();
        assert_eq!(
            show(&out),
            "\
ec_result <- None
ec_result <- Some(())
return ec_result
"
        );
        assert_eq!(
            out.0[0],
            assign(
                Pattern::Ident(var(EC_RESULT, Type::maybe(Type::empty()))),
                Expression::from_kind(ExpressionKind::None(Type::empty())),
                span()
            )
        );
    }

    #[test]
    fn a_surviving_for_loop_is_a_hard_error_with_its_span() {
        let loop_span: SourceSpan = (7, 3).into();
        let err = lower_oracle(
            &CodeBlock(vec![
                Statement::For(
                    int_var("i"),
                    Expression::integer(0),
                    Expression::integer(1),
                    CodeBlock(vec![]),
                    loop_span,
                ),
                ret(1),
            ]),
            &Type::integer(),
            span(),
        )
        .unwrap_err();
        assert_eq!(err, UnsupportedLoopError { span: loop_span });
    }

    // --- whole compositions: signatures travel -----------------------------

    fn oracle(name: &str, ty: Type, code: Vec<Statement>) -> OracleDef {
        OracleDef {
            sig: callee_sig(name, ty),
            code: CodeBlock(code),
            file_pos: span(),
        }
    }

    fn package_instance(
        name: &str,
        oracles: Vec<OracleDef>,
        imports: Vec<OracleSig>,
    ) -> PackageInstance {
        PackageInstance {
            name: name.to_lowercase(),
            params: vec![],
            types: vec![],
            pkg: Package {
                name: name.to_string(),
                types: vec![],
                params: vec![],
                state: vec![],
                oracles,
                imports: imports.into_iter().map(|s| (s, span())).collect(),
                invariants: vec![],
                file_name: format!("{name}.pkg.ssp"),
                file_contents: String::new(),
            },
        }
    }

    /// `Caller.Run() -> Integer` invokes `Callee.Get() -> Maybe(Integer)`.
    fn two_package_composition() -> Composition {
        let callee_ty = Type::maybe(Type::integer());
        let get = oracle(
            "Get",
            callee_ty.clone(),
            vec![Statement::Return(
                Some(Expression::from_kind(ExpressionKind::None(Type::integer()))),
                span(),
            )],
        );
        let get_edge = Edge::new(0, 1, get.sig.clone(), None);
        let run = oracle(
            "Run",
            Type::integer(),
            vec![
                Statement::Assignment(
                    Assignment {
                        pattern: Pattern::Ident(var("r", callee_ty.clone())),
                        rhs: AssignmentRhs::Invoke {
                            oracle_name: "Get".to_string(),
                            args: vec![],
                            edge: Some(get_edge.clone()),
                            return_type: Some(callee_ty.clone()),
                        },
                    },
                    span(),
                ),
                ret(1),
            ],
        );
        Composition {
            pkgs: vec![
                package_instance("Caller", vec![run.clone()], vec![get.sig.clone()]),
                package_instance("Callee", vec![get], vec![]),
            ],
            edges: vec![get_edge],
            exports: vec![Export::new(0, run.sig, None)],
            name: "Comp".to_string(),
            consts: vec![],
            invariants: vec![],
        }
    }

    #[test]
    fn signatures_are_rewritten_everywhere_together() {
        let comp = two_package_composition();
        let (out, ()) = Transformation(&comp).transform().unwrap();

        let maybe_int = Type::maybe(Type::integer());
        let maybe_maybe_int = Type::maybe(maybe_int.clone());

        assert_eq!(out.pkgs[0].pkg.oracles[0].sig.ty, maybe_int);
        // an oracle already returning `Maybe(T)` becomes `Maybe(Maybe(T))`:
        // the outer option is abort, the inner the value.
        assert_eq!(out.pkgs[1].pkg.oracles[0].sig.ty, maybe_maybe_int);
        assert_eq!(out.pkgs[0].pkg.imports[0].0.ty, maybe_maybe_int);
        assert_eq!(out.edges[0].sig().ty, maybe_maybe_int);
        assert_eq!(out.exports[0].sig().ty, maybe_int);

        // the caller's temporary and its embedded edge agree with the callee
        let Statement::Assignment(
            Assignment {
                pattern: Pattern::Ident(r1),
                rhs,
            },
            _,
        ) = &out.pkgs[0].pkg.oracles[0].code.0[1]
        else {
            panic!("expected `ec_r1 <- invoke Get()`")
        };
        assert_eq!(r1.get_type(), maybe_maybe_int);
        let AssignmentRhs::Invoke { edge, .. } = rhs else {
            panic!("expected an invoke")
        };
        assert_eq!(edge.as_ref().unwrap().sig().ty, maybe_maybe_int);

        // and `Get`'s body returns `Some(None)`
        let get_body = show(&out.pkgs[1].pkg.oracles[0].code);
        assert!(get_body.contains("ec_result <- Some(None)"), "{get_body}");
    }

    #[test]
    fn running_the_transform_twice_does_not_panic() {
        let comp = two_package_composition();
        let (once, ()) = Transformation(&comp).transform().unwrap();
        let (twice, ()) = Transformation(&once).transform().unwrap();
        for inst in &twice.pkgs {
            for oracle in &inst.pkg.oracles {
                assert_single_exit(&oracle.code);
            }
        }
    }

    /// §3.1 over real projects, through the whole [`EasyCryptTransform`]
    /// pipeline: every oracle body has no `Abort` and one trailing
    /// `return ec_result`, and every copy of every signature is `Maybe`-typed
    /// and agrees with the callee's own definition.
    ///
    /// [`EasyCryptTransform`]: crate::transforms::theorem_transforms::EasyCryptTransform
    #[test]
    fn every_oracle_of_every_example_satisfies_the_contract() {
        use crate::project::{DirectoryFiles, DirectoryProject, Project as _};
        use crate::transforms::theorem_transforms::EasyCryptTransform;
        use crate::transforms::TheoremTransform as _;

        fn check_invokes(stmts: &[Statement], comp: &Composition) {
            for s in stmts {
                match s {
                    Statement::Assignment(
                        Assignment {
                            pattern,
                            rhs:
                                AssignmentRhs::Invoke {
                                    edge, return_type, ..
                                },
                        },
                        _,
                    ) => {
                        let edge = edge.as_ref().expect("resolved");
                        let callee = comp.pkgs[edge.to()]
                            .pkg
                            .oracles
                            .iter()
                            .find(|o| o.sig.name == edge.sig().name)
                            .expect("callee exists");
                        assert_eq!(
                            edge.sig(),
                            &callee.sig,
                            "embedded edge disagrees with callee"
                        );
                        assert!(comp.edges.contains(edge), "embedded edge not in comp.edges");
                        assert_eq!(return_type.as_ref(), Some(&callee.sig.ty));
                        let Pattern::Ident(temp) = pattern else {
                            panic!("an invoke must bind an ec_r<N> temporary")
                        };
                        assert!(is_generated_name(&temp.ident()), "{temp:?}");
                        assert_eq!(temp.get_type(), callee.sig.ty);
                    }
                    Statement::InvokeOracle(_) => panic!("a bare invoke survived easycryptify"),
                    Statement::IfThenElse(ite) => {
                        check_invokes(&ite.then_block.0, comp);
                        check_invokes(&ite.else_block.0, comp);
                    }
                    _ => {}
                }
            }
        }

        let projects: &[(&str, &[&str])] = &[
            ("example-projects/hello-world", &["Proof"]),
            ("example-projects/simple-KEM-example", &["KEM_Proof"]),
            (
                "example-projects/kem-dem/kem-dem-cca-ssp",
                &["kem_dem_cca_ssp"],
            ),
            ("example-projects/4WHS", &["Simple4WHS", "Full4WHS"]),
            ("test-projects/test-splitinvoke", &["SplitInvokeProof"]),
            ("test-projects/test-loopunroll", &["Eq"]),
        ];
        let mut oracles_checked = 0;
        for (dir, theorems) in projects {
            let files = DirectoryFiles::load(std::path::Path::new(dir)).unwrap();
            let project = DirectoryProject::load(std::path::PathBuf::from(dir), &files).unwrap();
            for name in *theorems {
                let theorem = project.get_theorem(name).unwrap();
                let (theorem, _) = EasyCryptTransform.transform_theorem(theorem).unwrap();
                for gi in &theorem.instances {
                    let comp = gi.game();
                    for edge in &comp.edges {
                        assert!(matches!(edge.sig().ty.kind(), TypeKind::Maybe(_)));
                    }
                    for export in &comp.exports {
                        let def = &comp.pkgs[export.to()]
                            .pkg
                            .oracles
                            .iter()
                            .find(|o| o.sig.name == export.sig().name)
                            .unwrap()
                            .sig;
                        assert_eq!(export.sig(), def, "export disagrees with its oracle");
                    }
                    for inst in &comp.pkgs {
                        for (sig, _) in &inst.pkg.imports {
                            assert!(matches!(sig.ty.kind(), TypeKind::Maybe(_)));
                        }
                        for oracle in &inst.pkg.oracles {
                            assert!(matches!(oracle.sig.ty.kind(), TypeKind::Maybe(_)));
                            assert_single_exit(&oracle.code);
                            check_invokes(&oracle.code.0, comp);
                            oracles_checked += 1;
                        }
                    }
                }
            }
        }
        assert!(
            oracles_checked > 100,
            "only {oracles_checked} oracles checked"
        );
    }

    #[test]
    fn generated_names_are_recognised() {
        assert!(is_generated_name("ec_result"));
        assert!(is_generated_name("ec_done"));
        assert!(is_generated_name("ec_r1"));
        assert!(is_generated_name("ec_r12"));
        assert!(!is_generated_name("ec_r"));
        assert!(!is_generated_name("ec_rx"));
        assert!(!is_generated_name("ec_foo"));
        assert!(!is_generated_name("result"));
    }
}
