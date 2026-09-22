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
//! Before lowering, [`guard_unwraps`] removes the `unwrap-N` temporaries
//! `unwrapify` leaves behind, along with any guard that an enclosing guard
//! for the same operand already covers
//! (`docs/stories/easycrypt/17-unwrap-temporaries.md`). Every unwrap that is
//! kept still aborts at exactly the point `unwrapify` bound it.
//!
//! It runs last in [`crate::transforms::theorem_transforms::EasyCryptTransform`],
//! after `tableinitialize`, which pattern-matches on `T[k] <- invoke …` — a
//! shape this transform rewrites.

use std::collections::{BTreeMap, BTreeSet};

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

/// A surviving `unwrap` temporary would be named after its operand
/// (`sid_v` for `Unwrap(sid)`, story 17 §3.4), but that name is already an
/// identifier of the same oracle or package. Consistent with the exporter's
/// naming rule, this is a hard error rather than a silent rename.
#[derive(Debug, Clone, PartialEq, Eq, Error, Diagnostic)]
#[error(
    "the temporary `{name}` this unwrap needs in EasyCrypt collides with an existing identifier \
     of the same name"
)]
pub struct TemporaryNameCollision {
    pub name: String,
    #[label("this unwrap's value is kept in `{name}`")]
    pub span: SourceSpan,
}

/// Everything [`Transformation`] can reject.
#[derive(Debug, Clone, PartialEq, Eq, Error, Diagnostic)]
pub enum EasyCryptifyError {
    #[error(transparent)]
    #[diagnostic(transparent)]
    UnsupportedLoop(#[from] UnsupportedLoopError),

    #[error(transparent)]
    #[diagnostic(transparent)]
    TemporaryNameCollision(#[from] TemporaryNameCollision),
}

pub struct Transformation<'a>(pub &'a Composition);

impl super::Transformation for Transformation<'_> {
    type Err = EasyCryptifyError;
    type Aux = ();

    fn transform(&self) -> Result<(Composition, ()), EasyCryptifyError> {
        let mut comp = self.0.clone();
        for inst in &mut comp.pkgs {
            // Names a derived temporary may not take besides the ones the
            // body itself mentions: every parameter and state field of the
            // package, which become module variables in EasyCrypt.
            let package_names: BTreeSet<String> = (inst.pkg.params.iter())
                .chain(&inst.pkg.state)
                .map(|(name, _, _)| name.clone())
                .collect();
            for oracle in &mut inst.pkg.oracles {
                let mut reserved = package_names.clone();
                reserved.extend(oracle.sig.args.iter().map(|(name, _)| name.clone()));
                oracle.code =
                    lower_oracle(&oracle.code, &oracle.sig.ty, oracle.file_pos, &reserved)?;
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

/// "Can this terminate the oracle?", computed on the statements
/// [`guard_unwraps`] hands to the lowering.
///
/// An `Unwrap` is `Never` here: by then every unwrap's abort has been made
/// explicit as an `assert`-shaped guard (`if (not (e == None)) {} else
/// { abort }`, which is `Maybe`) at the position `unwrapify` bound it, and
/// the `Unwrap` itself only names the value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Term {
    Never,
    Maybe,
    Always,
}

fn term_stmt(stmt: &Statement) -> Term {
    match stmt {
        Statement::Abort(_) | Statement::Return(_, _) => Term::Always,
        Statement::Assignment(Assignment { rhs, .. }, _) => match rhs {
            AssignmentRhs::Invoke { .. } => Term::Maybe,
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
///
/// The body first goes through [`guard_unwraps`] (story 17), which decides
/// where an `Unwrap` needs a guard and which `unwrap-N` temporaries can go.
/// `reserved` holds the names, besides the body's own identifiers, that a
/// surviving temporary may not be renamed to.
fn lower_oracle(
    code: &CodeBlock,
    ret_ty: &Type,
    oracle_span: SourceSpan,
    reserved: &BTreeSet<String>,
) -> Result<CodeBlock, EasyCryptifyError> {
    let body = guard_unwraps(&code.0, reserved)?;
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
    let (body, _) = lowerer.lower(&body)?;
    out.extend(body);
    out.push(Statement::Return(
        Some(lowerer.ec_result.clone().into()),
        oracle_span,
    ));

    if !contains_done_guard(&out, &lowerer.ec_done) {
        out = drop_done(out, &lowerer.ec_done);
    }
    // Story 17 §3.3: a dropped guard is only ever one that a guard for the
    // same operand already dominates *structurally*. Every `Unwrap(e)` left
    // in the body must therefore sit inside the then-branch of an
    // `if (not (e == None))`.
    debug_assert!(
        every_unwrap_is_guarded(&out),
        "easycryptify left an `Unwrap` outside every guard for its operand: {out:#?}"
    );
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

                // An `Unwrap` needs no case of its own: `guard_unwraps` has
                // already put its guard in front of it as an `assert`
                // (handled by the `IfThenElse` arm below), so what is left
                // is a plain assignment the writer renders as `oget e`.
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
// Unwrap guards and temporaries (story 17)
// ---------------------------------------------------------------------------
//
// `unwrapify` binds every `Unwrap(e)` to a fresh `unwrap-N <- Unwrap(e)`
// right before the statement using it, with no deduplication. Such a binding
// does two things: it *aborts* when `e` is `None` — a control effect at that
// exact point — and it *names* a value. The abort stays where it is, as a
// guard; only the name may go.
//
// `guard_unwraps` runs before the lowering (story 17 §3.5) and makes every
// unwrap's abort explicit as an `assert`-shaped `if (not (e == None)) {}
// else { abort }` at the binding's position — exactly what the lowering then
// turns into story 16's guard. Three rules decide what else is kept:
//
// 1. the temporary is deleted and its uses become `Unwrap(e)`, provided
//    nothing `e` reads is written between the binding and a use (§3.1/§3.2);
// 2. a guard for an `e` that an earlier guard already covers — structurally
//    enclosing, with no write to what `e` reads in between — is dropped
//    (§3.3);
// 3. a temporary stays when rule 1's check fails or `e` is large, named
//    after `e` where that is unambiguous (§3.4).
//
// Rules 1 and 2 only ever *delete*: no guard is moved or created.

/// Prefix of the `unwrap-<N>` temporaries `unwrapify` binds every `Unwrap`
/// to.
const UNWRAP_TEMP_PREFIX: &str = "unwrap-";

/// Suffix of a surviving temporary named after its operand: `sid_v` holds
/// `Unwrap(sid)`.
pub const DERIVED_TEMP_SUFFIX: &str = "_v";

/// Story 17 §3.4: an unwrapped operand of more than this many expression
/// nodes ([`expr_size`]) keeps its temporary. Every operand in the example
/// projects is a variable (1 node) or a table read (2, or 4 when its index
/// is itself an inlined unwrap), so this only fires on genuinely large
/// operands such as a table read at a 5-tuple key.
pub const MAX_INLINED_UNWRAP_SIZE: usize = 6;

fn is_unwrap_temp(id: &Identifier) -> bool {
    matches!(id, Identifier::Generated(name, _)
        if name
            .strip_prefix(UNWRAP_TEMP_PREFIX)
            .is_some_and(|n| !n.is_empty() && n.chars().all(|c| c.is_ascii_digit())))
}

/// A temporary rule 3 keeps.
struct Survivor {
    temp: Identifier,
    operand: Expression,
    span: SourceSpan,
}

#[derive(Default)]
struct UnwrapGuards {
    /// `unwrap-N` → `Unwrap(e)` for every temporary being inlined, while the
    /// rest of the block that binds it is walked.
    inlined: BTreeMap<String, Expression>,
    survivors: Vec<Survivor>,
}

/// Story 17's pass over one oracle body; see the section comment above.
fn guard_unwraps(
    stmts: &[Statement],
    reserved: &BTreeSet<String>,
) -> Result<Vec<Statement>, TemporaryNameCollision> {
    let mut pass = UnwrapGuards::default();
    let out = pass.block(stmts, Vec::new());
    let mut taken = reserved.clone();
    collect_block_names(stmts, &mut taken);
    let renames = pass.name_survivors(&taken)?;
    Ok(if renames.is_empty() {
        out
    } else {
        rename_block(&out, &renames)
    })
}

impl UnwrapGuards {
    /// `facts` are the operands known to be `Some` on entry: a guard for each
    /// structurally encloses this block, and nothing they read has been
    /// written since. A fact never leaves the block that established it, so
    /// a guard in one branch of an `if` never covers the other branch or the
    /// code after the `if` (§4, sibling branches).
    fn block(&mut self, stmts: &[Statement], mut facts: Vec<Expression>) -> Vec<Statement> {
        let mut inlined_here = Vec::new();
        let mut out = Vec::new();
        for (i, stmt) in stmts.iter().enumerate() {
            match self.substitute(stmt) {
                Statement::Assignment(
                    Assignment {
                        pattern,
                        rhs: AssignmentRhs::Expression(value),
                    },
                    span,
                ) if matches!(value.kind(), ExpressionKind::Unwrap(_)) => {
                    let ExpressionKind::Unwrap(operand) = value.kind() else {
                        unreachable!()
                    };
                    let operand = (**operand).clone();

                    // Rule 2: the guard is only emitted if no enclosing guard
                    // for the same operand already covers this point.
                    if !facts.contains(&operand) {
                        out.push(assert_some(&operand, span));
                        facts.push(operand.clone());
                    }

                    let temp = match &pattern {
                        Pattern::Ident(id) if is_unwrap_temp(id) => Some(id.clone()),
                        _ => None,
                    };
                    match temp {
                        // Rule 1: inline the value, drop the binding.
                        Some(temp)
                            if expr_size(&operand) <= MAX_INLINED_UNWRAP_SIZE
                                && inlining_is_sound(&temp.ident(), &operand, &stmts[i + 1..]) =>
                        {
                            inlined_here.push(temp.ident());
                            self.inlined.insert(temp.ident(), value);
                        }
                        // Rule 3 (or a binding that was never a temporary).
                        temp => {
                            if let Some(temp) = temp {
                                self.survivors.push(Survivor {
                                    temp,
                                    operand,
                                    span,
                                });
                            }
                            kill(&mut facts, &pattern_writes(&pattern));
                            out.push(Statement::Assignment(
                                Assignment {
                                    pattern,
                                    rhs: AssignmentRhs::Expression(value),
                                },
                                span,
                            ));
                        }
                    }
                }

                Statement::IfThenElse(ite) => {
                    let then = self.block(&ite.then_block.0, facts.clone());
                    let els = self.block(&ite.else_block.0, facts.clone());
                    let mut written = block_writes(&ite.then_block.0);
                    written.extend(block_writes(&ite.else_block.0));
                    kill(&mut facts, &written);
                    out.push(Statement::IfThenElse(IfThenElse {
                        then_block: CodeBlock(then),
                        else_block: CodeBlock(els),
                        ..ite
                    }));
                }

                Statement::For(id, lo, hi, body, span) => {
                    // A fact must hold on every iteration, so whatever the
                    // body writes is killed before it is walked.
                    let mut written = block_writes(&body.0);
                    written.push(id.ident());
                    kill(&mut facts, &written);
                    let body = CodeBlock(self.block(&body.0, facts.clone()));
                    out.push(Statement::For(id, lo, hi, body, span));
                }

                other => {
                    // An `invoke` writes only the local it binds: the callee
                    // is another package, and packages share no state
                    // (story 17 §2.2).
                    kill(&mut facts, &stmt_writes(&other));
                    out.push(other);
                }
            }
        }
        for temp in inlined_here {
            self.inlined.remove(&temp);
        }
        out
    }

    /// `stmt` with the inlined temporaries substituted into its own
    /// expressions (its nested blocks are substituted as they are walked).
    fn substitute(&self, stmt: &Statement) -> Statement {
        if self.inlined.is_empty() {
            return stmt.clone();
        }
        let inlined = &self.inlined;
        map_own_exprs(stmt, &|e| substitute_expr(e, inlined))
    }

    /// Rule 3's naming: `x_v` for a survivor of `Unwrap(x)` where `x` is a
    /// plain identifier and no other survivor derives the same name; its
    /// `unwrap-N` name otherwise. A derived name already taken by an
    /// identifier of the oracle or its package is a hard error.
    fn name_survivors(
        &self,
        taken: &BTreeSet<String>,
    ) -> Result<BTreeMap<String, Identifier>, TemporaryNameCollision> {
        let derived: Vec<Option<String>> = self
            .survivors
            .iter()
            .map(|s| match s.operand.kind() {
                ExpressionKind::Identifier(id) if !is_unwrap_temp(id) => {
                    Some(format!("{}{DERIVED_TEMP_SUFFIX}", id.ident()))
                }
                _ => None,
            })
            .collect();
        let mut counts: BTreeMap<&str, usize> = BTreeMap::new();
        for name in derived.iter().flatten() {
            *counts.entry(name).or_default() += 1;
        }

        let mut renames = BTreeMap::new();
        for (survivor, name) in self.survivors.iter().zip(&derived) {
            let Some(name) = name else { continue };
            if counts[name.as_str()] > 1 {
                continue;
            }
            if taken.contains(name) {
                return Err(TemporaryNameCollision {
                    name: name.clone(),
                    span: survivor.span,
                });
            }
            renames.insert(
                survivor.temp.ident(),
                Identifier::Generated(name.clone(), survivor.temp.get_type()),
            );
        }
        Ok(renames)
    }
}

/// `if (not (e == None)) {} else { abort }` — the parser's desugaring of
/// `assert (not (e == None))`, which the lowering turns into story 16's
/// unwrap guard with the continuation moved into its then-branch.
fn assert_some(operand: &Expression, span: SourceSpan) -> Statement {
    if_then_else(is_some(operand), vec![], vec![Statement::Abort(span)], span)
}

/// Rule 1's check (§3.2): no use of `temp` in `rest` is reached after a
/// write to anything `operand` reads. A table write counts as a write to the
/// whole table.
fn inlining_is_sound(temp: &str, operand: &Expression, rest: &[Statement]) -> bool {
    fn walk(
        stmts: &[Statement],
        temp: &str,
        reads: &BTreeSet<String>,
        invalidated: &mut bool,
    ) -> bool {
        for stmt in stmts {
            // A statement's own expressions are evaluated before it writes.
            if *invalidated && own_exprs(stmt).iter().any(|e| mentions(e, temp)) {
                return false;
            }
            match stmt {
                Statement::IfThenElse(ite) => {
                    let (mut then_inv, mut else_inv) = (*invalidated, *invalidated);
                    if !walk(&ite.then_block.0, temp, reads, &mut then_inv)
                        || !walk(&ite.else_block.0, temp, reads, &mut else_inv)
                    {
                        return false;
                    }
                    *invalidated = then_inv || else_inv;
                }
                Statement::For(..) => {
                    // A later iteration sees an earlier one's writes.
                    let writes = stmt_writes(stmt).iter().any(|w| reads.contains(w));
                    if (*invalidated || writes) && block_mentions(std::slice::from_ref(stmt), temp)
                    {
                        return false;
                    }
                    *invalidated |= writes;
                }
                other => {
                    if stmt_writes(other).iter().any(|w| reads.contains(w)) {
                        *invalidated = true;
                    }
                }
            }
        }
        true
    }
    walk(rest, temp, &expr_reads(operand), &mut false)
}

fn kill(facts: &mut Vec<Expression>, written: &[String]) {
    if written.is_empty() {
        return;
    }
    facts.retain(|fact| {
        let reads = expr_reads(fact);
        !written.iter().any(|w| reads.contains(w))
    });
}

/// The direct subexpressions of `e`.
fn children(e: &Expression) -> Vec<&Expression> {
    match e.kind() {
        ExpressionKind::Bot
        | ExpressionKind::Sample(_)
        | ExpressionKind::StringLiteral(_)
        | ExpressionKind::IntegerLiteral(_)
        | ExpressionKind::BooleanLiteral(_)
        | ExpressionKind::BitsLiteral(..)
        | ExpressionKind::Identifier(_)
        | ExpressionKind::EmptyTable(_)
        | ExpressionKind::None(_) => vec![],
        ExpressionKind::TableAccess(_, e)
        | ExpressionKind::Some(e)
        | ExpressionKind::Unwrap(e)
        | ExpressionKind::Not(e)
        | ExpressionKind::Neg(e)
        | ExpressionKind::Inv(e)
        | ExpressionKind::Sum(e)
        | ExpressionKind::Prod(e)
        | ExpressionKind::Any(e)
        | ExpressionKind::All(e)
        | ExpressionKind::Union(e)
        | ExpressionKind::Cut(e)
        | ExpressionKind::SetDiff(e) => vec![e],
        ExpressionKind::Tuple(es)
        | ExpressionKind::List(es)
        | ExpressionKind::Set(es)
        | ExpressionKind::FnCall(_, es)
        | ExpressionKind::Equals(es)
        | ExpressionKind::And(es)
        | ExpressionKind::Or(es)
        | ExpressionKind::Xor(es)
        | ExpressionKind::Concat(es) => es.iter().collect(),
        ExpressionKind::Add(a, b)
        | ExpressionKind::Sub(a, b)
        | ExpressionKind::Mul(a, b)
        | ExpressionKind::Div(a, b)
        | ExpressionKind::Pow(a, b)
        | ExpressionKind::Mod(a, b)
        | ExpressionKind::LessThen(a, b)
        | ExpressionKind::GreaterThen(a, b)
        | ExpressionKind::LessThenEq(a, b)
        | ExpressionKind::GreaterThenEq(a, b) => vec![a, b],
    }
}

/// The number of expression nodes in `e` — the syntactic size of §3.4.
fn expr_size(e: &Expression) -> usize {
    1 + children(e).into_iter().map(expr_size).sum::<usize>()
}

/// The names of every variable, table and function `e` reads.
fn expr_reads(e: &Expression) -> BTreeSet<String> {
    fn go(e: &Expression, out: &mut BTreeSet<String>) {
        match e.kind() {
            ExpressionKind::Identifier(id)
            | ExpressionKind::TableAccess(id, _)
            | ExpressionKind::FnCall(id, _) => {
                out.insert(id.ident());
            }
            _ => {}
        }
        for child in children(e) {
            go(child, out);
        }
    }
    let mut out = BTreeSet::new();
    go(e, &mut out);
    out
}

fn mentions(e: &Expression, name: &str) -> bool {
    matches!(e.kind(), ExpressionKind::Identifier(id) if id.ident() == name)
        || children(e).into_iter().any(|c| mentions(c, name))
}

fn block_mentions(stmts: &[Statement], name: &str) -> bool {
    stmts.iter().any(|stmt| {
        own_exprs(stmt).iter().any(|e| mentions(e, name))
            || match stmt {
                Statement::IfThenElse(ite) => {
                    block_mentions(&ite.then_block.0, name)
                        || block_mentions(&ite.else_block.0, name)
                }
                Statement::For(_, _, _, body, _) => block_mentions(&body.0, name),
                _ => false,
            }
    })
}

/// A statement's own expressions, not those of its nested blocks.
fn own_exprs(stmt: &Statement) -> Vec<&Expression> {
    match stmt {
        Statement::Abort(_) | Statement::Return(None, _) => vec![],
        Statement::Return(Some(e), _) => vec![e],
        Statement::Assignment(Assignment { pattern, rhs }, _) => {
            let mut out = match pattern {
                Pattern::Table { index, .. } => vec![index],
                Pattern::Ident(_) | Pattern::Tuple(_) => vec![],
            };
            match rhs {
                AssignmentRhs::Expression(e) => out.push(e),
                AssignmentRhs::Invoke { args, .. } => out.extend(args),
                AssignmentRhs::Sample { .. } => {}
            }
            out
        }
        Statement::InvokeOracle(InvokeOracle { args, .. }) => args.iter().collect(),
        Statement::IfThenElse(ite) => vec![&ite.cond],
        Statement::For(_, lo, hi, _, _) => vec![lo, hi],
    }
}

/// `stmt` with `f` applied to its own expressions (see [`own_exprs`]).
fn map_own_exprs(stmt: &Statement, f: &impl Fn(&Expression) -> Expression) -> Statement {
    match stmt {
        Statement::Abort(_) => stmt.clone(),
        Statement::Return(value, span) => Statement::Return(value.as_ref().map(f), *span),
        Statement::Assignment(Assignment { pattern, rhs }, span) => {
            let pattern = match pattern {
                Pattern::Table { ident, index } => Pattern::Table {
                    ident: ident.clone(),
                    index: f(index),
                },
                other => other.clone(),
            };
            let rhs = match rhs {
                AssignmentRhs::Expression(e) => AssignmentRhs::Expression(f(e)),
                AssignmentRhs::Invoke {
                    oracle_name,
                    args,
                    edge,
                    return_type,
                } => AssignmentRhs::Invoke {
                    oracle_name: oracle_name.clone(),
                    args: args.iter().map(f).collect(),
                    edge: edge.clone(),
                    return_type: return_type.clone(),
                },
                sample @ AssignmentRhs::Sample { .. } => sample.clone(),
            };
            Statement::Assignment(Assignment { pattern, rhs }, *span)
        }
        Statement::InvokeOracle(inv) => Statement::InvokeOracle(InvokeOracle {
            args: inv.args.iter().map(f).collect(),
            ..inv.clone()
        }),
        Statement::IfThenElse(ite) => Statement::IfThenElse(IfThenElse {
            cond: f(&ite.cond),
            ..ite.clone()
        }),
        Statement::For(id, lo, hi, body, span) => {
            Statement::For(id.clone(), f(lo), f(hi), body.clone(), *span)
        }
    }
}

/// `e` with every `Generated` identifier named in `map` replaced by its
/// image.
fn substitute_expr(e: &Expression, map: &BTreeMap<String, Expression>) -> Expression {
    e.mapfold((), |(), e| match e.kind() {
        ExpressionKind::Identifier(Identifier::Generated(name, _)) if map.contains_key(name) => {
            ((), map[name].clone())
        }
        _ => ((), e),
    })
    .1
}

fn pattern_writes(pattern: &Pattern) -> Vec<String> {
    match pattern {
        Pattern::Ident(id) | Pattern::Table { ident: id, .. } => vec![id.ident()],
        Pattern::Tuple(ids) => ids.iter().map(Identifier::ident).collect(),
    }
}

/// Everything `stmt` may write, including in its nested blocks.
fn stmt_writes(stmt: &Statement) -> Vec<String> {
    match stmt {
        Statement::Abort(_) | Statement::Return(..) | Statement::InvokeOracle(_) => vec![],
        Statement::Assignment(Assignment { pattern, .. }, _) => pattern_writes(pattern),
        Statement::IfThenElse(ite) => {
            let mut out = block_writes(&ite.then_block.0);
            out.extend(block_writes(&ite.else_block.0));
            out
        }
        Statement::For(id, _, _, body, _) => {
            let mut out = block_writes(&body.0);
            out.push(id.ident());
            out
        }
    }
}

fn block_writes(stmts: &[Statement]) -> Vec<String> {
    stmts.iter().flat_map(stmt_writes).collect()
}

/// Every identifier name `stmts` mentions, written or read.
fn collect_block_names(stmts: &[Statement], out: &mut BTreeSet<String>) {
    for stmt in stmts {
        out.extend(stmt_writes(stmt));
        for e in own_exprs(stmt) {
            out.extend(expr_reads(e));
        }
        match stmt {
            Statement::IfThenElse(ite) => {
                collect_block_names(&ite.then_block.0, out);
                collect_block_names(&ite.else_block.0, out);
            }
            Statement::For(_, _, _, body, _) => collect_block_names(&body.0, out),
            _ => {}
        }
    }
}

/// Renames surviving temporaries (rule 3) throughout `stmts`.
fn rename_block(stmts: &[Statement], renames: &BTreeMap<String, Identifier>) -> Vec<Statement> {
    let images: BTreeMap<String, Expression> = renames
        .iter()
        .map(|(old, new)| (old.clone(), new.clone().into()))
        .collect();
    let rename = |id: &Identifier| renames.get(&id.ident()).cloned().unwrap_or(id.clone());
    stmts
        .iter()
        .map(
            |stmt| match map_own_exprs(stmt, &|e| substitute_expr(e, &images)) {
                Statement::Assignment(Assignment { pattern, rhs }, span) => {
                    let pattern = match pattern {
                        Pattern::Ident(id) => Pattern::Ident(rename(&id)),
                        Pattern::Tuple(ids) => Pattern::Tuple(ids.iter().map(rename).collect()),
                        table @ Pattern::Table { .. } => table,
                    };
                    Statement::Assignment(Assignment { pattern, rhs }, span)
                }
                Statement::IfThenElse(ite) => Statement::IfThenElse(IfThenElse {
                    then_block: CodeBlock(rename_block(&ite.then_block.0, renames)),
                    else_block: CodeBlock(rename_block(&ite.else_block.0, renames)),
                    ..ite
                }),
                Statement::For(id, lo, hi, body, span) => {
                    Statement::For(id, lo, hi, CodeBlock(rename_block(&body.0, renames)), span)
                }
                other => other,
            },
        )
        .collect()
}

/// The containment story 17 §3.3 asks to be asserted: every `Unwrap(e)` —
/// in a condition, an assignment, an argument or a table index — lies inside
/// the then-branch of an `if (not (e == None))`.
fn every_unwrap_is_guarded(stmts: &[Statement]) -> bool {
    fn guarded_operand(cond: &Expression) -> Option<&Expression> {
        let ExpressionKind::Not(inner) = cond.kind() else {
            return None;
        };
        match inner.kind() {
            ExpressionKind::Equals(es)
                if es.len() == 2 && matches!(es[1].kind(), ExpressionKind::None(_)) =>
            {
                Some(&es[0])
            }
            _ => None,
        }
    }
    fn expr_ok(e: &Expression, guards: &[&Expression]) -> bool {
        let here = match e.kind() {
            ExpressionKind::Unwrap(inner) => guards.contains(&&**inner),
            _ => true,
        };
        here && children(e).into_iter().all(|c| expr_ok(c, guards))
    }
    fn walk<'a>(stmts: &'a [Statement], guards: &mut Vec<&'a Expression>) -> bool {
        stmts.iter().all(|stmt| {
            own_exprs(stmt).iter().all(|e| expr_ok(e, guards))
                && match stmt {
                    Statement::IfThenElse(ite) => {
                        let guard = guarded_operand(&ite.cond);
                        guards.extend(guard);
                        let then_ok = walk(&ite.then_block.0, guards);
                        if guard.is_some() {
                            guards.pop();
                        }
                        then_ok && walk(&ite.else_block.0, guards)
                    }
                    Statement::For(_, _, _, body, _) => walk(&body.0, guards),
                    _ => true,
                }
        })
    }
    walk(stmts, &mut Vec::new())
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
        lower_oracle(&CodeBlock(body), &Type::integer(), span(), &BTreeSet::new()).unwrap()
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
        // an unwrap's abort is `guard_unwraps`'s assert by the time `Term`
        // is asked, so the unwrap itself only names a value
        assert_eq!(term_stmt(&unwrap("x", "m")), Term::Never);
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
        assert_eq!(term_block(&[set("x", 1), assert_("c")]), Term::Maybe);
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
            &BTreeSet::new(),
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
            &BTreeSet::new(),
        )
        .unwrap_err();
        assert_eq!(
            err,
            EasyCryptifyError::UnsupportedLoop(UnsupportedLoopError { span: loop_span })
        );
    }

    // --- story 17: unwrap temporaries and their guards ---------------------
    //
    // Inputs here are written in the shape `unwrapify` leaves: every
    // `Unwrap(e)` is hoisted into its own `unwrap-N <- Unwrap(e)` binding,
    // placed immediately before the statement that uses it.

    fn maybe_int(name: &str) -> Expression {
        var(name, Type::maybe(Type::integer())).into()
    }

    fn int_table(name: &str) -> Identifier {
        var(name, Type::table(Type::integer(), Type::integer()))
    }

    /// `T[idx]`, `T : Table(Integer, Integer)`.
    fn get(table: &str, idx: Expression) -> Expression {
        Expression::from_kind(ExpressionKind::TableAccess(int_table(table), Box::new(idx)))
    }

    fn int(name: &str) -> Expression {
        int_var(name).into()
    }

    /// `unwrapify`'s temporary `unwrap-N : Integer`.
    fn tmp(n: usize) -> Expression {
        int_var(&format!("unwrap-{n}")).into()
    }

    /// `unwrap-N <- Unwrap(operand)`.
    fn bind(n: usize, operand: Expression) -> Statement {
        assign(
            Pattern::Ident(int_var(&format!("unwrap-{n}"))),
            Expression::from_kind(ExpressionKind::Unwrap(Box::new(operand))),
            span(),
        )
    }

    fn let_(name: &str, rhs: Expression) -> Statement {
        assign(Pattern::Ident(int_var(name)), rhs, span())
    }

    /// `T[idx] <- Some(value)`.
    fn put(table: &str, idx: Expression, value: Expression) -> Statement {
        assign(
            Pattern::Table {
                ident: int_table(table),
                index: idx,
            },
            Expression::from_kind(ExpressionKind::Some(Box::new(value))),
            span(),
        )
    }

    fn is_none(e: Expression) -> Expression {
        Expression::equals(vec![
            e,
            Expression::from_kind(ExpressionKind::None(Type::integer())),
        ])
    }

    fn ite_e(cond: Expression, then: Vec<Statement>, els: Vec<Statement>) -> Statement {
        if_then_else(cond, then, els, span())
    }

    /// The `if (_mess = 2)` cascade of `KX_nochecks::Send3` (§1.2) in
    /// miniature: four `Unwrap(sid)` sites, the first one unconditional.
    #[test]
    fn send3_cascade_collapses_to_one_guard_and_no_temporaries() {
        let sid = || maybe_int("sid");
        let out = lower_int_oracle(vec![
            bind(2, sid()),
            ite_e(
                is_none(get("First", tmp(2))),
                vec![bind(3, sid()), put("First", tmp(3), int("ctr"))],
                vec![
                    bind(4, sid()),
                    ite_e(
                        is_none(get("Second", tmp(4))),
                        vec![bind(5, sid()), put("Second", tmp(5), int("ctr"))],
                        vec![],
                    ),
                ],
            ),
            ret(1),
        ]);
        assert_single_exit(&out);
        assert_eq!(
            show(&out),
            "\
ec_result <- None
if not (sid == None) {
  if (First[Unwrap(sid)] == None) {
    First[Unwrap(sid)] <- Some(ctr)
  } else {
    if (Second[Unwrap(sid)] == None) {
      Second[Unwrap(sid)] <- Some(ctr)
    }
  }
  ec_result <- Some(1)
}
return ec_result
"
        );
    }

    /// Dropping the dominated guards also removes the join they caused: the
    /// cascade can no longer terminate, so the code after it needs no
    /// `ec_done` guard (the second join of `KX_noprfkey::Send3`).
    #[test]
    fn a_dominated_unwrap_inside_a_branch_causes_no_join() {
        let out = lower_int_oracle(vec![
            bind(1, maybe_int("m")),
            let_("x", tmp(1)),
            ite(
                "c",
                vec![bind(2, maybe_int("m")), let_("y", tmp(2))],
                vec![],
            ),
            set("z", 3),
            ret(1),
        ]);
        assert_single_exit(&out);
        assert_eq!(
            show(&out),
            "\
ec_result <- None
if not (m == None) {
  x <- Unwrap(m)
  if c {
    y <- Unwrap(m)
  }
  z <- 3
  ec_result <- Some(1)
}
return ec_result
"
        );
    }

    /// §3.2, table: any write to `T` invalidates every read of `T[…]`, even
    /// at another index. The temporary whose use comes after the write
    /// survives (its operand is not a plain identifier, so it keeps its
    /// `unwrap-N` name), and the second unwrap keeps its own guard.
    #[test]
    fn a_table_write_between_binding_and_use_keeps_the_temporary_and_both_guards() {
        let tk = || get("T", int("k"));
        let out = lower_int_oracle(vec![
            bind(1, tk()),
            put("T", int("j"), Expression::integer(5)),
            let_("x", tmp(1)),
            bind(2, tk()),
            let_("y", tmp(2)),
            ret(1),
        ]);
        assert_single_exit(&out);
        assert_eq!(
            show(&out),
            "\
ec_result <- None
if not (T[k] == None) {
  unwrap-1 <- Unwrap(T[k])
  T[j] <- Some(5)
  x <- unwrap-1
  if not (T[k] == None) {
    y <- Unwrap(T[k])
    ec_result <- Some(1)
  }
}
return ec_result
"
        );
    }

    /// §3.2, local: reassigning the unwrapped local invalidates it. The
    /// survivor is named after its operand (§3.4).
    #[test]
    fn a_reassigned_local_between_binding_and_use_keeps_the_temporary_and_both_guards() {
        let out = lower_int_oracle(vec![
            bind(1, maybe_int("m")),
            assign(
                Pattern::Ident(var("m", Type::maybe(Type::integer()))),
                Expression::from_kind(ExpressionKind::Some(Box::new(Expression::integer(7)))),
                span(),
            ),
            let_("x", tmp(1)),
            bind(2, maybe_int("m")),
            let_("y", tmp(2)),
            ret(1),
        ]);
        assert_single_exit(&out);
        assert_eq!(
            show(&out),
            "\
ec_result <- None
if not (m == None) {
  m_v <- Unwrap(m)
  m <- Some(7)
  x <- m_v
  if not (m == None) {
    y <- Unwrap(m)
    ec_result <- Some(1)
  }
}
return ec_result
"
        );
    }

    /// §4: two unwraps of the same operand in *sibling* branches. Neither
    /// dominates the other, so each keeps its guard inside its own branch;
    /// hoisting one above the `if` would abort on a path that never
    /// unwrapped. Likewise an unwrap *after* an `if` is not dominated by one
    /// inside it.
    #[test]
    fn unwraps_in_sibling_branches_keep_their_guards_in_place() {
        let out = lower_int_oracle(vec![
            ite(
                "c",
                vec![bind(1, maybe_int("m")), let_("x", tmp(1))],
                vec![bind(2, maybe_int("m")), let_("y", tmp(2))],
            ),
            bind(3, maybe_int("m")),
            let_("z", tmp(3)),
            ret(1),
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
  if not (m == None) {
    y <- Unwrap(m)
  } else {
    ec_done <- true
  }
}
if not ec_done {
  if not (m == None) {
    z <- Unwrap(m)
    ec_result <- Some(1)
    ec_done <- true
  } else {
    ec_done <- true
  }
}
return ec_result
"
        );
    }

    /// §4: an `invoke` between binding and use. The composition graph is a
    /// DAG, an oracle cannot call its own package, and packages share no
    /// state (§2.2) — so the callee cannot write anything the caller's
    /// `m` or `T[k]` reads. Substitution still happens and the second guard
    /// is still dominated. Only the local the invoke *binds* is written.
    #[test]
    fn an_invoke_between_binding_and_use_invalidates_nothing_the_caller_reads() {
        let out = lower_int_oracle(vec![
            bind(1, maybe_int("m")),
            invoke("r", "O"),
            let_("x", tmp(1)),
            bind(2, maybe_int("m")),
            let_("y", tmp(2)),
            ret(1),
        ]);
        assert_single_exit(&out);
        assert_eq!(
            show(&out),
            "\
ec_result <- None
if not (m == None) {
  ec_r1 <- invoke O()
  if not (ec_r1 == None) {
    r <- Unwrap(ec_r1)
    x <- Unwrap(m)
    y <- Unwrap(m)
    ec_result <- Some(1)
  }
}
return ec_result
"
        );
    }

    /// …but the local an invoke binds *is* written.
    #[test]
    fn an_invoke_invalidates_the_local_it_binds() {
        let m = var("m", Type::maybe(Type::integer()));
        let invoke_into_m = Statement::Assignment(
            Assignment {
                pattern: Pattern::Ident(m),
                rhs: AssignmentRhs::Invoke {
                    oracle_name: "O".to_string(),
                    args: vec![],
                    edge: Some(edge("O", Type::maybe(Type::integer()))),
                    return_type: Some(Type::maybe(Type::integer())),
                },
            },
            span(),
        );
        let out = lower_int_oracle(vec![
            bind(1, maybe_int("m")),
            invoke_into_m,
            let_("x", tmp(1)),
            ret(1),
        ]);
        assert!(show(&out).contains("m_v <- Unwrap(m)"), "{}", show(&out));
        assert!(show(&out).contains("x <- m_v"), "{}", show(&out));
    }

    /// §3.4: an operand above [`MAX_INLINED_UNWRAP_SIZE`] keeps its
    /// temporary even though nothing invalidates it; a dominated second
    /// unwrap of it still loses its guard.
    #[test]
    fn a_large_operand_keeps_its_temporary_but_not_its_duplicate_guard() {
        let tuple_ty = Type::tuple(vec![Type::integer(); 6]);
        let big_table = var("B", Type::table(tuple_ty, Type::integer()));
        let key = Expression::from_kind(ExpressionKind::Tuple(
            ["a", "b", "c", "d", "e", "f"]
                .iter()
                .map(|n| int(n))
                .collect(),
        ));
        let operand = Expression::from_kind(ExpressionKind::TableAccess(big_table, Box::new(key)));
        assert!(expr_size(&operand) > MAX_INLINED_UNWRAP_SIZE);
        let out = lower_int_oracle(vec![
            bind(1, operand.clone()),
            let_("x", tmp(1)),
            bind(2, operand),
            let_("y", tmp(2)),
            ret(1),
        ]);
        let shown = show(&out);
        assert_eq!(shown.matches("if not (").count(), 1, "{shown}");
        assert!(shown.contains("unwrap-1 <- Unwrap(B["), "{shown}");
        assert!(shown.contains("x <- unwrap-1"), "{shown}");
        assert!(shown.contains("unwrap-2 <- Unwrap(B["), "{shown}");
        assert!(shown.contains("y <- unwrap-2"), "{shown}");
    }

    /// Two survivors deriving the same name are ambiguous: both keep their
    /// counter names rather than one of them being silently renamed.
    #[test]
    fn ambiguous_derived_names_fall_back_to_the_counter_names() {
        let reassign_m = || {
            assign(
                Pattern::Ident(var("m", Type::maybe(Type::integer()))),
                Expression::from_kind(ExpressionKind::Some(Box::new(Expression::integer(7)))),
                span(),
            )
        };
        let out = lower_int_oracle(vec![
            bind(1, maybe_int("m")),
            reassign_m(),
            let_("x", tmp(1)),
            bind(2, maybe_int("m")),
            reassign_m(),
            let_("y", tmp(2)),
            ret(1),
        ]);
        let shown = show(&out);
        assert!(shown.contains("unwrap-1 <- Unwrap(m)"), "{shown}");
        assert!(shown.contains("unwrap-2 <- Unwrap(m)"), "{shown}");
        assert!(!shown.contains("m_v"), "{shown}");
    }

    /// §3.4: a derived name that is already an identifier of the oracle is a
    /// hard error carrying the span of the unwrap, never a silent rename.
    #[test]
    fn a_derived_name_collision_is_a_hard_error_with_a_span() {
        let bind_span: SourceSpan = (40, 12).into();
        let mut binding = bind(1, maybe_int("m"));
        let Statement::Assignment(_, s) = &mut binding else {
            unreachable!()
        };
        *s = bind_span;
        let err = lower_oracle(
            &CodeBlock(vec![
                let_("m_v", Expression::integer(0)),
                binding,
                assign(
                    Pattern::Ident(var("m", Type::maybe(Type::integer()))),
                    Expression::from_kind(ExpressionKind::None(Type::integer())),
                    span(),
                ),
                let_("x", tmp(1)),
                ret(1),
            ]),
            &Type::integer(),
            span(),
            &BTreeSet::new(),
        )
        .unwrap_err();
        assert_eq!(
            err,
            EasyCryptifyError::TemporaryNameCollision(TemporaryNameCollision {
                name: "m_v".to_string(),
                span: bind_span,
            })
        );

        // a name reserved by the caller (a parameter or a state field) too
        let err = lower_oracle(
            &CodeBlock(vec![
                bind(1, maybe_int("m")),
                assign(
                    Pattern::Ident(var("m", Type::maybe(Type::integer()))),
                    Expression::from_kind(ExpressionKind::None(Type::integer())),
                    span(),
                ),
                let_("x", tmp(1)),
                ret(1),
            ]),
            &Type::integer(),
            span(),
            &BTreeSet::from(["m_v".to_string()]),
        )
        .unwrap_err();
        assert!(matches!(err, EasyCryptifyError::TemporaryNameCollision(_)));
    }

    /// Nested unwraps (`Unwrap(State[Unwrap(First[sid])])`): the inner
    /// temporary is substituted into the outer operand, and each operand
    /// is still guarded, inner first.
    #[test]
    fn a_nested_unwrap_is_substituted_into_the_outer_operand() {
        let out = lower_int_oracle(vec![
            bind(1, get("First", int("sid"))),
            bind(2, get("State", tmp(1))),
            let_("x", tmp(2)),
            ret(1),
        ]);
        assert_eq!(
            show(&out),
            "\
ec_result <- None
if not (First[sid] == None) {
  if not (State[Unwrap(First[sid])] == None) {
    x <- Unwrap(State[Unwrap(First[sid])])
    ec_result <- Some(1)
  }
}
return ec_result
"
        );
        assert!(every_unwrap_is_guarded(&out.0));
    }

    #[test]
    fn the_guard_containment_check_catches_an_unguarded_unwrap() {
        assert!(!every_unwrap_is_guarded(&[let_(
            "x",
            Expression::from_kind(ExpressionKind::Unwrap(Box::new(maybe_int("m"))))
        )]));
        assert!(!every_unwrap_is_guarded(&[ite_e(
            not(is_none(maybe_int("m"))),
            vec![],
            vec![let_(
                "x",
                Expression::from_kind(ExpressionKind::Unwrap(Box::new(maybe_int("m"))))
            )],
        )]));
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

    /// Story 17 §4 over every example, both 4WHS theorems included:
    ///
    /// - no path through an exported oracle tests the same `e == None` twice.
    ///   The one allowed repeat is a guard directly repeating the user's own
    ///   `assert not (e == None)` (story 16 §1.2's `State[ctr]`). Removing
    ///   that is redundant-*condition* elimination, which §6 defers;
    /// - no `unwrap-N` temporary survives, because in every project each use
    ///   follows its binding directly and every operand is small;
    /// - and every `Unwrap` sits inside a guard for its operand (the
    ///   `debug_assert` in `lower_oracle`, checked here in release builds
    ///   too).
    #[test]
    fn no_example_repeats_an_unwrap_guard_on_one_path_or_keeps_a_temporary() {
        use crate::project::{DirectoryFiles, DirectoryProject, Project as _};
        use crate::transforms::theorem_transforms::{DebugTransform, EasyCryptTransform};
        use crate::transforms::TheoremTransform as _;

        /// `e` for a condition `not (e == None)`.
        fn guarded(cond: &Expression) -> Option<&Expression> {
            let ExpressionKind::Not(inner) = cond.kind() else {
                return None;
            };
            match inner.kind() {
                ExpressionKind::Equals(es)
                    if es.len() == 2 && matches!(es[1].kind(), ExpressionKind::None(_)) =>
                {
                    Some(&es[0])
                }
                _ => None,
            }
        }

        /// Operands of the source's `assert not (e == None)`s, read off the
        /// un-lowered (`DebugTransform`) body.
        fn asserted(stmts: &[Statement], out: &mut Vec<Expression>) {
            for s in stmts {
                if let Statement::IfThenElse(ite) = s {
                    if matches!(ite.else_block.0.as_slice(), [Statement::Abort(_)]) {
                        out.extend(guarded(&ite.cond).cloned());
                    }
                    asserted(&ite.then_block.0, out);
                    asserted(&ite.else_block.0, out);
                }
            }
        }

        fn walk<'a>(
            stmts: &'a [Statement],
            path: &mut Vec<&'a Expression>,
            asserted: &[Expression],
            where_: &str,
        ) {
            for s in stmts {
                if let Statement::Assignment(Assignment { pattern, .. }, _) = s {
                    for id in pattern_writes(pattern) {
                        assert!(
                            !id.starts_with(UNWRAP_TEMP_PREFIX),
                            "{where_}: temporary {id} survived"
                        );
                    }
                }
                let Statement::IfThenElse(ite) = s else {
                    continue;
                };
                let guard = guarded(&ite.cond);
                if let Some(e) = guard {
                    let seen = path.iter().filter(|p| **p == e).count();
                    let allowed = usize::from(asserted.contains(e));
                    assert!(
                        seen <= allowed,
                        "{where_}: `{} == None` is tested {} times on one path",
                        show_expr(e),
                        seen + 1
                    );
                    path.push(e);
                }
                walk(&ite.then_block.0, path, asserted, where_);
                if guard.is_some() {
                    path.pop();
                }
                walk(&ite.else_block.0, path, asserted, where_);
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
        ];
        let mut guards_checked = 0;
        for (dir, theorems) in projects {
            let files = DirectoryFiles::load(std::path::Path::new(dir)).unwrap();
            let project = DirectoryProject::load(std::path::PathBuf::from(dir), &files).unwrap();
            for name in *theorems {
                let theorem = project.get_theorem(name).unwrap();
                let (exported, _) = EasyCryptTransform.transform_theorem(theorem).unwrap();
                let (source, _) = DebugTransform.transform_theorem(theorem).unwrap();
                for (gi, src_gi) in exported.instances.iter().zip(&source.instances) {
                    for (inst, src_inst) in gi.game().pkgs.iter().zip(&src_gi.game().pkgs) {
                        for (oracle, src_oracle) in
                            inst.pkg.oracles.iter().zip(&src_inst.pkg.oracles)
                        {
                            let where_ = format!("{name} {}::{}", inst.pkg.name, oracle.sig.name);
                            let mut asserts = Vec::new();
                            asserted(&src_oracle.code.0, &mut asserts);
                            walk(&oracle.code.0, &mut Vec::new(), &asserts, &where_);
                            assert!(every_unwrap_is_guarded(&oracle.code.0), "{where_}");
                            guards_checked += 1;
                        }
                    }
                }
            }
        }
        assert!(
            guards_checked > 100,
            "only {guards_checked} oracles checked"
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
