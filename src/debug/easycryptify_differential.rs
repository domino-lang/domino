// SPDX-License-Identifier: MIT OR Apache-2.0

//! The story-16 §5.1 differential test: `easycryptify` preserves **meaning**.
//!
//! The unit tests in `src/transforms/easycryptify.rs` pin the *shape* of the
//! lowering. This checks, with cvc5, that for one oracle the treeified
//! reference ([`EquivalenceTransform`], the trusted pipeline `domino prove`
//! uses) and the easycryptified version ([`EasyCryptTransform`]) cannot
//! disagree on equal arguments, equal prior state and equal randomness, where
//! "agree" is:
//!
//! - the reference aborts **iff** the easycryptified oracle returns `None`;
//! - the reference returns `v` **iff** the easycryptified one returns `Some(v)`;
//! - the resulting game state (package state and randomness counters) is
//!   identical.
//!
//! Both versions are symbolically executed with the debugger's executor
//! ([`crate::debug::exec`]) and compared through its **per-path SMT** — the
//! flat, acyclic, single-assignment conjunction every [`TerminalPath`] carries.
//! Not through `PathEffect`, which is lossy by design and never solver-facing.
//!
//! The reference runs as [`Side::Left`], the easycryptified version as
//! [`Side::Right`], *on the same game instance*, so the two share every root
//! constant — the oracle arguments (`<arg-…>`), the old game state, the game
//! constants and the `__sample-rand-…` functions — and only their SSA names
//! (`v!left!…` / `v!right!…`) differ. For every pair of terminal paths
//! `(l, r)` the solver must find `base ∧ l ∧ r ∧ ¬agree(l, r)` unsatisfiable.
//! Since each side's paths cover every input, that is the whole claim. A
//! vacuity guard makes sure the base frame is satisfiable and that every
//! feasible reference path overlaps at least one easycryptified path.
//!
//! `#[ignore]`d: it needs the `cvc5` binary on `PATH` and runs a symbolic
//! execution twice per oracle. Run it with
//! `cargo test --workspace -- --ignored easycryptify_matches_treeify`.

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::path::{Path, PathBuf};

use crate::debug::exec::{execute, Side, TerminalPath};
use crate::debug::ir::{inline_oracle, InlBlock, InlStmt, InlinedOracle, Place};
use crate::gamehops::GameHop;
use crate::identifier::Identifier;
use crate::project::{DirectoryFiles, DirectoryProject, Project as _};
use crate::theorem::Theorem;
use crate::transforms::theorem_transforms::{
    EasyCryptTransform, EquivalenceTransform, GameInstAux,
};
use crate::transforms::TheoremTransform as _;
use crate::writers::smt::contexts::EquivalenceContext;
use crate::writers::smt::declare::declare_const;
use crate::writers::smt::exprs::SmtExpr;

/// Upper bound on the paths per side — a runaway guard, not a sampling cap:
/// exceeding it fails the test instead of silently checking fewer paths.
const MAX_PATHS: usize = 4096;

/// What one terminal path computed, read back out of its
/// `return_constraint`, `(assert (= <return-…> (<mk-oracle-return-…> GS RV)))`,
/// where `RV` is `(mk-return-value V)` or `(as mk-abort …)`.
struct Outcome {
    /// The SSA constant holding the final game state.
    game_state: SmtExpr,
    /// `Some(V)` for a return, `None` for an abort.
    value: Option<SmtExpr>,
}

fn outcome(path: &TerminalPath) -> Outcome {
    let shape = || {
        panic!(
            "unexpected return_constraint shape: {}",
            path.return_constraint
        )
    };
    let SmtExpr::List(assert) = &path.return_constraint else {
        shape()
    };
    let [SmtExpr::Atom(kw), SmtExpr::List(eq)] = assert.as_slice() else {
        shape()
    };
    assert_eq!(kw, "assert");
    let [SmtExpr::Atom(op), _ret_const, SmtExpr::List(mk)] = eq.as_slice() else {
        shape()
    };
    assert_eq!(op, "=");
    let [_ctor, game_state, rv] = mk.as_slice() else {
        shape()
    };
    let value = match rv {
        SmtExpr::List(items) if matches!(items.first(), Some(SmtExpr::Atom(a)) if a == "mk-return-value") => {
            Some(items[1].clone())
        }
        SmtExpr::List(items) if matches!(items.first(), Some(SmtExpr::Atom(a)) if a == "as") => {
            assert!(
                matches!(items.get(1), Some(SmtExpr::Atom(a)) if a == "mk-abort"),
                "unexpected return value: {rv}"
            );
            None
        }
        _ => shape(),
    };
    assert_eq!(path.terminal.is_abort(), value.is_none());
    Outcome {
        game_state: game_state.clone(),
        value,
    }
}

fn emit(smt: &mut String, e: SmtExpr) {
    writeln!(smt, "{e}").unwrap();
}

fn list(items: Vec<SmtExpr>) -> SmtExpr {
    SmtExpr::List(items)
}

fn atom(s: &str) -> SmtExpr {
    SmtExpr::Atom(s.to_string())
}

/// The agreement condition of one (reference, easycryptified) path pair.
fn agree(reference: &Outcome, ec: &Outcome) -> SmtExpr {
    let same_state = list(vec![
        atom("="),
        reference.game_state.clone(),
        ec.game_state.clone(),
    ]);
    let Some(ec_value) = &ec.value else {
        // `easycryptify` leaves no `abort`; the only abort terminals the
        // executor still produces for it are the `none` children of guarded
        // `Unwrap`s, which must be infeasible. Nothing agrees with them.
        return atom("false");
    };
    let same_value = match &reference.value {
        None => list(vec![
            list(vec![atom("_"), atom("is"), atom("mk-none")]),
            ec_value.clone(),
        ]),
        Some(v) => list(vec![
            atom("="),
            ec_value.clone(),
            list(vec![atom("mk-some"), v.clone()]),
        ]),
    };
    list(vec![atom("and"), same_state, same_value])
}

/// `(assert (= <return-…> …))` for an oracle *other* than the one under test
/// ties its `<return-…>` constant to the monolithic oracle function. The
/// check never mentions those constants; dropping the ties keeps the base
/// frame small without changing what can be derived about this oracle.
fn is_return_tie(e: &SmtExpr) -> bool {
    let SmtExpr::List(items) = e else {
        return false;
    };
    let [SmtExpr::Atom(kw), SmtExpr::List(eq)] = items.as_slice() else {
        return false;
    };
    kw == "assert"
        && matches!(eq.as_slice(), [SmtExpr::Atom(op), SmtExpr::Atom(c), ..]
            if op == "=" && c.starts_with("<return-"))
}

/// Every frame-local of `inl`: its raw SMT symbol (`<pkg#frame::name>`) and
/// the declaration of its [`sanitize`]d stand-in.
///
/// The executor explores every *syntactic* path without a solver, and binds
/// a local only when it is assigned. On a path that is infeasible, a local
/// can be read before any assignment — e.g. the body of an `if (not
/// ec_done)` guard on a path where an earlier guard already failed — and the
/// executor then leaves the local's own symbol in the SMT, undeclared. On a
/// feasible path this cannot happen (Domino never reads an unassigned local),
/// so the harness declares each such symbol as an unconstrained constant:
/// sound, since an arbitrary value only makes disagreement *easier* to find.
/// (The raw symbol is not even legal SMT-LIB — `#` ends a simple symbol — so
/// it is renamed via [`sanitize`] where it occurs.)
fn local_symbols(inl: &InlinedOracle) -> BTreeMap<String, SmtExpr> {
    fn place(p: &Place, out: &mut BTreeMap<String, SmtExpr>) {
        match p {
            Place::Local { key, ty } => {
                let name = Identifier::Generated(key.clone(), ty.clone()).smt_identifier_string();
                let decl = declare_const(sanitize(&name), ty.clone().into());
                out.insert(name, decl);
            }
            Place::Index { base, .. } => place(base, out),
            Place::Tuple(ps) => ps.iter().for_each(|p| place(p, out)),
            Place::State { .. } | Place::Discard => {}
        }
    }
    fn block(b: &InlBlock, out: &mut BTreeMap<String, SmtExpr>) {
        for stmt in &b.0 {
            match stmt {
                InlStmt::Assign { target, .. }
                | InlStmt::Sample { target, .. }
                | InlStmt::Unwrap { target, .. } => place(target, out),
                InlStmt::Branch { then, els, .. } => {
                    block(then, out);
                    block(els, out);
                }
                InlStmt::Call {
                    frame, bind, body, ..
                } => {
                    for (key, ty, _) in &frame.arg_bindings {
                        place(
                            &Place::Local {
                                key: key.clone(),
                                ty: ty.clone(),
                            },
                            out,
                        );
                    }
                    if let Some(b) = bind {
                        place(b, out);
                    }
                    block(body, out);
                }
                InlStmt::Return { .. } | InlStmt::Abort { .. } => {}
            }
        }
    }
    let mut out = BTreeMap::new();
    block(&inl.body, &mut out);
    out
}

/// A legal SMT-LIB stand-in for a raw `<pkg#frame::name>` local symbol.
fn sanitize(raw: &str) -> String {
    raw.replace('#', "!").replace("::", "!unbound!")
}

/// `path`'s `decls` and `constraints` as SMT text, preceded by declarations
/// of the locals it reads without ever binding (see [`local_symbols`]) —
/// skipping any already in `declared` — with each such read renamed to its
/// declared stand-in. The returned text never mentions a raw local symbol.
fn path_text(
    path: &TerminalPath,
    locals: &BTreeMap<String, SmtExpr>,
    declared: &mut std::collections::BTreeSet<String>,
) -> String {
    let mut body = String::new();
    for e in path.decls.iter().chain(&path.constraints) {
        writeln!(body, "{e}").unwrap();
    }
    let mut out = String::new();
    for (raw, decl) in locals {
        if body.contains(raw.as_str()) {
            body = body.replace(raw.as_str(), &sanitize(raw));
            if declared.insert(raw.clone()) {
                writeln!(out, "{decl}").unwrap();
            }
        }
    }
    out.push_str(&body);
    out
}

/// [`Outcome`] with every raw local symbol renamed as [`path_text`] does.
fn sanitize_outcome(o: Outcome, locals: &BTreeMap<String, SmtExpr>) -> Outcome {
    let fix = |e: SmtExpr| -> SmtExpr {
        let text = e.to_string();
        if locals.keys().any(|raw| text.contains(raw.as_str())) {
            let mut t = text;
            for raw in locals.keys() {
                t = t.replace(raw.as_str(), &sanitize(raw));
            }
            SmtExpr::Atom(t)
        } else {
            e
        }
    };
    Outcome {
        game_state: fix(o.game_state),
        value: o.value.map(fix),
    }
}

fn load(dir: &Path) -> DirectoryProject<'static> {
    let files: &'static DirectoryFiles = Box::leak(Box::new(DirectoryFiles::load(dir).unwrap()));
    DirectoryProject::load(dir.to_path_buf(), files).unwrap()
}

/// Checks one oracle of the game instance on `side_left ? left : right` of
/// equivalence hop `hop` of `theorem_name`. Returns `(reference paths,
/// easycryptified paths)` for the report.
fn check(dir: &Path, theorem_name: &str, hop: usize, left: bool, oracle: &str) -> (usize, usize) {
    // Everything below borrows from the project; leaking keeps the lifetimes
    // simple in a test.
    let project: &'static DirectoryProject<'static> = Box::leak(Box::new(load(dir)));
    let theorem: &'static Theorem<'static> = project.get_theorem(theorem_name).unwrap();
    let (theorem_ref, auxs_ref) = EquivalenceTransform.transform_theorem(theorem).unwrap();
    let (theorem_ec, auxs_ec) = EasyCryptTransform.transform_theorem(theorem).unwrap();
    let theorem_ref: &'static Theorem<'static> = Box::leak(Box::new(theorem_ref));
    let theorem_ec: &'static Theorem<'static> = Box::leak(Box::new(theorem_ec));
    let auxs_ref: &'static Vec<(String, GameInstAux)> = Box::leak(Box::new(auxs_ref));
    let auxs_ec: &'static Vec<(String, GameInstAux)> = Box::leak(Box::new(auxs_ec));

    let eq = match &theorem_ref.game_hops[hop] {
        GameHop::Equivalence(eq) => eq,
        other => panic!("hop {hop} of {theorem_name} is not an equivalence: {other:?}"),
    };
    let gi_name = if left {
        eq.left_name()
    } else {
        eq.right_name()
    };
    let eqctx = EquivalenceContext::new(eq, theorem_ref, auxs_ref);

    let sample_info = |auxs: &'static Vec<(String, GameInstAux)>| {
        &auxs
            .iter()
            .find(|(n, _)| n == gi_name)
            .unwrap()
            .1
            .sample_info
    };
    let ref_inst = theorem_ref.find_game_instance(gi_name).unwrap();
    let ec_inst = theorem_ec.find_game_instance(gi_name).unwrap();
    let ref_si = sample_info(auxs_ref);
    let ec_si = sample_info(auxs_ec);
    assert_eq!(
        ref_si.positions, ec_si.positions,
        "both pipelines run samplify before their control-flow lowering, so the \
         sampling positions (and therefore the randomness) must coincide"
    );

    let ref_inl = inline_oracle(ref_inst, oracle).unwrap();
    let ec_inl = inline_oracle(ec_inst, oracle).unwrap();
    let ref_paths = execute(&ref_inl, ref_inst, ref_si, Side::Left, Some(MAX_PATHS)).unwrap();
    let ec_paths = execute(&ec_inl, ec_inst, ec_si, Side::Right, Some(MAX_PATHS)).unwrap();
    assert!(!ref_paths.is_empty() && !ec_paths.is_empty());

    // --- one cvc5 script for the whole oracle -----------------------------
    let mut smt = String::new();
    emit(
        &mut smt,
        list(vec![atom("set-option"), atom(":incremental"), atom("true")]),
    );
    for e in eqctx.emit_base_declarations() {
        emit(&mut smt, e);
    }
    for e in eqctx.emit_theorem_paramfuncs() {
        emit(&mut smt, e);
    }
    for e in eqctx.emit_game_definitions() {
        emit(&mut smt, e);
    }
    for e in eqctx.emit_constant_declarations(Some(oracle)) {
        if !is_return_tie(&e) {
            emit(&mut smt, e);
        }
    }
    let check_sat = || list(vec![atom("check-sat")]);
    let push = || list(vec![atom("push"), atom("1")]);
    let pop = || list(vec![atom("pop"), atom("1")]);

    emit(&mut smt, check_sat()); // base frame must be satisfiable
    let ref_locals = local_symbols(&ref_inl);
    let ec_locals = local_symbols(&ec_inl);
    let ec_outcomes: Vec<Outcome> = ec_paths
        .iter()
        .map(|p| sanitize_outcome(outcome(p), &ec_locals))
        .collect();
    for rp in &ref_paths {
        let r = sanitize_outcome(outcome(rp), &ref_locals);
        emit(&mut smt, push());
        let mut declared = std::collections::BTreeSet::new();
        smt.push_str(&path_text(rp, &ref_locals, &mut declared));
        emit(&mut smt, check_sat()); // reference path feasible?
        for (ep, e_out) in ec_paths.iter().zip(&ec_outcomes) {
            emit(&mut smt, push());
            smt.push_str(&path_text(ep, &ec_locals, &mut declared.clone()));
            emit(&mut smt, check_sat()); // jointly feasible?
            emit(
                &mut smt,
                list(vec![
                    atom("assert"),
                    list(vec![atom("not"), agree(&r, e_out)]),
                ]),
            );
            emit(&mut smt, check_sat()); // disagreement: must be unsat
            emit(&mut smt, pop());
        }
        emit(&mut smt, pop());
    }

    let script = std::env::temp_dir().join(format!(
        "easycryptify-differential-{}-{theorem_name}-{gi_name}-{oracle}.smt2",
        std::process::id()
    ));
    std::fs::write(&script, &smt).unwrap();
    let out = std::process::Command::new("cvc5")
        .args(["--lang=smt2", "--tlimit-per=60000"])
        .arg(&script)
        .output()
        .expect("easycryptify_matches_treeify needs the cvc5 binary on PATH");
    let stdout = String::from_utf8_lossy(&out.stdout);
    let mut answers = stdout.lines().filter(|l| !l.trim().is_empty());
    let mut next = |what: &str| -> String {
        let a = answers.next().unwrap_or_else(|| {
            panic!(
                "cvc5 ran out of answers at {what}\nstderr: {}\nscript: {}",
                String::from_utf8_lossy(&out.stderr),
                script.display()
            )
        });
        assert!(
            a == "sat" || a == "unsat",
            "{oracle} in {gi_name}: cvc5 answered `{a}` at {what}; script: {}",
            script.display()
        );
        a.to_string()
    };

    assert_eq!(next("the base frame"), "sat", "base frame is unsatisfiable");
    let mut feasible_ref_paths = 0;
    for (i, rp) in ref_paths.iter().enumerate() {
        let feasible = next(&format!("reference path {i}")) == "sat";
        let mut overlaps = false;
        for (j, ep) in ec_paths.iter().enumerate() {
            overlaps |= next(&format!("pair ({i}, {j}) feasibility")) == "sat";
            let verdict = next(&format!("pair ({i}, {j}) disagreement"));
            assert_eq!(
                verdict,
                "unsat",
                "{oracle} in {gi_name}: reference path {i} ({:?}) and easycryptified path {j} \
                 ({:?}) can disagree; script: {}",
                rp.terminal,
                ep.terminal,
                script.display()
            );
        }
        if feasible {
            feasible_ref_paths += 1;
            assert!(
                overlaps,
                "{oracle} in {gi_name}: feasible reference path {i} overlaps no \
                 easycryptified path; script: {}",
                script.display()
            );
        }
    }
    assert!(
        feasible_ref_paths > 0,
        "{oracle} in {gi_name}: no feasible reference path"
    );
    let _ = std::fs::remove_file(&script);
    (ref_paths.len(), ec_paths.len())
}

fn repo(rel: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(rel)
}

/// A throwaway project with the shapes the corpus lacks: an oracle whose
/// every path aborts (the `(Always, Always)` case, with a dropped
/// continuation), an `if c { abort }` (the `(Always, _)` case), joins whose
/// early exit is *feasible* (in the 4WHS oracles every exit that reaches a
/// join is infeasible, so there the `ec_done` guard is not load-bearing), a
/// callee that aborts and already returns `Maybe(T)` (`Maybe(Maybe(T))`
/// after lowering), and a bare `invoke`.
fn synthetic_project() -> tempfile::TempDir {
    let dir = tempfile::tempdir().unwrap();
    let write = |rel: &str, text: &str| {
        let p = dir.path().join(rel);
        std::fs::create_dir_all(p.parent().unwrap()).unwrap();
        std::fs::write(p, text).unwrap();
    };
    write("ssp.toml", "");
    write(
        "packages/Callee.pkg.ssp",
        "package Callee {
    params {
        b: Bool,
    }

    state {
        t: Table(Integer, Integer),
    }

    oracle Get(k: Integer) -> Maybe(Integer) {
        if b {
            abort;
        }
        return t[k];
    }

    oracle Put(k: Integer, v: Integer) {
        assert (t[k] == None as Integer);
        t[k] <- Some(v);
    }
}
",
    );
    write(
        "packages/Caller.pkg.ssp",
        "package Caller {
    state {
        ctr: Integer,
        u: Table(Integer, Integer),
    }

    import oracles {
        Get(k: Integer) -> Maybe(Integer),
        Put(k: Integer, v: Integer),
    }

    oracle AllAbort(x: Integer) -> Integer {
        ctr <- (ctr + x);
        if (x == 1) {
            abort;
        } else {
            abort;
        }
        ctr <- 0;
        return ctr;
    }

    oracle ThenAborts(x: Integer) -> Integer {
        if (x == 0) {
            abort;
        }
        ctr <- (ctr + 1);
        return ctr;
    }

    oracle Join(x: Integer) -> Integer {
        if (x == 1) {
            y <- Unwrap(u[x]);
        } else {
            y <- 0;
        }
        ctr <- (ctr + 1);
        return y;
    }

    oracle NestedReturn(x: Integer) -> Integer {
        if (x == 2) {
            if (ctr == 0) {
                return 7;
            }
        }
        ctr <- (ctr + 1);
        return ctr;
    }

    oracle Chain(k: Integer, v: Integer) -> Integer {
        invoke Put(k, v);
        m <- invoke Get(k);
        if (m == None as Integer) {
            ctr <- (ctr + 1);
        } else {
            ctr <- Unwrap(m);
        }
        return ctr;
    }

    oracle Dominated(k: Integer) -> Integer {
        y <- Unwrap(u[k]);
        if (y == 0) {
            z <- Unwrap(u[k]);
        } else {
            z <- 1;
        }
        m <- invoke Get(k);
        ctr <- (ctr + Unwrap(u[k]));
        return z;
    }

    oracle AfterJoin(x: Integer, k: Integer) -> Integer {
        if (x == 1) {
            y <- Unwrap(u[k]);
        } else {
            y <- 0;
        }
        z <- Unwrap(u[k]);
        return (y + z);
    }

    oracle TableWritten(k: Integer, j: Integer) -> Integer {
        y <- Unwrap(u[k]);
        u[j] <- None as Integer;
        z <- Unwrap(u[k]);
        return (y + z);
    }

    oracle LocalReassigned(k: Integer) -> Integer {
        m <- u[k];
        y <- Unwrap(m);
        m <- u[(k + 1)];
        z <- Unwrap(m);
        return (y + z);
    }
}
",
    );
    write(
        "games/G.comp.ssp",
        "composition G {
    const b: Bool;

    instance callee = Callee {
        params {
            b: b,
        }
    }

    instance caller = Caller {}

    compose {
        adversary: {
            AllAbort: caller,
            ThenAborts: caller,
            Join: caller,
            NestedReturn: caller,
            Chain: caller,
            Dominated: caller,
            AfterJoin: caller,
            TableWritten: caller,
            LocalReassigned: caller,
        },
        caller: {
            Get: callee,
            Put: callee,
        },
    }
}
",
    );
    write(
        "theorem/proof.ssp",
        "theorem T {
    const b: Bool;

    instance g0 = G {
        params {
            b: false,
        }
    }

    instance g1 = G {
        params {
            b: b,
        }
    }

    gamehops {
        equivalence g0 g1 {
            invariant: ./theorem/invariant.smt2
            AllAbort: {
                lemmas {
                    equal-aborts: []
                }
            }
            ThenAborts: {
                lemmas {
                    equal-aborts: []
                }
            }
            Join: {
                lemmas {
                    equal-aborts: []
                }
            }
            NestedReturn: {
                lemmas {
                    equal-aborts: []
                }
            }
            Chain: {
                lemmas {
                    equal-aborts: []
                }
            }
            Dominated: {
                lemmas {
                    equal-aborts: []
                }
            }
            AfterJoin: {
                lemmas {
                    equal-aborts: []
                }
            }
            TableWritten: {
                lemmas {
                    equal-aborts: []
                }
            }
            LocalReassigned: {
                lemmas {
                    equal-aborts: []
                }
            }
        }
    }
}
",
    );
    write("theorem/invariant.smt2", "");
    dir
}

#[test]
#[ignore = "needs the cvc5 binary on PATH; runs a symbolic execution twice per oracle"]
fn easycryptify_matches_treeify() {
    let mut report = Vec::new();
    let mut run = |dir: &Path, theorem: &str, hop: usize, left: bool, oracle: &str| {
        let (r, e) = check(dir, theorem, hop, left, oracle);
        report.push(format!(
            "{theorem}#{hop} {oracle}: {r} reference × {e} easycryptified paths"
        ));
    };

    let four_whs = repo("example-projects/4WHS");
    // Full4WHS hop 7 is `H4 == H5`; H4 instantiates `KX_nochecks`. `Send3` is
    // the 4-live-leaf cascade: the flag, and the tail collapsing to one copy.
    run(&four_whs, "Full4WHS", 7, true, "Send3");
    // Full4WHS hop 0 is `H0 == H1_0`; H0 instantiates `KX`. `Send2` has
    // nested unwraps under an invoke; `NewSession` has no join, so no flag.
    run(&four_whs, "Full4WHS", 0, true, "Send2");
    run(&four_whs, "Full4WHS", 0, true, "NewSession");

    let synthetic = synthetic_project();
    for left in [true, false] {
        // `(Always, Always)` and the dropped continuation
        run(synthetic.path(), "T", 0, left, "AllAbort");
        // `(Always, _)`: the continuation moves into the surviving branch
        run(synthetic.path(), "T", 0, left, "ThenAborts");
        // joins whose early exit is feasible, so the `ec_done` guard is
        // load-bearing: an unwrap that may abort, and a nested `return`
        run(synthetic.path(), "T", 0, left, "Join");
        run(synthetic.path(), "T", 0, left, "NestedReturn");
        // a bare invoke, and a `Maybe`-returning callee that may abort
        run(synthetic.path(), "T", 0, left, "Chain");
        // story 17: guards dropped as dominated, with a *feasible* first
        // abort, the dominating guard reached across an `if` and an invoke
        // (the callee cannot write the caller's `u`, §2.2)
        run(synthetic.path(), "T", 0, left, "Dominated");
        // story 17: guards that must *not* be dropped — one after a join
        // whose other branch never unwrapped, one after a write to the
        // unwrapped table (at a possibly equal index), one after the
        // unwrapped local is reassigned
        run(synthetic.path(), "T", 0, left, "AfterJoin");
        run(synthetic.path(), "T", 0, left, "TableWritten");
        run(synthetic.path(), "T", 0, left, "LocalReassigned");
    }
    eprintln!("{}", report.join("\n"));
}
