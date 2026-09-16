// SPDX-License-Identifier: MIT OR Apache-2.0

//! Renders an [`EcFile`] to EasyCrypt source text.
//!
//! Rendering is total: every AST that can be constructed renders to *some*
//! text (there is no `panic!`/`todo!` here), and rendering the same AST twice
//! is byte-identical — nothing here iterates a `HashMap`.
//!
//! Parenthesisation follows a precedence table (loosest first): `=>` (right
//! associative) `<` `\/` `<` `/\` `<` `=` `<>` `<` `<` `<=` `>` `>=` `<` `+`
//! `-` `<` `*` `%/` `%%` `<` `^^` `<` unary `!` `-` `<` application `<`
//! projection/`.[ ]`. This is the story's "minimum viable" table with one
//! correction: `^^` moves above `*`/`%/`/`%%` to match `ecParser.mly`'s
//! `%left`/`%right` declarations (see [`binop_info`]).

use super::ast::*;

const INDENT: &str = "  ";

/// Precedence of a prefix `!`/`-`.
const UNOP_PREC: i8 = 8;
/// Precedence of application-like forms: `f a b`, `Some e`, `oget e`,
/// `rem m k`. Their own arguments require [`ATOM_PREC`], not this: `f (g x)`
/// still needs parens around `g x` (juxtaposition is left-associative), so
/// an application is only safe unparenthesised where an atom would be.
const APP_PREC: i8 = 9;
/// Precedence of atoms: variables, literals, tuples, projections, map
/// indexing, and any other syntactically self-delimited form.
const ATOM_PREC: i8 = 10;

fn indent(level: usize) -> String {
    INDENT.repeat(level)
}

/// Render a whole file: the header banner, `require`s and top-level items.
pub fn render_file(f: &EcFile) -> String {
    let mut out = String::new();

    for line in &f.header {
        out.push_str(&format!("(* {line} *)\n"));
    }
    if !f.header.is_empty() {
        out.push('\n');
    }

    for req in &f.requires {
        out.push_str(&render_require(req));
        out.push('\n');
    }
    if !f.requires.is_empty() {
        out.push('\n');
    }

    let items: Vec<String> = f.items.iter().map(render_item).collect();
    out.push_str(&items.join("\n\n"));
    if !items.is_empty() {
        out.push('\n');
    }

    out
}

fn render_require(r: &Require) -> String {
    let keyword = if r.import { "require import" } else { "require" };
    format!("{keyword} {}.", r.names.join(" "))
}

fn render_item(item: &EcItem) -> String {
    match item {
        EcItem::Comment(s) => format!("(* {s} *)"),
        EcItem::TypeAbstract { name } => format!("type {name}."),
        EcItem::TypeAlias { name, ty } => format!("type {name} = {}.", render_type(ty)),
        EcItem::Record { name, fields } => render_record(name, fields),
        EcItem::OpDecl { name, ty } => format!("op {name} : {}.", render_type(ty)),
        EcItem::OpDef {
            name,
            args,
            ret,
            body,
        } => render_op_def(name, args, ret.as_ref(), body),
        EcItem::Axiom { name, formula } => {
            format!("axiom {name} : {}.", render_expr(formula))
        }
        EcItem::ModuleType {
            name,
            params,
            includes,
            procs,
        } => render_module_type(name, params, includes, procs),
        EcItem::Clone {
            base,
            as_name,
            overrides,
        } => render_clone(base, as_name, overrides),
        EcItem::ModuleAlias {
            name,
            functor,
            args,
        } => format!("module {name} = {functor}({}).", args.join(", ")),
        EcItem::Module(m) => render_module(m),
        EcItem::Section(s) => render_section(s),
    }
}

fn render_record(name: &str, fields: &[(String, EcType)]) -> String {
    let mut out = format!("type {name} = {{\n");
    let rendered: Vec<String> = fields
        .iter()
        .map(|(f, ty)| format!("{}{f} : {}", indent(1), render_type(ty)))
        .collect();
    out.push_str(&rendered.join(";\n"));
    out.push_str("\n}.");
    out
}

fn render_op_def(name: &str, args: &[(String, EcType)], ret: Option<&EcType>, body: &EcExpr) -> String {
    let mut out = format!("op {name}");
    for (arg_name, ty) in args {
        out.push_str(&format!(" ({arg_name} : {})", render_type(ty)));
    }
    if let Some(ty) = ret {
        out.push_str(&format!(" : {}", render_type(ty)));
    }
    out.push_str(&format!(" = {}.", render_expr(body)));
    out
}

/// A pure alias (`includes` has exactly one entry, `procs` is empty) renders
/// on one line — `module type X = { include Y }.` — matching the shape
/// story 11 specifies; anything else falls back to one line per member,
/// like a plain module type always has.
fn render_module_type(
    name: &str,
    params: &[(String, String)],
    includes: &[String],
    procs: &[ProcSig],
) -> String {
    let header = format!("module type {name}{}", render_params(params));
    if procs.is_empty() && includes.len() == 1 {
        return format!("{header} = {{ include {} }}.", includes[0]);
    }
    let mut lines: Vec<String> = includes
        .iter()
        .map(|inc| format!("{}include {inc}", indent(1)))
        .collect();
    lines.extend(
        procs
            .iter()
            .map(|sig| format!("{}{}", indent(1), render_proc_sig(sig))),
    );
    let mut out = header;
    out.push_str(" = {\n");
    out.push_str(&lines.join("\n"));
    out.push_str("\n}.");
    out
}

fn render_proc_sig(sig: &ProcSig) -> String {
    format!(
        "proc {}({}) : {}",
        sig.name,
        render_typed_args(&sig.args),
        render_type(&sig.ret)
    )
}

/// `name : ty` pairs, comma-separated, for a `proc(...)` argument list.
fn render_typed_args(args: &[(String, EcType)]) -> String {
    args.iter()
        .map(|(n, ty)| format!("{n} : {}", render_type(ty)))
        .collect::<Vec<_>>()
        .join(", ")
}

fn render_params(params: &[(String, String)]) -> String {
    params
        .iter()
        .map(|(n, ty)| format!(" ({n} : {ty})"))
        .collect()
}

fn render_clone(base: &str, as_name: &str, overrides: &[CloneOverride]) -> String {
    let mut out = format!("clone {base} as {as_name}");
    if !overrides.is_empty() {
        let rendered: Vec<String> = overrides.iter().map(render_clone_override).collect();
        out.push_str(" with ");
        out.push_str(&rendered.join(", "));
    }
    out.push('.');
    out
}

fn render_clone_override(o: &CloneOverride) -> String {
    match o {
        CloneOverride::Type { lhs, rhs } => format!("type {lhs} <- {}", render_type(rhs)),
        CloneOverride::Op { lhs, rhs } => format!("op {lhs} <- {}", render_expr(rhs)),
    }
}

fn render_module(m: &EcModule) -> String {
    let mut header = format!("module {}{}", m.name, render_params(&m.params));
    if let Some(implements) = &m.implements {
        header.push_str(&format!(" : {implements}"));
    }
    header.push_str(" = {\n");

    let mut body_lines: Vec<String> = Vec::new();
    for (name, ty) in &m.vars {
        body_lines.push(format!("{}var {name} : {}", indent(1), render_type(ty)));
    }
    if !m.vars.is_empty() && !m.procs.is_empty() {
        body_lines.push(String::new());
    }
    let proc_texts: Vec<String> = m.procs.iter().map(|p| render_proc(p, 1)).collect();
    body_lines.push(proc_texts.join("\n\n"));

    let mut out = header;
    out.push_str(&body_lines.join("\n"));
    out.push_str("\n}.");
    out
}

fn render_proc(p: &EcProc, level: usize) -> String {
    let pad = indent(level);
    let inner_pad = indent(level + 1);

    let mut out = format!(
        "{pad}proc {}({}) : {} = {{\n",
        p.name,
        render_typed_args(&p.args),
        render_type(&p.ret)
    );

    for (name, ty, init) in &p.locals {
        match init {
            Some(e) => out.push_str(&format!(
                "{inner_pad}var {name} : {} <- {};\n",
                render_type(ty),
                render_expr(e)
            )),
            None => out.push_str(&format!("{inner_pad}var {name} : {};\n", render_type(ty))),
        }
    }

    for stmt in &p.body.0 {
        out.push_str(&render_stmt(stmt, level + 1));
        out.push('\n');
    }

    if let Some(ret) = &p.ret_expr {
        out.push_str(&format!(
            "{inner_pad}return {};\n",
            render_expr(ret)
        ));
    }

    out.push_str(&format!("{pad}}}"));
    out
}

/// Render one statement at `level` levels of two-space indent. A conditional
/// spans multiple lines; every other statement is one line.
pub fn render_stmt(stmt: &EcStmt, level: usize) -> String {
    let pad = indent(level);
    match stmt {
        EcStmt::Comment(s) => format!("{pad}(* {s} *)"),
        EcStmt::Assign { lhs, rhs } => {
            format!("{pad}{} <- {};", render_lvalue(lhs), render_expr(rhs))
        }
        EcStmt::Sample { lhs, distr } => format!(
            "{pad}{} <$ {};",
            render_lvalue(lhs),
            render_expr(distr)
        ),
        EcStmt::Call {
            lhs,
            module,
            proc,
            args,
        } => {
            let rendered_args = args
                .iter()
                .map(render_expr)
                .collect::<Vec<_>>()
                .join(", ");
            let call = format!("{module}.{proc}({rendered_args})");
            match lhs {
                Some(l) => format!("{pad}{} <@ {call};", render_lvalue(l)),
                None => format!("{pad}{call};"),
            }
        }
        EcStmt::If {
            cond,
            then_block,
            else_block,
        } => {
            let mut out = format!("{pad}if ({}) {{\n", render_expr(cond));
            out.push_str(&render_block_lines(then_block, level + 1));
            out.push_str(&format!("\n{pad}}}"));
            if let Some(else_b) = else_block {
                out.push_str(" else {\n");
                out.push_str(&render_block_lines(else_b, level + 1));
                out.push_str(&format!("\n{pad}}}"));
            }
            out
        }
    }
}

fn render_block_lines(block: &EcBlock, level: usize) -> String {
    block
        .0
        .iter()
        .map(|s| render_stmt(s, level))
        .collect::<Vec<_>>()
        .join("\n")
}

fn render_lvalue(lv: &EcLvalue) -> String {
    match lv {
        EcLvalue::Var(v) => v.clone(),
        EcLvalue::Tuple(vars) => format!("({})", vars.join(", ")),
        EcLvalue::MapSet { map, key } => format!("{map}.[{}]", render_expr(key)),
    }
}

fn render_section(s: &EcSection) -> String {
    let mut lines: Vec<String> = vec!["section.".to_string()];
    for d in &s.declares {
        lines.push(render_declare_module(d));
    }
    for item in &s.items {
        lines.push(render_item(item));
    }
    for lemma in &s.lemmas {
        lines.push(render_lemma(lemma));
    }
    lines.push("end section.".to_string());
    lines.join("\n\n")
}

fn render_declare_module(d: &DeclareModule) -> String {
    let mut out = format!("declare module {} <: {}", d.name, d.module_type);
    if !d.restrictions.is_empty() {
        let restrictions = d
            .restrictions
            .iter()
            .map(|r| format!("-{r}"))
            .collect::<Vec<_>>()
            .join(", ");
        out.push_str(&format!(" {{ {restrictions} }}"));
    }
    out.push('.');
    out
}

fn render_lemma(lemma: &EcLemma) -> String {
    let binders: String = lemma
        .binders
        .iter()
        .map(render_lemma_binder)
        .collect::<Vec<_>>()
        .join(" ");
    let sep = if binders.is_empty() { "" } else { " " };
    let mut out = format!(
        "lemma {}{sep}{binders} : {}.\nproof.\n",
        lemma.name,
        render_expr(&lemma.statement)
    );
    for line in &lemma.proof {
        out.push_str(&render_proof_line(line));
        out.push('\n');
    }
    out.push_str("qed.");
    out
}

fn render_lemma_binder(b: &LemmaBinder) -> String {
    match b {
        LemmaBinder::Memory(name) => format!("&{name}"),
        LemmaBinder::Typed { name, ty } => format!("({name} : {})", render_type(ty)),
    }
}

fn render_proof_line(line: &ProofLine) -> String {
    let pad = indent(line.indent);
    match line.bullet {
        Some(b) => format!("{pad}{b} {}", line.text),
        None => format!("{pad}{}", line.text),
    }
}

/// Render a type. Tuple and function types parenthesise themselves whenever
/// they are nested inside a compound type (`option`, `fmap`, `distr`, or the
/// left side of `->`); a bare `EcType::Tuple` already renders itself
/// parenthesised (`(a * b)`), so only `EcType::Fun` needs an explicit wrap.
pub fn render_type(t: &EcType) -> String {
    match t {
        EcType::Int => "int".to_string(),
        EcType::Bool => "bool".to_string(),
        EcType::Unit => "unit".to_string(),
        EcType::Named(name) => name.clone(),
        EcType::Tuple(items) => {
            let rendered: Vec<String> = items.iter().map(render_type).collect();
            format!("({})", rendered.join(" * "))
        }
        EcType::Option(inner) => format!("{} option", render_type_atom(inner)),
        EcType::Fmap(k, v) => format!("({}, {}) fmap", render_type_atom(k), render_type_atom(v)),
        EcType::Distr(inner) => format!("{} distr", render_type_atom(inner)),
        EcType::Fun(a, b) => format!("{} -> {}", render_type_atom(a), render_type(b)),
    }
}

fn render_type_atom(t: &EcType) -> String {
    match t {
        EcType::Fun(..) => format!("({})", render_type(t)),
        _ => render_type(t),
    }
}

/// Render an expression with no outer parentheses (the entry point for
/// statement right-hand sides, formulas, and other true top-level positions).
pub fn render_expr(e: &EcExpr) -> String {
    render_operand(e, 0)
}

/// The precedence class of `e`'s outermost syntactic form, loosest at `0`
/// and tightest ("atom") at `10`. A negative integer literal is pinned to
/// application precedence (`9`) rather than atom precedence: bare next to
/// another token (as a bare application argument) `-1` lexes as subtraction,
/// e.g. `f -1` is `f - 1`, so it still needs parens exactly where an
/// application argument would.
fn prec(e: &EcExpr) -> i8 {
    match e {
        EcExpr::Int(n) if *n < 0 => APP_PREC,
        EcExpr::Var(_)
        | EcExpr::Qualified { .. }
        | EcExpr::Int(_)
        | EcExpr::Bool(_)
        | EcExpr::Unit
        | EcExpr::Tuple(_)
        | EcExpr::Proj { .. }
        | EcExpr::Field { .. }
        | EcExpr::RecordLit { .. }
        | EcExpr::None_(_)
        | EcExpr::MapGet { .. }
        | EcExpr::MapSet { .. }
        | EcExpr::MapEmpty
        | EcExpr::Pr { .. } => ATOM_PREC,
        EcExpr::App { args, .. } if args.is_empty() => ATOM_PREC,
        EcExpr::App { .. } | EcExpr::Some_(_) | EcExpr::Oget(_) | EcExpr::MapRem { .. } => {
            APP_PREC
        }
        EcExpr::Unop { .. } => UNOP_PREC,
        EcExpr::Binop { op, .. } => binop_info(*op).1,
        EcExpr::If { .. } | EcExpr::Let { .. } | EcExpr::Quant { .. } => 0,
    }
}

/// Render `e` for a position that requires at least `min_prec`, wrapping in
/// parentheses when `e`'s own precedence is looser.
fn render_operand(e: &EcExpr, min_prec: i8) -> String {
    let text = render_expr_inner(e);
    if prec(e) < min_prec {
        format!("({text})")
    } else {
        text
    }
}

/// `(spelling, precedence level, is right-associative)`.
///
/// This *deviates from the story's "minimum viable" table in one place*:
/// `ecParser.mly`'s `%left`/`%right` declarations put `^^` in the `HAT`
/// operator class, which is tighter than `*` `/` `%` and the comparisons —
/// verified by compiling `a < b ^^ a <= b` unparenthesised, which EasyCrypt
/// groups as `a < (b ^^ a) <= b` and rejects as a type error (`^^` applied
/// to two `int`s, from `b ^^ a`). `Xor` is placed above `Mul`/`Div`/`Mod`
/// here accordingly; every other row matches the story's table and its six
/// required precedence tests.
fn binop_info(op: EcBinop) -> (&'static str, i8, bool) {
    match op {
        EcBinop::Implies => ("=>", 0, true),
        EcBinop::Or => ("\\/", 1, false),
        EcBinop::And => ("/\\", 2, false),
        EcBinop::Eq => ("=", 3, false),
        EcBinop::Ne => ("<>", 3, false),
        EcBinop::Lt => ("<", 4, false),
        EcBinop::Le => ("<=", 4, false),
        EcBinop::Gt => (">", 4, false),
        EcBinop::Ge => (">=", 4, false),
        EcBinop::Add => ("+", 5, false),
        EcBinop::Sub => ("-", 5, false),
        EcBinop::Mul => ("*", 6, false),
        EcBinop::Div => ("%/", 6, false),
        EcBinop::Mod => ("%%", 6, false),
        EcBinop::Xor => ("^^", 7, false),
    }
}

fn render_expr_inner(e: &EcExpr) -> String {
    match e {
        EcExpr::Var(name) => name.clone(),
        EcExpr::Qualified { path, mem } => {
            let base = path.join(".");
            match mem {
                Some(m) => format!("{base}{{{m}}}"),
                None => base,
            }
        }
        EcExpr::Int(n) => n.to_string(),
        EcExpr::Bool(b) => b.to_string(),
        EcExpr::Unit => "tt".to_string(),
        EcExpr::Tuple(items) => {
            let rendered: Vec<String> = items.iter().map(render_expr).collect();
            format!("({})", rendered.join(", "))
        }
        EcExpr::Proj { expr, index } => format!("{}.`{index}", render_operand(expr, ATOM_PREC)),
        EcExpr::Field { expr, field } => format!("{}.`{field}", render_operand(expr, ATOM_PREC)),
        EcExpr::RecordLit { fields } => {
            let rendered: Vec<String> = fields
                .iter()
                .map(|(f, v)| format!("{f} = {}", render_expr(v)))
                .collect();
            format!("{{| {} |}}", rendered.join("; "))
        }
        EcExpr::Some_(inner) => format!("Some {}", render_operand(inner, ATOM_PREC)),
        EcExpr::None_(ty) => format!("None<:{}>", render_type(ty)),
        EcExpr::Oget(inner) => format!("oget {}", render_operand(inner, ATOM_PREC)),
        EcExpr::MapGet { map, key } => {
            format!(
                "{}.[{}]",
                render_operand(map, ATOM_PREC),
                render_expr(key)
            )
        }
        EcExpr::MapSet { map, key, value } => format!(
            "{}.[{} <- {}]",
            render_operand(map, ATOM_PREC),
            render_expr(key),
            render_expr(value)
        ),
        EcExpr::MapRem { map, key } => format!(
            "rem {} {}",
            render_operand(map, ATOM_PREC),
            render_operand(key, ATOM_PREC)
        ),
        EcExpr::MapEmpty => "empty".to_string(),
        EcExpr::App { head, args } => {
            if args.is_empty() {
                head.clone()
            } else {
                let rendered: Vec<String> =
                    args.iter().map(|a| render_operand(a, ATOM_PREC)).collect();
                format!("{head} {}", rendered.join(" "))
            }
        }
        EcExpr::Unop { op, arg } => {
            let sym = match op {
                EcUnop::Not => "!",
                EcUnop::Neg => "-",
            };
            let operand = render_operand(arg, UNOP_PREC);
            if *op == EcUnop::Neg && operand.starts_with('-') {
                format!("{sym} {operand}")
            } else {
                format!("{sym}{operand}")
            }
        }
        EcExpr::Binop { op, lhs, rhs } => {
            let (sym, level, right_assoc) = binop_info(*op);
            // `=`/`<>` are the one row in this table that EasyCrypt's own
            // grammar declares non-associative outright: `a = b = c` is a
            // parse error (`ecParser.mly`), not merely a type error, unlike
            // same-precedence `<`/`<=`/`>`/`>=` chains (those parse, and
            // only fail to typecheck). An `Eq`/`Ne` operand at the same
            // precedence therefore always needs parentheses, on either
            // side — verified by compiling `a = b = c` against
            // `r2026.06-12-g7e192dd` and getting a parse error, surfaced by
            // story 06's `Domino_state_eq` (`(is-mk-none L) = (is-mk-none
            // R)`, where both operands are themselves `=`).
            let (lhs_min, rhs_min) = match op {
                EcBinop::Eq | EcBinop::Ne => (level + 1, level + 1),
                _ if right_assoc => (level + 1, level),
                _ => (level, level + 1),
            };
            format!(
                "{} {sym} {}",
                render_operand(lhs, lhs_min),
                render_operand(rhs, rhs_min)
            )
        }
        EcExpr::If {
            cond,
            then_expr,
            else_expr,
        } => format!(
            "if {} then {} else {}",
            render_expr(cond),
            render_expr(then_expr),
            render_expr(else_expr)
        ),
        EcExpr::Let { name, value, body } => format!(
            "let {name} = {} in {}",
            render_expr(value),
            render_expr(body)
        ),
        EcExpr::Quant {
            kind,
            binders,
            body,
        } => {
            let keyword = match kind {
                Quantifier::Forall => "forall",
                Quantifier::Exists => "exists",
            };
            let rendered_binders: String = binders
                .iter()
                .map(|(n, ty)| format!(" ({n} : {})", render_type(ty)))
                .collect();
            format!(
                "{keyword}{rendered_binders}, {}",
                render_expr(body)
            )
        }
        EcExpr::Pr {
            module,
            proc,
            args,
            memory,
            event,
        } => {
            let rendered_args = args.iter().map(render_expr).collect::<Vec<_>>().join(", ");
            format!(
                "Pr[{module}.{proc}({rendered_args}) @ &{memory} : {}]",
                render_expr(event)
            )
        }
    }
}
