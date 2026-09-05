// SPDX-License-Identifier: MIT OR Apache-2.0

//! What one returning path *computed* — the symbolic return value and the new
//! game state — rendered in terms of the oracle's arguments, the old game state,
//! the game constants and the sample points (story 18).
//!
//! The per-path SMT the executor builds (`src/debug/exec.rs`) is a flat, acyclic,
//! single-assignment conjunction: every `<v!side!n!name>` constant is defined
//! exactly once by an `(assert (= <v!…> <rhs>))`, always after everything `<rhs>`
//! mentions. That means the definitions can simply be **unfolded back to the
//! roots** — [`build`] does exactly that and pretty-prints the result.
//!
//! # Fidelity
//!
//! Everything in [`PathEffect`] is a *rendering*: human-facing and deliberately
//! lossy (`(mk-some x)` in table-value position loses its `Some`, sub-terms get
//! hoisted into `where` names, deep terms are truncated). It is never fed to the
//! solver and no verdict depends on it. When the rendering and the path SMT
//! disagree, the SMT is authoritative and this module has a bug — the viewer
//! says so in a footer.

use std::collections::HashMap;

use serde_derive::Serialize;

use crate::writers::smt::exprs::SmtExpr;

/// A sub-term rendering longer than this is hoisted into a `where` binding when
/// it is reached more than once. Tuned against the story-18 goldens: keeps
/// `old.Prot.ctr` (12 chars, four uses) inline while
/// `encaps(old.Prot.pk, rand#0).1` (three uses) gets a name.
pub const INLINE_MAX_CHARS: usize = 12;
/// Hard cap on any single rendered string. On overflow the term is cut with `…`
/// and [`PathEffect::truncated`] is set — the only defence against a
/// pathological deep path; it must never abort a run.
pub const MAX_TERM_CHARS: usize = 2000;
/// Hard cap on the number of hoisted `where` bindings.
pub const MAX_WHERES: usize = 40;
/// Hard cap on renderer recursion depth — a pathologically deep path is cut
/// with `…` rather than overflowing the stack. Far beyond any real oracle
/// (the whole corpus nests < 30 deep).
const MAX_DEPTH: usize = 400;

/// What one returning path computed, expressed over the oracle's arguments, the
/// old game state, the game constants and the sample points.
///
/// Every string in here is a *rendering* — human-facing, deliberately lossy (see
/// the module docs). The authoritative encoding is the path's SMT.
#[derive(Debug, Clone, Serialize)]
pub struct PathEffect {
    /// The rendered return value. `None` for `return` with no value (rendered as
    /// `()` by the viewer) — this whole struct is `None` for an abort.
    pub returns: Option<String>,
    /// One entry per folded package instance, in game-declaration order.
    pub state: Vec<PkgEffect>,
    /// Sample points whose counter advanced, in sample-id order.
    pub rand: Vec<RandEffect>,
    /// Shared sub-terms hoisted out of the strings above, in dependency order.
    pub wheres: Vec<Binding>,
    /// A term hit [`MAX_TERM_CHARS`] / [`MAX_WHERES`] and was elided with `…`.
    pub truncated: bool,
}

#[derive(Debug, Clone, Serialize)]
pub struct PkgEffect {
    pub pkg_inst: String,
    /// Fields whose final SSA constant differs from the seeded one, in package
    /// declaration order.
    pub changed: Vec<FieldEffect>,
    /// Field names still bound to their seed, in package declaration order.
    pub unchanged: Vec<String>,
}

#[derive(Debug, Clone, Serialize)]
pub struct FieldEffect {
    pub field: String,
    /// The flat rendering, e.g. `old.Prot.SENTCTXT[old.Prot.ctr -> ctxt]`.
    pub value: String,
    /// Set when `value` is a `store` chain, so the viewer can put one entry per
    /// line for a wide table. `base` is the rendered chain base.
    pub table: Option<TableUpdate>,
}

#[derive(Debug, Clone, Serialize)]
pub struct TableUpdate {
    pub base: String,
    pub entries: Vec<Entry>,
}

#[derive(Debug, Clone, Serialize)]
pub struct Entry {
    pub key: String,
    pub value: String,
}

#[derive(Debug, Clone, Serialize)]
pub struct RandEffect {
    /// `Prot.Run.encaps_rand`
    pub point: String,
    /// Rendered type, e.g. `Bits(256)`.
    pub ty: String,
    /// How many draws this path made.
    pub draws: usize,
}

#[derive(Debug, Clone, Serialize)]
pub struct Binding {
    pub name: String,
    pub value: String,
}

/// One folded package instance's fields, as handed to [`build`].
pub struct PkgInput {
    pub pkg_inst: String,
    /// `(field name, final SSA constant string)` for fields whose final constant
    /// differs from the seed, in package declaration order.
    pub changed: Vec<(String, String)>,
    /// Field names still bound to their seed, in package declaration order.
    pub unchanged: Vec<String>,
}

/// Everything [`build`] needs. `def_map` and `roots` come from the terminal's
/// `SymState`; `returns` is `to_smt(&st, e)` of the terminal's return value.
pub struct EffectInput<'a> {
    pub returns: Option<SmtExpr>,
    pub pkgs: Vec<PkgInput>,
    pub rand: Vec<RandEffect>,
    /// `<v!…>` constant name → its defining right-hand side.
    pub def_map: &'a HashMap<String, SmtExpr>,
    /// `<v!…>` constant name → its rendered root form (`old.I.f`, a const name,
    /// or an argument name). These are never unfolded further.
    pub roots: &'a HashMap<String, String>,
}

/// Strip the `<`…`>` (or `<<`…`>>`) name brackets an SMT identifier carries.
fn unbracket(s: &str) -> &str {
    s.trim_start_matches('<').trim_end_matches('>')
}

/// The source basename of an SSA constant: `<v!left!25!ctxt>` → `ctxt`.
fn ssa_basename(s: &str) -> &str {
    unbracket(s).rsplit('!').next().unwrap_or(s)
}

fn is_ssa(s: &str) -> bool {
    s.starts_with("<v!")
}

fn atom(e: &SmtExpr) -> Option<&str> {
    match e {
        SmtExpr::Atom(a) => Some(a.as_str()),
        _ => None,
    }
}

/// `elN-i` → `(N, i)` (both as written, `i` 1-based).
fn parse_el(head: &str) -> Option<(usize, usize)> {
    let rest = head.strip_prefix("el")?;
    let (n, i) = rest.split_once('-')?;
    Some((n.parse().ok()?, i.parse().ok()?))
}

fn parse_tuple_arity(head: &str) -> Option<usize> {
    head.strip_prefix("mk-tuple")?.parse().ok()
}

/// Render the effect of one returning path.
pub fn build(input: EffectInput<'_>) -> PathEffect {
    let sample_ty: HashMap<String, String> = input
        .rand
        .iter()
        .map(|r| (r.point.clone(), r.ty.clone()))
        .collect();

    let mut r = Renderer {
        def_map: input.def_map,
        roots: input.roots,
        sample_ty: &sample_ty,
        counts: HashMap::new(),
        wheres: Vec::new(),
        where_of: HashMap::new(),
        name_taken: HashMap::new(),
        truncated: false,
        depth: 0,
    };

    // Pass 1 — reference counting over every root.
    if let Some(ret) = &input.returns {
        r.count(ret);
    }
    for pkg in &input.pkgs {
        for (_, ssa) in &pkg.changed {
            r.count(&SmtExpr::Atom(ssa.clone()));
        }
    }

    // Pass 2 — render.
    let returns = input.returns.as_ref().map(|e| r.render(e));
    let state = input
        .pkgs
        .iter()
        .map(|pkg| PkgEffect {
            pkg_inst: pkg.pkg_inst.clone(),
            changed: pkg
                .changed
                .iter()
                .map(|(field, ssa)| r.render_field(field, ssa))
                .collect(),
            unchanged: pkg.unchanged.clone(),
        })
        .collect();

    PathEffect {
        returns,
        state,
        rand: input.rand,
        wheres: r.wheres,
        truncated: r.truncated,
    }
}

struct Renderer<'a> {
    def_map: &'a HashMap<String, SmtExpr>,
    roots: &'a HashMap<String, String>,
    sample_ty: &'a HashMap<String, String>,
    counts: HashMap<String, usize>,
    wheres: Vec<Binding>,
    where_of: HashMap<String, String>,
    name_taken: HashMap<String, String>,
    truncated: bool,
    depth: usize,
}

impl<'a> Renderer<'a> {
    /// Follow `Atom` → definition transitively (but never through a root or a
    /// bare sample point), so `elN-i` reduction can see a `mk-tupleN` that hides
    /// behind an SSA name.
    fn resolve<'e>(&'e self, e: &'e SmtExpr) -> &'e SmtExpr {
        let mut cur = e;
        loop {
            let Some(a) = atom(cur) else { return cur };
            if self.roots.contains_key(a) {
                return cur;
            }
            match self.def_map.get(a) {
                Some(next) => cur = next,
                None => return cur,
            }
        }
    }

    // ---- pass 1 -----------------------------------------------------------
    fn count(&mut self, e: &SmtExpr) {
        if self.depth >= MAX_DEPTH {
            return;
        }
        self.depth += 1;
        self.count_dispatch(e);
        self.depth -= 1;
    }

    fn count_dispatch(&mut self, e: &SmtExpr) {
        match e {
            SmtExpr::Atom(a) => {
                if self.roots.contains_key(a) {
                    return;
                }
                if let Some(def) = self.def_map.get(a) {
                    let c = self.counts.entry(a.clone()).or_insert(0);
                    *c += 1;
                    if *c == 1 {
                        let def = def.clone();
                        self.count(&def);
                    }
                }
            }
            SmtExpr::List(items) => {
                if items.is_empty() {
                    return;
                }
                if let Some(head) = atom(&items[0]) {
                    if let Some((_, i)) = parse_el(head) {
                        if items.len() == 2 {
                            let arg = self.resolve(&items[1]).clone();
                            if let SmtExpr::List(t) = &arg {
                                if let Some(n) = t.first().and_then(atom).and_then(parse_tuple_arity) {
                                    if n + 1 == t.len() && i >= 1 && i <= n {
                                        let elem = t[i].clone();
                                        self.count(&elem);
                                        return;
                                    }
                                }
                            }
                            self.count(&items[1]);
                            return;
                        }
                    }
                }
                for it in items.iter().skip(1) {
                    self.count(it);
                }
            }
            SmtExpr::Comment(_) => {}
        }
    }

    // ---- pass 2 ---------------------------------------------------------
    fn cap(&mut self, s: String) -> String {
        if s.chars().count() > MAX_TERM_CHARS {
            self.truncated = true;
            let mut out: String = s.chars().take(MAX_TERM_CHARS).collect();
            out.push('…');
            out
        } else {
            s
        }
    }

    /// A fresh, collision-free `where` name derived from an SSA basename.
    fn where_name(&mut self, ssa: &str) -> String {
        let base = ssa_basename(ssa).to_string();
        let mut name = base.clone();
        let mut n = 2;
        while matches!(self.name_taken.get(&name), Some(owner) if owner != ssa) {
            name = format!("{base}#{n}");
            n += 1;
        }
        self.name_taken.insert(name.clone(), ssa.to_string());
        name
    }

    fn push_where(&mut self, name: String, value: String) {
        if self.wheres.iter().any(|b| b.name == name) {
            return;
        }
        if self.wheres.len() >= MAX_WHERES {
            self.truncated = true;
            return;
        }
        self.wheres.push(Binding { name, value });
    }

    /// `(__sample-rand-{GI}-{ty} (sample-id "I" "O" "name") i)` → the hoisted
    /// name `name#i`, spelled out in a `where` line.
    fn sample_binding(&mut self, ssa: Option<&str>, items: &[SmtExpr]) -> Option<String> {
        let sid = match items.get(1) {
            Some(SmtExpr::List(l)) if l.first().and_then(atom) == Some("sample-id") => l,
            _ => return None,
        };
        let strip = |e: &SmtExpr| atom(e).map(|s| s.trim_matches('"').to_string());
        let inst = strip(sid.get(1)?)?;
        let oracle = strip(sid.get(2)?)?;
        let sname = strip(sid.get(3)?)?;
        let idx = atom(items.get(2)?)?.to_string();
        let point = format!("{inst}.{oracle}.{sname}");
        let base = ssa.map(ssa_basename).unwrap_or(&sname);
        let name = format!("{base}#{idx}");
        let ty = self
            .sample_ty
            .get(&point)
            .cloned()
            .unwrap_or_else(|| "?".to_string());
        self.push_where(name.clone(), format!("sample {ty} @ {point} #{idx}"));
        Some(name)
    }

    fn render(&mut self, e: &SmtExpr) -> String {
        let s = self.render_inner(e);
        self.cap(s)
    }

    fn render_inner(&mut self, e: &SmtExpr) -> String {
        if self.depth >= MAX_DEPTH {
            self.truncated = true;
            return "…".to_string();
        }
        self.depth += 1;
        let r = self.render_dispatch(e);
        self.depth -= 1;
        r
    }

    fn render_dispatch(&mut self, e: &SmtExpr) -> String {
        match e {
            SmtExpr::Atom(a) => {
                if let Some(root) = self.roots.get(a) {
                    return root.clone();
                }
                if !is_ssa(a) || !self.def_map.contains_key(a) {
                    return unbracket(a).to_string();
                }
                if let Some(name) = self.where_of.get(a) {
                    return name.clone();
                }
                let def = self.def_map.get(a).unwrap().clone();
                // A bare sample draw is always named.
                if let SmtExpr::List(items) = &def {
                    if items.first().and_then(atom).is_some_and(|h| h.starts_with("__sample-rand-")) {
                        if let Some(name) = self.sample_binding(Some(a), items) {
                            self.where_of.insert(a.clone(), name.clone());
                            return name;
                        }
                    }
                }
                let rendered = self.render_inner(&def);
                let hoist = self.counts.get(a).copied().unwrap_or(0) >= 2
                    && rendered.chars().count() > INLINE_MAX_CHARS;
                if hoist {
                    let name = self.where_name(a);
                    self.where_of.insert(a.clone(), name.clone());
                    self.push_where(name.clone(), rendered);
                    name
                } else {
                    rendered
                }
            }
            SmtExpr::Comment(_) => String::new(),
            SmtExpr::List(items) => {
                if items.is_empty() {
                    return "()".to_string();
                }
                // `((as const (Array …)) mk-none)` — the empty table.
                if items.len() == 2 {
                    if let SmtExpr::List(h) = &items[0] {
                        if h.first().and_then(atom) == Some("as")
                            && h.get(1).and_then(atom) == Some("const")
                        {
                            return "{}".to_string();
                        }
                    }
                }
                let Some(head) = atom(&items[0]).map(str::to_string) else {
                    // head is itself a compound term — render generically.
                    let parts: Vec<String> = items.iter().map(|x| self.render_inner(x)).collect();
                    return format!("({})", parts.join(" "));
                };
                self.render_list(&head, items)
            }
        }
    }

    fn render_list(&mut self, head: &str, items: &[SmtExpr]) -> String {
        let arg = |r: &mut Self, i: usize| r.render_inner(&items[i]);
        match head {
            "store" if items.len() == 4 => self.render_store(&items[0], &items[1..]),
            "select" if items.len() == 3 => format!("{}[{}]", arg(self, 1), arg(self, 2)),
            "mk-some" if items.len() == 2 => format!("Some({})", arg(self, 1)),
            "mk-none" => "None".to_string(),
            "as" if items.len() == 3 => {
                if atom(&items[1]) == Some("mk-none") {
                    "None".to_string()
                } else {
                    arg(self, 1)
                }
            }
            "maybe-get" if items.len() == 2 => format!("unwrap({})", arg(self, 1)),
            "not" if items.len() == 2 => {
                if let SmtExpr::List(inner) = &items[1] {
                    if inner.first().and_then(atom) == Some("=") && inner.len() == 3 {
                        return format!(
                            "{} != {}",
                            self.render_inner(&inner[1]),
                            self.render_inner(&inner[2])
                        );
                    }
                }
                format!("!{}", arg(self, 1))
            }
            "=" if items.len() == 3 => format!("{} == {}", arg(self, 1), arg(self, 2)),
            "and" | "or" if items.len() >= 2 => {
                let op = if head == "and" { " && " } else { " || " };
                let parts: Vec<String> =
                    items[1..].iter().map(|x| self.render_inner(x)).collect();
                format!("({})", parts.join(op))
            }
            "+" | "-" | "*" if items.len() >= 3 => {
                let parts: Vec<String> =
                    items[1..].iter().map(|x| self.render_inner(x)).collect();
                parts.join(&format!(" {head} "))
            }
            "ite" if items.len() == 4 => format!(
                "if {} then {} else {}",
                arg(self, 1),
                arg(self, 2),
                arg(self, 3)
            ),
            "__sample-rand-" => arg(self, 1),
            _ if head.starts_with("__sample-rand-") => self
                .sample_binding(None, items)
                .unwrap_or_else(|| self.render_generic(head, items)),
            _ => {
                if let Some((n, i)) = parse_el(head) {
                    if items.len() == 2 {
                        let resolved = self.resolve(&items[1]).clone();
                        if let SmtExpr::List(t) = &resolved {
                            if t.first().and_then(atom).and_then(parse_tuple_arity) == Some(n)
                                && n + 1 == t.len()
                                && i >= 1
                                && i <= n
                            {
                                let elem = t[i].clone();
                                return self.render_inner(&elem);
                            }
                        }
                        return format!("{}.{}", arg(self, 1), i);
                    }
                }
                if parse_tuple_arity(head).is_some() {
                    let parts: Vec<String> =
                        items[1..].iter().map(|x| self.render_inner(x)).collect();
                    return format!("({})", parts.join(", "));
                }
                self.render_generic(head, items)
            }
        }
    }

    /// `head(arg, …)` with the name brackets stripped. `<<func-encaps>>` →
    /// `encaps`; anything else keeps its inner text.
    fn render_generic(&mut self, head: &str, items: &[SmtExpr]) -> String {
        let name = unbracket(head)
            .strip_prefix("func-")
            .map(str::to_string)
            .unwrap_or_else(|| unbracket(head).to_string());
        if items.len() == 1 {
            return name;
        }
        let parts: Vec<String> = items[1..].iter().map(|x| self.render_inner(x)).collect();
        format!("{name}({})", parts.join(", "))
    }

    /// Flatten a `(store (store … ) k v)` chain: the base once, then the
    /// updates in write order (innermost = first written).
    fn render_store(&mut self, base: &SmtExpr, kv: &[SmtExpr]) -> String {
        let (base_str, mut entries) = self.flatten_store(base);
        entries.push(Entry {
            key: self.render_inner(&kv[0]),
            value: self.render_value_pos(&kv[1]),
        });
        let body: Vec<String> = entries
            .iter()
            .map(|e| format!("{} -> {}", e.key, e.value))
            .collect();
        format!("{base_str}[{}]", body.join(", "))
    }

    fn flatten_store(&mut self, e: &SmtExpr) -> (String, Vec<Entry>) {
        let resolved = self.resolve(e).clone();
        if let SmtExpr::List(items) = &resolved {
            if items.first().and_then(atom) == Some("store") && items.len() == 4 {
                let (base, mut entries) = self.flatten_store(&items[1]);
                entries.push(Entry {
                    key: self.render_inner(&items[2]),
                    value: self.render_value_pos(&items[3]),
                });
                return (base, entries);
            }
        }
        (self.render_inner(e), Vec::new())
    }

    /// A table value is a `Maybe` in SMT; in value position strip one `mk-some`
    /// (`k -> v`, not `k -> Some(v)`) and render `mk-none` as an explicit delete.
    fn render_value_pos(&mut self, e: &SmtExpr) -> String {
        let resolved = self.resolve(e).clone();
        if let SmtExpr::List(items) = &resolved {
            match items.first().and_then(atom) {
                Some("mk-some") if items.len() == 2 => return self.render_inner(&items[1]),
                Some("as") if items.len() == 3 && atom(&items[1]) == Some("mk-none") => {
                    return "None".to_string()
                }
                _ => {}
            }
        }
        if atom(&resolved) == Some("mk-none") {
            return "None".to_string();
        }
        self.render_inner(e)
    }

    fn render_field(&mut self, field: &str, ssa: &str) -> FieldEffect {
        let e = SmtExpr::Atom(ssa.to_string());
        let resolved = self.resolve(&e).clone();
        let is_store = matches!(&resolved,
            SmtExpr::List(items) if items.first().and_then(atom) == Some("store") && items.len() == 4);
        if is_store {
            if let SmtExpr::List(items) = &resolved {
                let (base, mut entries) = self.flatten_store(&items[1]);
                entries.push(Entry {
                    key: self.render_inner(&items[2]),
                    value: self.render_value_pos(&items[3]),
                });
                let body: Vec<String> = entries
                    .iter()
                    .map(|en| format!("{} -> {}", en.key, en.value))
                    .collect();
                let value = self.cap(format!("{base}[{}]", body.join(", ")));
                return FieldEffect {
                    field: field.to_string(),
                    value,
                    table: Some(TableUpdate { base, entries }),
                };
            }
        }
        FieldEffect {
            field: field.to_string(),
            value: self.render(&e),
            table: None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn a(s: &str) -> SmtExpr {
        SmtExpr::Atom(s.to_string())
    }
    fn l(items: Vec<SmtExpr>) -> SmtExpr {
        SmtExpr::List(items)
    }

    struct Fix {
        def: HashMap<String, SmtExpr>,
        roots: HashMap<String, String>,
    }
    impl Fix {
        fn new() -> Self {
            Fix {
                def: HashMap::new(),
                roots: HashMap::new(),
            }
        }
        fn def(&mut self, name: &str, rhs: SmtExpr) -> &mut Self {
            self.def.insert(name.to_string(), rhs);
            self
        }
        fn root(&mut self, name: &str, rendered: &str) -> &mut Self {
            self.roots.insert(name.to_string(), rendered.to_string());
            self
        }
        fn build(&self, returns: Option<SmtExpr>, pkgs: Vec<PkgInput>) -> PathEffect {
            super::build(EffectInput {
                returns,
                pkgs,
                rand: Vec::new(),
                def_map: &self.def,
                roots: &self.roots,
            })
        }
        fn field(&self, ssa: &str) -> FieldEffect {
            let e = self.build(
                None,
                vec![PkgInput {
                    pkg_inst: "P".into(),
                    changed: vec![("f".into(), ssa.to_string())],
                    unchanged: vec![],
                }],
            );
            e.state.into_iter().next().unwrap().changed.into_iter().next().unwrap()
        }
    }

    #[test]
    fn store_chain_single() {
        let mut f = Fix::new();
        f.root("<v!left!0!f>", "old.P.f")
            .root("<v!left!1!k>", "old.P.ctr")
            .root("<v!left!2!v>", "ctxt")
            .def(
                "<v!left!3!f>",
                l(vec![a("store"), a("<v!left!0!f>"), a("<v!left!1!k>"), l(vec![a("mk-some"), a("<v!left!2!v>")])]),
            );
        let fe = f.field("<v!left!3!f>");
        assert_eq!(fe.value, "old.P.f[old.P.ctr -> ctxt]");
        let t = fe.table.unwrap();
        assert_eq!(t.base, "old.P.f");
        assert_eq!(t.entries.len(), 1);
        assert_eq!(t.entries[0].key, "old.P.ctr");
        assert_eq!(t.entries[0].value, "ctxt");
    }

    #[test]
    fn store_chain_nested_and_repeated_key() {
        let mut f = Fix::new();
        f.root("<v!left!0!f>", "old.P.f").root("<v!left!1!k>", "k");
        f.def(
            "<v!left!2!f>",
            l(vec![a("store"), a("<v!left!0!f>"), a("<v!left!1!k>"), l(vec![a("mk-some"), a("1")])]),
        );
        f.def(
            "<v!left!3!f>",
            l(vec![a("store"), a("<v!left!2!f>"), a("<v!left!1!k>"), l(vec![a("mk-some"), a("2")])]),
        );
        let fe = f.field("<v!left!3!f>");
        assert_eq!(fe.value, "old.P.f[k -> 1, k -> 2]");
    }

    #[test]
    fn store_on_empty_base() {
        let mut f = Fix::new();
        f.root("<v!left!1!k>", "k");
        let empty = l(vec![l(vec![a("as"), a("const"), a("(Array Int (Maybe Int))")]), a("mk-none")]);
        f.def(
            "<v!left!2!f>",
            l(vec![a("store"), empty, a("<v!left!1!k>"), l(vec![a("mk-some"), a("7")])]),
        );
        assert_eq!(f.field("<v!left!2!f>").value, "{}[k -> 7]");
    }

    #[test]
    fn store_value_none_is_delete() {
        let mut f = Fix::new();
        f.root("<v!left!0!f>", "old.P.f").root("<v!left!1!k>", "k");
        f.def(
            "<v!left!2!f>",
            l(vec![a("store"), a("<v!left!0!f>"), a("<v!left!1!k>"), l(vec![a("as"), a("mk-none"), a("(Maybe Int)")])]),
        );
        assert_eq!(f.field("<v!left!2!f>").value, "old.P.f[k -> None]");
    }

    #[test]
    fn el_of_tuple_reduces() {
        let mut f = Fix::new();
        f.root("<v!r!0!a>", "aa").root("<v!r!1!b>", "bb").root("<v!r!2!c>", "cc");
        f.def(
            "<v!r!3!ret>",
            l(vec![a("mk-tuple3"), a("<v!r!0!a>"), a("<v!r!1!b>"), a("<v!r!2!c>")]),
        );
        f.def("<v!r!4!x>", l(vec![a("el3-2"), a("<v!r!3!ret>")]));
        let e = f.build(Some(a("<v!r!4!x>")), vec![]);
        assert_eq!(e.returns.unwrap(), "bb");
        // `ret` never surfaces.
        assert!(e.wheres.iter().all(|w| w.name != "ret"));
    }

    #[test]
    fn el_of_non_tuple_is_dot_index() {
        let mut f = Fix::new();
        f.root("<v!l!0!pk>", "old.P.pk").root("<v!l!1!r>", "r");
        f.def(
            "<v!l!2!x>",
            l(vec![a("el2-1"), l(vec![a("<<func-encaps>>"), a("<v!l!0!pk>"), a("<v!l!1!r>")])]),
        );
        assert_eq!(f.build(Some(a("<v!l!2!x>")), vec![]).returns.unwrap(), "encaps(old.P.pk, r).1");
    }

    #[test]
    fn maybe_get_and_accessors() {
        let mut f = Fix::new();
        f.root("<v!l!0!sk>", "old.P.sk");
        f.def("<v!l!1!u>", l(vec![a("maybe-get"), a("<v!l!0!sk>")]));
        assert_eq!(f.build(Some(a("<v!l!1!u>")), vec![]).returns.unwrap(), "unwrap(old.P.sk)");
    }

    #[test]
    fn arg_name_passes_through() {
        let mut f = Fix::new();
        f.root("<v!l!0!m0>", "m0");
        f.def("<v!l!1!x>", a("<v!l!0!m0>"));
        assert_eq!(f.build(Some(a("<v!l!1!x>")), vec![]).returns.unwrap(), "m0");
    }

    #[test]
    fn sample_inline_vs_where() {
        // one use → still hoisted (sample draws are always named)
        let mut f = Fix::new();
        f.def(
            "<v!l!0!rand>",
            l(vec![
                a("__sample-rand-GI-Bits_256"),
                l(vec![a("sample-id"), a("\"I\""), a("\"O\""), a("\"encaps_rand\"")]),
                a("0"),
            ]),
        );
        let e = super::build(EffectInput {
            returns: Some(a("<v!l!0!rand>")),
            pkgs: vec![],
            rand: vec![RandEffect { point: "I.O.encaps_rand".into(), ty: "Bits(256)".into(), draws: 1 }],
            def_map: &f.def,
            roots: &f.roots,
        });
        assert_eq!(e.returns.unwrap(), "rand#0");
        assert_eq!(e.wheres.len(), 1);
        assert_eq!(e.wheres[0].name, "rand#0");
        assert_eq!(e.wheres[0].value, "sample Bits(256) @ I.O.encaps_rand #0");
    }

    #[test]
    fn hoisting_threshold() {
        // a 13-char rendering used twice is hoisted; 12 is not.
        let mut f = Fix::new();
        f.root("<v!l!0!a>", "aaaaaaaaaaaaa"); // 13
        f.root("<v!l!1!b>", "bbbbbbbbbbbb"); // 12
        f.def("<v!l!2!x>", a("<v!l!0!a>"));
        f.def("<v!l!3!y>", a("<v!l!1!b>"));
        f.def("<v!l!4!p>", l(vec![a("mk-tuple2"), a("<v!l!2!x>"), a("<v!l!2!x>")]));
        f.def("<v!l!5!q>", l(vec![a("mk-tuple2"), a("<v!l!3!y>"), a("<v!l!3!y>")]));
        let e = f.build(Some(l(vec![a("mk-tuple2"), a("<v!l!4!p>"), a("<v!l!5!q>")])), vec![]);
        // x used twice, 13 chars → hoisted; y used twice, 12 chars → inline.
        assert!(e.wheres.iter().any(|w| w.value == "aaaaaaaaaaaaa"));
        assert!(e.wheres.iter().all(|w| w.value != "bbbbbbbbbbbb"));
    }

    #[test]
    fn name_collision_disambiguated() {
        let mut f = Fix::new();
        // two distinct SSA names with the same basename `t`, both long, both used twice
        f.root("<v!l!0!p>", "old.P.pp").root("<v!l!1!q>", "old.P.qq");
        f.def("<v!l!2!t>", l(vec![a("<<func-f>>"), a("<v!l!0!p>"), a("<v!l!0!p>")]));
        f.def("<v!l!3!t>", l(vec![a("<<func-g>>"), a("<v!l!1!q>"), a("<v!l!1!q>")]));
        f.def("<v!l!4!u>", l(vec![a("mk-tuple2"), a("<v!l!2!t>"), a("<v!l!2!t>")]));
        f.def("<v!l!5!w>", l(vec![a("mk-tuple2"), a("<v!l!3!t>"), a("<v!l!3!t>")]));
        let e = f.build(Some(l(vec![a("mk-tuple2"), a("<v!l!4!u>"), a("<v!l!5!w>")])), vec![]);
        let names: Vec<_> = e.wheres.iter().map(|w| w.name.clone()).collect();
        assert!(names.contains(&"t".to_string()));
        assert!(names.contains(&"t#2".to_string()));
    }

    #[test]
    fn truncation_sets_flag_no_panic() {
        let mut f = Fix::new();
        f.root("<v!l!0!x>", "x");
        // build a deeply nested + term
        let mut e = a("<v!l!0!x>");
        for _ in 0..1000 {
            e = l(vec![a("+"), e, a("1")]);
        }
        f.def("<v!l!1!big>", e);
        let out = f.build(Some(a("<v!l!1!big>")), vec![]);
        assert!(out.truncated);
        assert!(out.returns.unwrap().contains('…'));
    }

    #[test]
    fn unknown_head_degrades() {
        let mut f = Fix::new();
        f.root("<v!l!0!x>", "x");
        f.def("<v!l!1!y>", l(vec![a("<weird-new-op>"), a("<v!l!0!x>"), a("3")]));
        assert_eq!(f.build(Some(a("<v!l!1!y>")), vec![]).returns.unwrap(), "weird-new-op(x, 3)");
    }

    #[test]
    fn unchanged_fields_listed_verbatim() {
        let f = Fix::new();
        let e = f.build(
            None,
            vec![PkgInput {
                pkg_inst: "Prot".into(),
                changed: vec![],
                unchanged: vec!["TESTED".into(), "sk".into(), "pk".into()],
            }],
        );
        assert_eq!(e.state[0].unchanged, vec!["TESTED", "sk", "pk"]);
        assert!(e.state[0].changed.is_empty());
    }
}
