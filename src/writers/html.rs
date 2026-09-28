// SPDX-License-Identifier: MIT OR Apache-2.0

//! `domino html`: one self-contained HTML page per theorem.
//!
//! The page has one tab per proposition. A tab is a grid with one column per
//! game instance on the path [`Proof::try_new`] finds from the proposition's
//! left game to its right game (in path order, with the hop between each pair
//! of neighbours), and one row per exported oracle. The header cell of each
//! column is the game's composition diagram; every other cell is the oracle
//! fully inlined across package boundaries — the same listing `domino inline`
//! prints, in both a full and a lossy rendering the page toggles between.
//! A theorem without propositions gets a single tab over its game hops.
//!
//! The diagram reuses the solver-based layout the LaTeX export uses
//! ([`GraphLayout`]), translated to inline SVG with the same geometry as the
//! tikz output. Without a solver (or when layout fails) a simple layered
//! fallback is drawn. Boolean package parameters are shown as a superscript on
//! the package instance (`true` → 1, `false` → 0; hover for `name = value`),
//! with the path's constant specialization applied. Every Boolean is coloured
//! by where its value comes from ([`BitSource`]): fixed in the game, set by the
//! theorem's game instance, or a proof parameter.

use std::collections::{BTreeMap, HashMap};
use std::fmt::Write as _;
use std::path::Path;

use crate::debug::ir::{render_expr, render_oracle_listing};
use crate::expressions::{Expression, ExpressionKind};
use crate::gamehops::GameHop;
use crate::identifier::{game_ident::GameIdentifier, theorem_ident::TheoremIdentifier, Identifier};
use crate::package::Composition;
use crate::packageinstance::PackageInstance;
use crate::proof::ConstAssignment;
use crate::theorem::{GameInstance, Theorem};
use crate::transforms::theorem_transforms::{EquivalenceTransformError, ViewTransform};
use crate::transforms::TheoremTransform;
use crate::types::TypeKind;
use crate::util::smtsolver::SmtSolverBackend;
use crate::writers::util::graph::GraphLayout;

/// Pixels per tikz unit (1cm in the LaTeX export).
const SCALE: f64 = 50.0;
/// Package box width and column pitch, in tikz units (as in `tikzgraph.rs`).
const BOX_WIDTH: f64 = 2.0;
const COLUMN_PITCH: f64 = 3.5;

/// One column of a tab: a game instance, the constants the proof path fixes
/// for it, and the hop that led here from the previous column.
struct Step<'t> {
    game: &'t GameInstance,
    /// `(theorem-level name, assigned literal)`.
    assignments: Vec<(String, String)>,
    via: Option<&'t GameHop<'t>>,
}

/// One tab of the page.
struct Tab<'t> {
    title: String,
    subtitle: String,
    steps: Vec<Step<'t>>,
}

/// Both renderings of one inlined oracle, or why it could not be inlined.
struct Listings {
    full: Result<String, String>,
    lossy: Result<String, String>,
}

/// Render the HTML page for `theorem` (the *untransformed* theorem).
///
/// `backend` lays out the composition diagrams; `graph_cache` is where the
/// layouts are cached (shared with the LaTeX export's format). `lossy` picks
/// the listing rendering the page opens with.
pub fn render_theorem_html<B: SmtSolverBackend>(
    theorem: &Theorem,
    backend: Option<&B>,
    graph_cache: &Path,
    lossy: bool,
) -> Result<String, EquivalenceTransformError> {
    let (theorem_dbg, _aux) = ViewTransform.transform_theorem(theorem)?;
    let tabs = tabs(theorem);

    let mut listings: HashMap<(String, String), Listings> = HashMap::new();
    let mut out = String::new();
    let _ = write!(
        out,
        "<!doctype html>\n<html lang=\"en\"><head><meta charset=\"utf-8\">\
         <meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\
         <title>{name}</title><style>{STYLE}</style></head>\
         <body class=\"{body_class}\">\n<header>\n\
         <div class=\"titlebar\"><h1>theorem <code>{name}</code></h1>\
         <div class=\"tools\">\
         <label><input type=\"checkbox\" id=\"opt-lossy\"> lossy</label>\
         <label><input type=\"checkbox\" id=\"opt-wrap\"> wrap lines</label>\
         <span class=\"zoom\"><button id=\"zoom-out\" title=\"smaller code\">A−</button>\
         <button id=\"zoom-in\" title=\"larger code\">A+</button></span>\
         <button id=\"pp-toggle\" title=\"show / hide the package pane\">packages</button>\
         <span class=\"legend\" title=\"colour of Boolean parameters: fixed in the game definition, \
         set by the theorem's game instance, or a proof parameter\">bits:\
         <b class=\"b-fixed\">fixed</b><b class=\"b-inst\">instance</b><b class=\"b-proof\">proof</b></span>\
         <span class=\"hint\"><kbd>←</kbd><kbd>→</kbd> previous / next game · click a package for its code</span>\
         </div></div>\n",
        name = esc(&theorem.name),
        body_class = if lossy { "show-lossy" } else { "" },
    );

    let _ = write!(out, "<nav class=\"tabs\">");
    for (t, tab) in tabs.iter().enumerate() {
        let _ = write!(
            out,
            "<button class=\"tab\" data-tab=\"{t}\"><b>{}</b> <span>{}</span></button>",
            esc(&tab.title),
            esc(&tab.subtitle),
        );
    }
    out.push_str("</nav>\n");

    out.push_str("<details class=\"hops\"><summary>all game hops</summary><ol start=\"0\">");
    for hop in &theorem.game_hops {
        let _ = write!(
            out,
            "<li><span class=\"kind\">{}</span> <code>{}</code></li>",
            hop_kind(hop),
            esc(&hop.to_string()),
        );
    }
    out.push_str("</ol></details>\n</header>\n");

    for (t, tab) in tabs.iter().enumerate() {
        let _ = writeln!(out, "<section class=\"tabpane\" data-tab=\"{t}\">");

        // The path as a clickable breadcrumb: one chip per column, the hop
        // between neighbours in between.
        out.push_str("<nav class=\"path\">");
        for (c, step) in tab.steps.iter().enumerate() {
            if let Some(hop) = step.via {
                let _ = write!(
                    out,
                    "<span class=\"via\" title=\"{}\">{}</span>",
                    esc(&hop.to_string()),
                    hop_kind(hop),
                );
            }
            let _ = write!(
                out,
                "<button class=\"chip\" data-col=\"{c}\">{}{}</button>",
                esc(step.game.name()),
                specialization_html(&step.assignments),
            );
        }
        out.push_str("</nav>\n");

        let oracles = oracles_in_order(tab.steps.iter().map(|s| s.game));

        out.push_str("<div class=\"scroller\"><table>\n<thead><tr><th class=\"corner\"></th>");
        let n = tab.steps.len();
        for (c, step) in tab.steps.iter().enumerate() {
            let via = match step.via {
                Some(hop) => format!(
                    "<div class=\"gsub\">via {} <code>{}</code></div>",
                    hop_kind(hop),
                    esc(&hop.to_string())
                ),
                None => String::new(),
            };
            let _ = write!(
                out,
                "<th class=\"col\" data-col=\"{c}\"><div class=\"gname\">\
                 <span class=\"idx\">{}/{n}</span> {}{}{}</div>\
                 <div class=\"gsub\">game <code>{}</code></div>{via}</th>",
                c + 1,
                esc(step.game.name()),
                game_bits_html(&game_bits(step.game)),
                specialization_html(&step.assignments),
                esc(step.game.game_name()),
            );
        }
        out.push_str("</tr>\n<tr class=\"diagrams\"><th class=\"corner\"></th>");
        for step in &tab.steps {
            let _ = write!(out, "<td data-game=\"{}\">", esc(step.game.name()));
            out.push_str(&bits_caption(&game_bits(step.game), &step.assignments));
            out.push_str(&diagram_svg(
                step.game.game(),
                &step.assignments,
                backend,
                graph_cache,
            ));
            out.push_str("</td>");
        }
        out.push_str("</tr></thead>\n<tbody>\n");

        for oracle in &oracles {
            let _ = write!(
                out,
                "<tr><th class=\"oname\"><code>{}</code></th>",
                esc(oracle)
            );
            for step in &tab.steps {
                if !exports(step.game.game(), oracle) {
                    out.push_str("<td class=\"absent\"></td>");
                    continue;
                }
                let l = listing(&mut listings, &theorem_dbg, step.game, oracle);
                out.push_str("<td>");
                for (class, text) in [("full", &l.full), ("lossy", &l.lossy)] {
                    match text {
                        Ok(text) => {
                            let _ = write!(out, "<pre class=\"{class}\">{}</pre>", esc(text));
                        }
                        Err(e) => {
                            let _ = write!(out, "<div class=\"{class} error\">{}</div>", esc(e));
                        }
                    }
                }
                out.push_str("</td>");
            }
            out.push_str("</tr>\n");
        }
        out.push_str("</tbody></table></div>\n</section>\n");
    }

    // Package sources for the side pane, once per package.
    let sources: BTreeMap<&str, &str> = tabs
        .iter()
        .flat_map(|tab| &tab.steps)
        .flat_map(|step| &step.game.game().pkgs)
        .map(|inst| (inst.pkg.name.as_str(), inst.pkg.file_contents.as_str()))
        .collect();
    out.push_str("<div hidden>");
    for (name, src) in sources {
        let _ = write!(
            out,
            "<pre class=\"pkgsrc\" data-pkg=\"{}\">{}</pre>",
            esc(name),
            esc(src)
        );
    }
    out.push_str("</div>\n");
    out.push_str(
        "<aside id=\"pkgpane\"><div class=\"pp-head\"><div><div class=\"pp-title\"></div>\
         <div class=\"pp-sub\"></div></div><button id=\"pp-close\" title=\"close (Esc)\">×</button></div>\
         <div class=\"pp-body\"><h3>instance parameters</h3><pre class=\"pp-params\"></pre>\
         <h3>package source</h3><pre class=\"pp-src\"></pre></div></aside>\n",
    );

    let _ = write!(out, "<script>{SCRIPT}</script>\n</body></html>\n");
    Ok(out)
}

/// Both renderings of `oracle` inlined in `game`, computed once per
/// `(game, oracle)` — a game can appear on several propositions' paths.
fn listing<'m>(
    cache: &'m mut HashMap<(String, String), Listings>,
    theorem_dbg: &Theorem,
    game: &GameInstance,
    oracle: &str,
) -> &'m Listings {
    cache
        .entry((game.name().to_string(), oracle.to_string()))
        .or_insert_with(|| {
            let inst = theorem_dbg
                .find_game_instance(game.name())
                .expect("transformed theorem keeps every game instance");
            let render = |lossy| {
                render_oracle_listing(inst, oracle, lossy)
                    .map(|listing| strip_header(listing.text))
                    .map_err(|e| e.to_string())
            };
            Listings {
                full: render(false),
                lossy: render(true),
            }
        })
}

/// Drops the listing's `// game instance: ...` header line; the column
/// header already says all of it.
fn strip_header(text: String) -> String {
    match text.split_once('\n') {
        Some((first, rest)) if first.starts_with("// game instance:") => rest.to_string(),
        _ => text,
    }
}

/// One tab per proposition, in file order, each over the path the proof
/// search found. Without propositions: one tab over all game hops.
fn tabs<'t>(theorem: &'t Theorem<'t>) -> Vec<Tab<'t>> {
    if theorem.proofs.is_empty() {
        return vec![Tab {
            title: "game hops".to_string(),
            subtitle: "(no propositions)".to_string(),
            steps: games_in_hop_order(theorem)
                .into_iter()
                .map(|game| Step {
                    game,
                    assignments: Vec::new(),
                    via: None,
                })
                .collect(),
        }];
    }

    theorem
        .proofs
        .iter()
        .map(|proof| {
            let mut hops = proof.game_hops();
            let steps = proof
                .path()
                .enumerate()
                .map(|(i, (game, assignments))| Step {
                    game: theorem
                        .find_game_instance(game.name())
                        .expect("the proof path only visits theorem game instances"),
                    assignments: assignments.iter().map(assignment_pair).fold(
                        Vec::new(),
                        |mut acc, pair| {
                            // Two game constants set from the same theorem
                            // constant yield the same pair twice.
                            if !acc.contains(&pair) {
                                acc.push(pair);
                            }
                            acc
                        },
                    ),
                    via: if i == 0 { None } else { hops.next() },
                })
                .collect();
            Tab {
                title: proof.name().to_string(),
                subtitle: format!("{} ~ {}", proof.left_name(), proof.right_name()),
                steps,
            }
        })
        .collect()
}

fn assignment_pair(a: &ConstAssignment) -> (String, String) {
    (a.original_name(), a.assigned_value())
}

/// Where a Boolean shown on the page gets its value; picks its colour.
#[derive(Clone, Copy)]
enum BitSource {
    /// A literal in the game definition (`b: true` on a package instance).
    Fixed,
    /// A game constant the theorem's game instance sets to a literal.
    Instance,
    /// A theorem constant, i.e. a proof parameter.
    Proof,
}

impl BitSource {
    /// Of a game constant's value in a game instance.
    fn of_game_const(expr: &Expression) -> Option<Self> {
        match expr.kind() {
            ExpressionKind::BooleanLiteral(_) => Some(Self::Instance),
            _ if is_proof_param(expr) => Some(Self::Proof),
            _ => None,
        }
    }

    /// Of a package parameter's value in a game instance: a literal from the
    /// game definition, or a game constant carrying the instance's value.
    fn of_pkg_param(expr: &Expression) -> Option<Self> {
        match expr.kind() {
            ExpressionKind::BooleanLiteral(_) => Some(Self::Fixed),
            ExpressionKind::Identifier(Identifier::GameIdentifier(GameIdentifier::Const(c))) => {
                c.assigned_value.as_deref().and_then(Self::of_game_const)
            }
            _ => None,
        }
    }

    fn class(self) -> &'static str {
        match self {
            Self::Fixed => "b-fixed",
            Self::Instance => "b-inst",
            Self::Proof => "b-proof",
        }
    }

    fn label(self) -> &'static str {
        match self {
            Self::Fixed => "fixed parameter",
            Self::Instance => "instance parameter",
            Self::Proof => "proof parameter",
        }
    }
}

/// `text`, escaped, in the colour of `source` (plain when unknown).
fn bit_span(text: &str, source: Option<BitSource>, title: Option<&str>) -> String {
    let Some(source) = source else {
        return esc(text);
    };
    let title = title.map_or(String::new(), |t| format!(" title=\"{}\"", esc(t)));
    format!(
        "<span class=\"{}\"{title}>{}</span>",
        source.class(),
        esc(text)
    )
}

/// A Boolean constant of a game instance, as the theorem instantiates it.
struct GameBit {
    name: String,
    /// A literal, or the name of a theorem constant.
    value: String,
    source: Option<BitSource>,
}

/// The game instance's Boolean constants in the game's declaration order.
fn game_bits(game: &GameInstance) -> Vec<GameBit> {
    game.game()
        .consts
        .iter()
        .filter(|(_, ty)| matches!(ty.kind(), TypeKind::Boolean))
        .filter_map(|(name, _)| {
            let (_, expr) = game.consts.iter().find(|(id, _)| &id.name == name)?;
            Some(GameBit {
                name: name.clone(),
                value: render_expr(expr),
                source: BitSource::of_game_const(expr),
            })
        })
        .collect()
}

fn is_proof_param(expr: &Expression) -> bool {
    matches!(
        expr.kind(),
        ExpressionKind::Identifier(Identifier::TheoremIdentifier(TheoremIdentifier::Const(_)))
    )
}

/// `[bit1 -> 1, bit2 -> b]`, each value coloured by its [`BitSource`].
fn game_bits_html(bits: &[GameBit]) -> String {
    if bits.is_empty() {
        return String::new();
    }
    let body = bits
        .iter()
        .map(|bit| {
            let title = bit.source.map(BitSource::label);
            let value = bit_span(&bit_digit(&bit.value), bit.source, title);
            format!("{} -&gt; {value}", esc(&bit.name))
        })
        .collect::<Vec<_>>()
        .join(", ");
    format!(" <span class=\"gbits\">[{body}]</span>")
}

/// `bit1=1 bit2=0` above the diagram; proof parameters resolved through the
/// path's `assignments` where it fixes them.
fn bits_caption(bits: &[GameBit], assignments: &[(String, String)]) -> String {
    if bits.is_empty() {
        return String::new();
    }
    let body = bits
        .iter()
        .map(|bit| {
            let value = bit_digit(&substitute(bit.value.clone(), assignments));
            let title = match bit.source {
                Some(BitSource::Proof) => Some(format!("proof parameter {}", bit.value)),
                source => source.map(|s| s.label().to_string()),
            };
            let value = bit_span(&value, bit.source, title.as_deref());
            format!("<span>{}={value}</span>", esc(&bit.name))
        })
        .collect::<Vec<_>>()
        .join(" ");
    format!("<div class=\"bitscap\">{body}</div>")
}

/// Replace a proof parameter by the value the proof path assigns it, if any.
fn substitute(value: String, assignments: &[(String, String)]) -> String {
    assignments
        .iter()
        .find(|(original, _)| *original == value)
        .map_or(value, |(_, assigned)| assigned.clone())
}

fn bit_digit(value: &str) -> String {
    match value {
        "true" => "1".to_string(),
        "false" => "0".to_string(),
        other => other.to_string(),
    }
}

fn specialization_html(assignments: &[(String, String)]) -> String {
    if assignments.is_empty() {
        return String::new();
    }
    let body = assignments
        .iter()
        .map(|(name, value)| format!("{} ↦ {}", esc(name), esc(&bit_digit(value))))
        .collect::<Vec<_>>()
        .join(", ");
    format!(" <span class=\"spec\">[{body}]</span>")
}

/// Game instances in the order the hops first mention them; instances no hop
/// mentions come last, in declaration order.
fn games_in_hop_order<'t>(theorem: &'t Theorem) -> Vec<&'t GameInstance> {
    let mut names: Vec<&str> = Vec::new();
    for hop in &theorem.game_hops {
        for name in [
            hop.left_game_instance_name(),
            hop.right_game_instance_name(),
        ] {
            if !names.contains(&name) {
                names.push(name);
            }
        }
    }
    for inst in &theorem.instances {
        if !names.contains(&inst.name()) {
            names.push(inst.name());
        }
    }
    names
        .into_iter()
        .filter_map(|name| theorem.find_game_instance(name))
        .collect()
}

/// Every exported oracle name, in order of first appearance across `games`.
fn oracles_in_order<'g>(games: impl Iterator<Item = &'g GameInstance>) -> Vec<String> {
    let mut names: Vec<String> = Vec::new();
    for game in games {
        for export in &game.game().exports {
            if !names.iter().any(|n| n == export.name()) {
                names.push(export.name().to_string());
            }
        }
    }
    names
}

fn exports(comp: &Composition, oracle: &str) -> bool {
    comp.exports.iter().any(|e| e.name() == oracle)
}

fn hop_kind(hop: &GameHop) -> &'static str {
    match hop {
        GameHop::Conjecture(_) => "conjecture",
        GameHop::Reduction(_) => "reduction",
        GameHop::Equivalence(_) => "equivalence",
        GameHop::Hybrid(_) => "hybrid",
    }
}

/// A Boolean parameter of a package instance.
struct PkgBit {
    name: String,
    /// With the proof path's assignments substituted in.
    value: String,
    source: Option<BitSource>,
    /// Hover text: where the value comes from.
    origin: String,
}

/// The Boolean parameters of a package instance, in declaration order.
fn bool_params(pkg_inst: &PackageInstance, assignments: &[(String, String)]) -> Vec<PkgBit> {
    pkg_inst
        .pkg
        .params
        .iter()
        .filter(|(_, ty, _)| matches!(ty.kind(), TypeKind::Boolean))
        .filter_map(|(name, _, _)| {
            let (_, expr) = pkg_inst.params.iter().find(|(id, _)| &id.name == name)?;
            let rendered = render_expr(expr);
            let source = BitSource::of_pkg_param(expr);
            let origin = match (source, expr.kind()) {
                (Some(BitSource::Proof), _) => format!("proof parameter {rendered}"),
                (
                    Some(BitSource::Instance),
                    ExpressionKind::Identifier(Identifier::GameIdentifier(GameIdentifier::Const(
                        c,
                    ))),
                ) => format!("instance parameter {}", c.name),
                (Some(source), _) => source.label().to_string(),
                (None, _) => String::new(),
            };
            Some(PkgBit {
                name: name.clone(),
                value: substitute(rendered, assignments),
                source,
                origin,
            })
        })
        .collect()
}

/// Every parameter of a package instance as `name: Type = value`, one per
/// line, for the side pane.
fn params_text(pkg_inst: &PackageInstance, assignments: &[(String, String)]) -> String {
    pkg_inst
        .pkg
        .params
        .iter()
        .map(|(name, ty, _)| {
            let value = pkg_inst
                .params
                .iter()
                .find(|(id, _)| &id.name == name)
                .map_or("?".to_string(), |(_, expr)| {
                    substitute(render_expr(expr), assignments)
                });
            format!("{name}: {ty} = {value}")
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// A package node: its box and label — the package name with the Boolean
/// parameters as a superscript, and the instance name in parentheses below
/// when it differs — grouped so a click opens the side pane.
fn package_node(
    pkg_inst: &PackageInstance,
    assignments: &[(String, String)],
    (x, y, w, h): (f64, f64, f64, f64),
) -> String {
    let params = bool_params(pkg_inst, assignments);
    let mut title = format!("package {}, instance {}", pkg_inst.pkg.name, pkg_inst.name);
    for bit in &params {
        let _ = write!(title, "\n{} = {}", bit.name, bit.value);
        if !bit.origin.is_empty() {
            let _ = write!(title, " ({})", bit.origin);
        }
    }
    let digits: Vec<(String, Option<BitSource>)> = params
        .iter()
        .map(|bit| (bit_digit(&bit.value), bit.source))
        .collect();
    let sup_len = digits
        .iter()
        .map(|(d, _)| d.chars().count() + 1)
        .sum::<usize>();

    // Squeeze long lines into the box rather than letting them overflow.
    let fit = |chars: usize, px_per_char: f64| {
        if chars as f64 * px_per_char > w - 8.0 {
            format!(
                " textLength=\"{:.1}\" lengthAdjust=\"spacingAndGlyphs\"",
                w - 8.0
            )
        } else {
            String::new()
        }
    };
    let pkg_name = &pkg_inst.pkg.name;
    let inst_line = (pkg_inst.name != *pkg_name).then(|| format!("({})", pkg_inst.name));
    let (cx, cy) = (x + w / 2.0, y + h / 2.0);
    let name_y = if inst_line.is_some() { cy - 7.0 } else { cy };

    let sup_html = if digits.is_empty() {
        String::new()
    } else {
        let body = digits
            .iter()
            .map(|(digit, source)| match source {
                Some(s) => format!("<tspan class=\"{}\">{}</tspan>", s.class(), esc(digit)),
                None => esc(digit),
            })
            .collect::<Vec<_>>()
            .join(",");
        format!("<tspan class=\"sup\" baseline-shift=\"super\">{body}</tspan>")
    };
    let mut node = format!(
        "<g class=\"pkgnode\" data-pkg=\"{}\" data-inst=\"{}\" data-params=\"{}\">\
         <title>{}</title>\
         <rect class=\"pkgbox\" x=\"{x:.1}\" y=\"{y:.1}\" width=\"{w:.1}\" height=\"{h:.1}\" rx=\"3\"/>\
         <text class=\"pkg\" x=\"{cx:.1}\" y=\"{name_y:.1}\" text-anchor=\"middle\" \
         dominant-baseline=\"middle\"{}>{}{sup_html}</text>",
        esc(pkg_name),
        esc(&pkg_inst.name),
        esc(&params_text(pkg_inst, assignments)),
        esc(&title),
        fit(pkg_name.chars().count() + sup_len.saturating_sub(1), 7.2),
        esc(pkg_name),
    );
    if let Some(line) = inst_line {
        let _ = write!(
            node,
            "<text class=\"inst\" x=\"{cx:.1}\" y=\"{:.1}\" text-anchor=\"middle\" \
             dominant-baseline=\"middle\"{}>{}</text>",
            cy + 9.0,
            fit(line.chars().count(), 6.0),
            esc(&line),
        );
    }
    node.push_str("</g>");
    node
}

/// Box: `(column, bottom, top)` in tikz units (y up). Arrow: `(x0, x1, y, labels)`.
struct Geometry {
    boxes: Vec<(f64, f64, f64)>,
    arrows: Vec<(f64, f64, f64, Vec<String>)>,
}

fn diagram_svg<B: SmtSolverBackend>(
    comp: &Composition,
    assignments: &[(String, String)],
    backend: Option<&B>,
    cache: &Path,
) -> String {
    let geo = backend
        .and_then(|b| solver_geometry(comp, b, cache))
        .unwrap_or_else(|| fallback_geometry(comp));

    // Bounds in tikz units; arrow labels stack above their arrow.
    let mut min_x = f64::MAX;
    let mut max_x = f64::MIN;
    let mut min_y = f64::MAX;
    let mut max_y = f64::MIN;
    for &(x, bottom, top) in &geo.boxes {
        min_x = min_x.min(x);
        max_x = max_x.max(x + BOX_WIDTH);
        min_y = min_y.min(bottom);
        max_y = max_y.max(top);
    }
    for (x0, x1, y, labels) in &geo.arrows {
        min_x = min_x.min(*x0);
        max_x = max_x.max(*x1);
        min_y = min_y.min(*y);
        max_y = max_y.max(y + 0.35 * labels.len() as f64);
    }
    if min_x > max_x {
        return "<div class=\"absent\">empty composition</div>".to_string();
    }
    let pad = 0.3;
    let (min_x, max_x, min_y, max_y) = (min_x - pad, max_x + pad, min_y - pad, max_y + pad);
    let px = |x: f64| (x - min_x) * SCALE;
    let py = |y: f64| (max_y - y) * SCALE;

    let mut svg = String::new();
    let _ = write!(
        svg,
        "<svg class=\"diagram\" width=\"{w:.0}\" height=\"{h:.0}\" viewBox=\"0 0 {w:.1} {h:.1}\" \
         xmlns=\"http://www.w3.org/2000/svg\">\
         <defs><marker id=\"arrowhead\" viewBox=\"0 0 10 10\" refX=\"10\" refY=\"5\" \
         markerWidth=\"7\" markerHeight=\"7\" orient=\"auto-start-reverse\">\
         <path d=\"M0,0 L10,5 L0,10 z\" class=\"head\"/></marker></defs>",
        w = (max_x - min_x) * SCALE,
        h = (max_y - min_y) * SCALE,
    );
    for (x0, x1, y, labels) in &geo.arrows {
        let _ = write!(
            svg,
            "<line class=\"edge\" x1=\"{:.1}\" y1=\"{:.1}\" x2=\"{:.1}\" y2=\"{:.1}\" \
             marker-end=\"url(#arrowhead)\"/>",
            px(*x0),
            py(*y),
            px(*x1),
            py(*y),
        );
        for (k, label) in labels.iter().rev().enumerate() {
            let _ = write!(
                svg,
                "<text class=\"oracle\" x=\"{:.1}\" y=\"{:.1}\" text-anchor=\"middle\">{}</text>",
                px((x0 + x1) / 2.0),
                py(*y) - 4.0 - 14.0 * k as f64,
                esc(label),
            );
        }
    }
    for (i, &(x, bottom, top)) in geo.boxes.iter().enumerate() {
        svg.push_str(&package_node(
            &comp.pkgs[i],
            assignments,
            (px(x), py(top), BOX_WIDTH * SCALE, (top - bottom) * SCALE),
        ));
    }
    svg.push_str("</svg>");
    svg
}

/// The same geometry `tikzgraph.rs::smt_composition_graph` draws.
fn solver_geometry<B: SmtSolverBackend>(
    comp: &Composition,
    backend: &B,
    cache: &Path,
) -> Option<Geometry> {
    let layout = GraphLayout::new(backend, cache, comp)?;
    let model = layout.model();
    let int = |name: String| model.get_value_as_int(&name).map(f64::from);

    let mut boxes = Vec::new();
    for pkg in &comp.pkgs {
        let name = &pkg.name;
        boxes.push((
            int(format!("{name}-column"))? * COLUMN_PITCH,
            int(format!("{name}-bottom"))? / 2.0,
            int(format!("{name}-top"))? / 2.0,
        ));
    }

    let mut arrows = Vec::new();
    for from in 0..comp.pkgs.len() {
        for to in 0..comp.pkgs.len() {
            let labels: Vec<String> = comp
                .edges
                .iter()
                .filter(|e| e.from() == from && e.to() == to)
                .map(|e| e.name().to_string())
                .collect();
            if labels.is_empty() {
                continue;
            }
            let (a, b) = (&comp.pkgs[from].name, &comp.pkgs[to].name);
            arrows.push((
                int(format!("{a}-column"))? * COLUMN_PITCH + BOX_WIDTH,
                int(format!("{b}-column"))? * COLUMN_PITCH,
                int(format!("edge-{a}-{b}-height"))? / 2.0,
                labels,
            ));
        }
    }
    for to in 0..comp.pkgs.len() {
        let labels: Vec<String> = comp
            .exports
            .iter()
            .filter(|e| e.to() == to)
            .map(|e| e.name().to_string())
            .collect();
        if labels.is_empty() {
            continue;
        }
        let b = &comp.pkgs[to].name;
        arrows.push((
            int("--column".to_string())? * COLUMN_PITCH + BOX_WIDTH,
            int(format!("{b}-column"))? * COLUMN_PITCH,
            int(format!("edge---{b}-height"))? / 2.0,
            labels,
        ));
    }
    Some(Geometry { boxes, arrows })
}

/// Solver-free layout: column = longest call chain from the adversary, packages
/// stacked within a column, one arrow per (caller, callee) pair. Crossings are
/// possible; it is only the fallback.
fn fallback_geometry(comp: &Composition) -> Geometry {
    let n = comp.pkgs.len();
    let mut depth = vec![1usize; n];
    // Bellman-Ford-style relaxation, bounded so cycles cannot loop forever.
    for _ in 0..n {
        for e in &comp.edges {
            if depth[e.to()] < depth[e.from()] + 1 && depth[e.from()] < n + 1 {
                depth[e.to()] = depth[e.from()] + 1;
            }
        }
    }
    let mut next_slot = vec![0usize; n + 2];
    let boxes: Vec<(f64, f64, f64)> = (0..n)
        .map(|i| {
            let slot = next_slot[depth[i]];
            next_slot[depth[i]] += 1;
            let top = -(slot as f64) * 1.6;
            (depth[i] as f64 * COLUMN_PITCH, top - 1.0, top)
        })
        .collect();
    let mid = |i: usize| (boxes[i].1 + boxes[i].2) / 2.0;

    let mut arrows = Vec::new();
    // Arrows are horizontal at the callee's centre height, like the solver
    // layout's; they may start beside rather than on the caller's box.
    let mut add = |x0: f64, to: usize, labels: Vec<String>| {
        arrows.push((x0, boxes[to].0, mid(to), labels));
    };
    for (from, &(from_x, _, _)) in boxes.iter().enumerate() {
        for to in 0..n {
            let labels: Vec<String> = comp
                .edges
                .iter()
                .filter(|e| e.from() == from && e.to() == to)
                .map(|e| e.name().to_string())
                .collect();
            if !labels.is_empty() {
                add(from_x + BOX_WIDTH, to, labels);
            }
        }
    }
    for to in 0..n {
        let labels: Vec<String> = comp
            .exports
            .iter()
            .filter(|e| e.to() == to)
            .map(|e| e.name().to_string())
            .collect();
        if !labels.is_empty() {
            add(0.0, to, labels);
        }
    }
    Geometry { boxes, arrows }
}

fn esc(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '"' => out.push_str("&quot;"),
            _ => out.push(c),
        }
    }
    out
}

const STYLE: &str = r#"
:root { --bg:#ffffff; --fg:#1b1f24; --muted:#6a737d; --line:#d0d7de; --head:#f6f8fa;
        --accent:#0969da; --accent-bg:#ddf4ff; --pkg:#fff8e1; --pkgline:#8a6d00;
        --edge:#444c56; --proof:#b3261e; --inst:#8250df; --err:#b3261e; --code:12px; }
@media (prefers-color-scheme: dark) {
  :root { --bg:#0d1117; --fg:#e6edf3; --muted:#8b949e; --line:#30363d; --head:#161b22;
          --accent:#4493f8; --accent-bg:#132339; --pkg:#2d2610; --pkgline:#d4a72c;
          --edge:#adbac7; --proof:#ff7b72; --inst:#d2a8ff; --err:#ff7b72; }
}
html, body { height:100%; }
body { background:var(--bg); color:var(--fg); margin:0; display:flex; flex-direction:column;
       height:100vh; overflow:hidden;
       font:14px/1.4 -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif; }
code, pre, kbd { font-family: ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; }
header { flex:none; padding:10px 16px 0; }
.titlebar { display:flex; flex-wrap:wrap; gap:8px 20px; align-items:center; justify-content:space-between; }
h1 { font-size:18px; margin:0; }
.tools { display:flex; flex-wrap:wrap; gap:14px; align-items:center; color:var(--muted); font-size:13px; }
.tools label { cursor:pointer; user-select:none; }
button { font:inherit; color:var(--fg); background:var(--head); border:1px solid var(--line);
         border-radius:6px; padding:2px 8px; cursor:pointer; }
button:hover { border-color:var(--accent); }
kbd { border:1px solid var(--line); border-radius:4px; padding:0 4px; font-size:11px; margin-right:2px; }
.tabs { display:flex; flex-wrap:wrap; gap:6px; margin:10px 0 6px; }
.tab span { color:var(--muted); font-size:12px; }
.tab.active { background:var(--accent-bg); border-color:var(--accent); }
details.hops { color:var(--muted); font-size:13px; margin-bottom:4px; }
details.hops summary { cursor:pointer; }
details.hops ol { margin:4px 0; padding-left:28px; }
details.hops .kind { display:inline-block; min-width:90px; }
details.hops code { color:var(--fg); }
section.tabpane { display:none; flex:1; min-height:0; flex-direction:column; padding:0 16px 12px; }
section.tabpane.active { display:flex; }
nav.path { flex:none; display:flex; flex-wrap:wrap; gap:4px 6px; align-items:center; margin:4px 0 8px; }
.chip { font-family: ui-monospace, Menlo, monospace; font-size:12px; }
.chip.visible { background:var(--accent-bg); border-color:var(--accent); }
.via { color:var(--muted); font-size:11px; cursor:help; }
.via::before { content:"→ "; } .via::after { content:" →"; }
.spec { color:var(--proof); font-size:11px; font-weight:normal; }
.scroller { flex:1; min-height:0; overflow:auto; border:1px solid var(--line); scroll-snap-type:x proximity; }
table { border-collapse:separate; border-spacing:0; }
th, td { border-right:1px solid var(--line); border-bottom:1px solid var(--line);
         vertical-align:top; text-align:left; padding:6px 10px; }
th.col { scroll-snap-align:start; }
thead tr:first-child th { position:sticky; top:0; z-index:2; background:var(--head); }
th.corner, th.oname { position:sticky; left:0; z-index:1; background:var(--head); }
thead th.corner { z-index:3; }
.gname { font-weight:600; font-family: ui-monospace, Menlo, monospace; white-space:nowrap; }
.gname .idx { color:var(--muted); font-weight:normal; font-size:11px; }
.gsub { color:var(--muted); font-weight:normal; font-size:12px; }
tr.diagrams td { background:var(--bg); }
pre { margin:0; font-size:var(--code); line-height:1.35; white-space:pre; }
body.wrap pre { white-space:pre-wrap; overflow-wrap:anywhere; max-width:80ch; }
body:not(.show-lossy) .lossy, body.show-lossy .full { display:none; }
.error { color:var(--err); white-space:pre-wrap; max-width:60ch; }
svg.diagram { display:block; }
svg .pkgbox { fill:var(--pkg); stroke:var(--pkgline); stroke-width:1.2; }
svg .pkg { fill:var(--fg); font:12px ui-monospace, Menlo, monospace; }
svg .sup { fill:var(--muted); font-size:9px; }
svg .edge { stroke:var(--edge); stroke-width:1.2; }
svg .head { fill:var(--edge); }
svg .oracle { fill:var(--muted); font:10px ui-monospace, Menlo, monospace; }
svg .inst { fill:var(--muted); font:10px ui-monospace, Menlo, monospace; }
svg .pkgnode { cursor:pointer; }
svg .pkgnode:hover .pkgbox { stroke-width:2.2; }
svg .pkgnode.selected .pkgbox { stroke:var(--accent); stroke-width:2.4; }
.gbits { font-weight:normal; font-size:12px; }
.b-fixed { color:var(--muted); } svg .b-fixed { fill:var(--muted); }
.b-inst { color:var(--inst); font-weight:600; } svg .b-inst { fill:var(--inst); }
.b-proof { color:var(--proof); font-weight:600; } svg .b-proof { fill:var(--proof); }
.legend b { margin-left:6px; }
.bitscap { display:flex; flex-wrap:wrap; gap:4px 12px; margin-bottom:4px;
           font:11px ui-monospace, Menlo, monospace; color:var(--muted); }
#pkgpane { position:fixed; top:0; right:0; bottom:0; width:var(--pane); z-index:10;
           display:flex; flex-direction:column; background:var(--bg);
           border-left:1px solid var(--line); box-shadow:-8px 0 24px rgba(0,0,0,.25);
           transform:translateX(100%); transition:transform .15s; }
:root { --pane:min(680px, 50vw); }
body.pp-open #pkgpane { transform:none; }
body.pp-open header, body.pp-open section.tabpane { margin-right:var(--pane); }
.pp-head { display:flex; justify-content:space-between; align-items:flex-start; gap:8px;
           padding:10px 14px; border-bottom:1px solid var(--line); background:var(--head); }
.pp-title { font:600 15px ui-monospace, Menlo, monospace; }
.pp-sub { color:var(--muted); font-size:12px; }
.pp-body { flex:1; min-height:0; overflow:auto; padding:4px 14px 16px; }
.pp-body h3 { font-size:11px; text-transform:uppercase; letter-spacing:.05em; color:var(--muted); margin:12px 0 4px; }
.pp-body .kw { color:var(--accent); }
.pp-body .cm { color:var(--muted); font-style:italic; }
"#;

/// Tabs, the lossy / wrap / zoom options (remembered per browser), column
/// chips, and ←/→ to step between game columns.
const SCRIPT: &str = r#"
(function () {
  const store = {
    get(k) { try { return localStorage.getItem('domino-html-' + k); } catch (e) { return null; } },
    set(k, v) { try { localStorage.setItem('domino-html-' + k, v); } catch (e) {} },
  };
  const body = document.body;
  const tabs = [...document.querySelectorAll('.tab')];
  const panes = [...document.querySelectorAll('.tabpane')];
  const pane = () => document.querySelector('.tabpane.active');

  // Package side pane.
  const ppane = document.getElementById('pkgpane');
  const sources = {};
  document.querySelectorAll('pre.pkgsrc').forEach(p => { sources[p.dataset.pkg] = p.textContent; });
  const TOKENS = /\/\*[\s\S]*?\*\/|\/\/[^\n]*|\b(?:package|composition|theorem|params|state|types|import|oracles|oracle|return|if|else|assert|abort|invoke|for|in|const|Bool|Integer|Bits|Maybe|Table|Some|None|unwrap|true|false)\b/g;
  function highlight(text) {
    const esc = t => t.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
    let out = '', last = 0;
    for (const m of text.matchAll(TOKENS)) {
      const cls = m[0].startsWith('/') ? 'cm' : 'kw';
      out += esc(text.slice(last, m.index)) + '<span class="' + cls + '">' + esc(m[0]) + '</span>';
      last = m.index + m[0].length;
    }
    return out + esc(text.slice(last));
  }
  function setPane(open) {
    body.classList.toggle('pp-open', open);
    refresh();
  }
  function openPkg(node) {
    document.querySelectorAll('.pkgnode.selected').forEach(n => n.classList.remove('selected'));
    node.classList.add('selected');
    const cell = node.closest('td');
    const pkg = node.dataset.pkg;
    ppane.querySelector('.pp-title').textContent = 'package ' + pkg;
    ppane.querySelector('.pp-sub').textContent =
      'instance ' + node.dataset.inst + (cell ? ' in game instance ' + cell.dataset.game : '');
    ppane.querySelector('.pp-params').textContent = node.dataset.params || '(no parameters)';
    ppane.querySelector('.pp-src').innerHTML = highlight(sources[pkg] || '(source not available)');
    ppane.querySelector('.pp-body').scrollTop = 0;
    setPane(true);
  }
  ppane.querySelector('.pp-title').textContent = 'packages';
  ppane.querySelector('.pp-sub').textContent = 'click a package in a diagram';
  document.addEventListener('click', e => {
    const node = e.target.closest && e.target.closest('.pkgnode');
    if (node) openPkg(node);
  });
  document.getElementById('pp-close').addEventListener('click', () => setPane(false));
  document.getElementById('pp-toggle').addEventListener('click',
    () => setPane(!body.classList.contains('pp-open')));

  function option(id, cls, key) {
    const box = document.getElementById(id);
    const saved = store.get(key);
    if (saved !== null) body.classList.toggle(cls, saved === '1');
    box.checked = body.classList.contains(cls);
    box.addEventListener('change', () => {
      body.classList.toggle(cls, box.checked);
      store.set(key, box.checked ? '1' : '0');
      refresh();
    });
  }
  option('opt-lossy', 'show-lossy', 'lossy');
  option('opt-wrap', 'wrap', 'wrap');

  let code = parseInt(store.get('code'), 10) || 12;
  function zoom(d) {
    code = Math.min(20, Math.max(8, code + d));
    document.documentElement.style.setProperty('--code', code + 'px');
    store.set('code', String(code));
    refresh();
  }
  zoom(0);
  document.getElementById('zoom-in').addEventListener('click', () => zoom(1));
  document.getElementById('zoom-out').addEventListener('click', () => zoom(-1));

  function showTab(t) {
    tabs.forEach(b => b.classList.toggle('active', b.dataset.tab === String(t)));
    panes.forEach(p => p.classList.toggle('active', p.dataset.tab === String(t)));
    store.set('tab:' + document.title, String(t));
    refresh();
  }
  tabs.forEach(b => b.addEventListener('click', () => showTab(b.dataset.tab)));

  // Geometry of the active pane: the scroller, its game columns, and the left
  // edge of the area not covered by the sticky oracle-name column.
  function geo(p) {
    const sc = p.querySelector('.scroller');
    const cols = [...p.querySelectorAll('th.col')];
    const corner = p.querySelector('th.corner');
    const r = sc.getBoundingClientRect();
    return { sc, cols, left: r.left + corner.offsetWidth, right: r.right, cornerW: corner.offsetWidth };
  }
  function scrollToCol(p, i) {
    const g = geo(p);
    const c = g.cols[Math.max(0, Math.min(g.cols.length - 1, i))];
    if (!c) return;
    g.sc.scrollTo({ left: g.sc.scrollLeft + c.getBoundingClientRect().left - g.left, behavior: 'smooth' });
  }
  function refresh() {
    const p = pane();
    if (!p) return;
    const g = geo(p);
    g.sc.style.scrollPaddingLeft = g.cornerW + 'px';
    const chips = p.querySelectorAll('.chip');
    g.cols.forEach((c, i) => {
      const r = c.getBoundingClientRect();
      chips[i].classList.toggle('visible', r.right > g.left + 20 && r.left < g.right - 20);
    });
  }

  panes.forEach(p => {
    p.querySelectorAll('.chip').forEach(ch =>
      ch.addEventListener('click', () => scrollToCol(p, parseInt(ch.dataset.col, 10))));
    let queued = false;
    p.querySelector('.scroller').addEventListener('scroll', () => {
      if (queued) return;
      queued = true;
      requestAnimationFrame(() => { queued = false; refresh(); });
    });
  });
  window.addEventListener('resize', refresh);

  document.addEventListener('keydown', e => {
    if (e.key === 'Escape' && body.classList.contains('pp-open')) { setPane(false); return; }
    if (e.altKey || e.ctrlKey || e.metaKey || e.shiftKey) return;
    if (e.target.closest && e.target.closest('input, textarea, select')) return;
    if (e.key !== 'ArrowRight' && e.key !== 'ArrowLeft') return;
    const p = pane();
    if (!p) return;
    const g = geo(p);
    const lefts = g.cols.map(c => c.getBoundingClientRect().left - g.left);
    let target;
    if (e.key === 'ArrowRight') {
      target = lefts.findIndex(x => x > 5);
      if (target < 0) return;
    } else {
      target = -1;
      lefts.forEach((x, i) => { if (x < -5) target = i; });
      if (target < 0) return;
    }
    e.preventDefault();
    scrollToCol(p, target);
  });

  const saved = parseInt(store.get('tab:' + document.title), 10);
  showTab(saved >= 0 && saved < tabs.length ? saved : 0);
})();
"#;
