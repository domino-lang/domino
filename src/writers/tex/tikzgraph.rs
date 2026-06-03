// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::{
    package::Composition, parser::ast::Identifier, parser::reduction::ReductionMapping,
    util::smtsolver::SmtSolverBackend, writers::util::graph::GraphLayout,
};

use std::{fmt::Write, path::Path};

pub(crate) trait TikzGraph {
    fn tikz_graph(&self, backend: &impl SmtSolverBackend, cache: &Path) -> String;
}

pub(crate) struct ReductionGraph<'a> {
    pub mapping: &'a ReductionMapping<'a>,
    pub composition: &'a Composition,
}

impl TikzGraph for ReductionGraph<'_> {
    fn tikz_graph(&self, backend: &impl SmtSolverBackend, cache: &Path) -> String {
        smt_composition_graph(backend, self.composition, Some(self.mapping), cache).unwrap_or(
            fallback_composition_graph(self.composition, Some(self.mapping)),
        )
    }
}

impl TikzGraph for Composition {
    fn tikz_graph(&self, backend: &impl SmtSolverBackend, cache: &Path) -> String {
        smt_composition_graph(backend, self, None, cache)
            .unwrap_or(fallback_composition_graph(self, None))
    }
}

fn fallback_composition_graph(
    composition: &Composition,
    reduction_mapping: Option<&ReductionMapping>,
) -> String {
    let mut result = String::new();
    let mut printed = Vec::new();
    let mut newly = Vec::new();

    let mut tikzx = 0;
    let mut tikzy = 0;

    writeln!(result, "\\begin{{tikzpicture}}").unwrap();
    while printed.len() < composition.pkgs.len() {
        for i in 0..composition.pkgs.len() {
            if printed.contains(&i) {
                continue;
            }

            if !composition
                .edges
                .iter()
                .any(|edge| i == edge.from() && !printed.contains(&edge.to()))
            {
                write!(
                    result,
                    "{}",
                    package_node_tikz(
                        &composition.pkgs[i].name,
                        reduction_mapping,
                        i,
                        tikzy + 1,
                        tikzy,
                        tikzx,
                    )
                )
                .unwrap();

                newly.push(i);
                tikzy -= 2;

                for edge in &composition.edges {
                    if i == edge.from() {
                        writeln!(result, "\\draw[-latex,rounded corners] (node{}) -- ($(node{}.east) + (1,0)$) |- node[onarrow] {{\\O{{{}}}}} (node{});", edge.from(), edge.from(), edge.name(), edge.to()).unwrap();
                    }
                }
            }
        }
        printed.append(&mut newly);
        tikzx -= 4;
        tikzy = tikzx / 4;
    }

    writeln!(
        result,
        "\\node[package] (nodea) at ({tikzx}, {tikzy}) {{$A$}};"
    )
    .unwrap();
    for export in &composition.exports {
        writeln!(result, "\\draw[-latex,rounded corners] (nodea) -- ($(nodea.east) + (1,0)$) |- node[onarrow] {{\\O{{{}}}}} (node{});", export.sig().name, export.to()).unwrap();
    }
    writeln!(result, "\\end{{tikzpicture}}").unwrap();
    result
}

fn smt_composition_graph(
    backend: &impl SmtSolverBackend,
    composition: &Composition,
    reduction_mapping: Option<&ReductionMapping>,
    cache: &Path,
) -> Option<String> {
    let mut result = String::new();
    let layout = GraphLayout::new(backend, cache, composition);
    if let Some(layout) = layout {
        let model = layout.model();
        writeln!(result, "\\begin{{tikzpicture}}").unwrap();

        for i in 0..composition.pkgs.len() {
            let pkgname = &composition.pkgs[i].name;
            let top = model.get_value_as_int(&format!("{pkgname}-top")).unwrap();
            let bottom = model
                .get_value_as_int(&format!("{pkgname}-bottom"))
                .unwrap();
            let column = model
                .get_value_as_int(&format!("{pkgname}-column"))
                .unwrap();

            write!(
                result,
                "{}",
                package_node_tikz(pkgname, reduction_mapping, i, top, bottom, column)
            )
            .unwrap();
        }

        for from in 0..composition.pkgs.len() {
            for to in 0..composition.pkgs.len() {
                let oracles: Vec<_> = composition
                    .edges
                    .iter()
                    .filter_map(|edge| {
                        if from == edge.from() && to == edge.to() {
                            Some(edge.name())
                        } else {
                            None
                        }
                    })
                    .collect();
                if oracles.is_empty() {
                    continue;
                }

                let pkga = &composition.pkgs[from].name;
                let pkgb = &composition.pkgs[to].name;

                let height = model
                    .get_value_as_int(&format!("edge-{pkga}-{pkgb}-height"))
                    .unwrap();
                let acolumn = model.get_value_as_int(&format!("{pkga}-column")).unwrap();
                let bcolumn = model.get_value_as_int(&format!("{pkgb}-column")).unwrap();

                let height = f64::from(height) / 2.0;
                let oracles = oracles
                    .into_iter()
                    .map(|o| format!("\\O{{{}}}", o.replace("_", "\\_")))
                    .collect::<Vec<_>>()
                    .join("\\\\");
                writeln!(
                    result,
                    "\\draw[-latex,rounded corners]
    ({},{}) -- node[onarrow] {{{}}} ({},{});",
                    f64::from(acolumn) * 3.5 + 2.0,
                    height,
                    oracles,
                    f64::from(bcolumn) * 3.5,
                    height
                )
                .unwrap();
            }
        }
        for to in 0..composition.pkgs.len() {
            let oracles: Vec<_> = composition
                .exports
                .iter()
                .filter_map(|export| {
                    if to == export.to() {
                        Some(export.name())
                    } else {
                        None
                    }
                })
                .collect();
            if oracles.is_empty() {
                continue;
            }

            let pkgb = &composition.pkgs[to].name;

            let height = model
                .get_value_as_int(&format!("edge---{pkgb}-height"))
                .unwrap();
            let acolumn = model.get_value_as_int("--column").unwrap();
            let bcolumn = model.get_value_as_int(&format!("{pkgb}-column")).unwrap();

            let height = f64::from(height) / 2.0;
            let oracles = oracles
                .into_iter()
                .map(|o| format!("\\O{{{}}}", o.replace("_", "\\_")))
                .collect::<Vec<_>>()
                .join("\\\\");
            writeln!(
                result,
                "\\draw[-latex,rounded corners] ({},{}) -- node[onarrow] {{{}}} ({},{});",
                f64::from(acolumn) * 3.5 + 2.0,
                height,
                oracles,
                f64::from(bcolumn) * 3.5,
                height
            )
            .unwrap();
        }

        writeln!(result, "\\end{{tikzpicture}}").unwrap();

        Some(result)
    } else {
        None
    }
}

fn package_node_tikz(
    pkgname: &str,
    reduction_mapping: Option<&ReductionMapping>,
    idx: usize,
    top: i32,
    bottom: i32,
    column: i32,
) -> String {
    let fill = if reduction_mapping.is_some()
        && reduction_mapping
            .unwrap()
            .entries()
            .iter()
            .any(|entry| pkgname == entry.construction().as_str())
    {
        "red!50"
    } else {
        "white"
    };

    format!(
        "\\node[anchor=south west,align=center,package,minimum height={}cm,fill={fill}] (node{}) at ({},{}) {{\\M{{{}}}}};",
        f64::from(top - bottom) / 2.0,
        idx,
        f64::from(column) * 3.5,
        f64::from(bottom) / 2.0,
        //compname.replace('_', "\\_"),
        pkgname.replace('_', "\\_")
    )
}
