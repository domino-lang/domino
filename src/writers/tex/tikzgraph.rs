use crate::{
    package::{Composition, Edge, Export},
    parser::ast::Identifier,
    parser::reduction::ReductionMapping,
    util::{
        prover_process::{Communicator, ProverBackend, ProverResponse},
        smtmodel::{SmtModel, SmtModelEntry},
    },
};

use std::{collections::HashSet, fmt::Write};

pub(crate) trait TikzGraph {
    fn tikz_graph(&self, backend: &ProverBackend) -> String;
}

pub(crate) struct ReductionGraph<'a> {
    pub mapping: &'a ReductionMapping<'a>,
    pub composition: &'a Composition,
}

impl TikzGraph for ReductionGraph<'_> {
    fn tikz_graph(&self, backend: &ProverBackend) -> String {
        smt_composition_graph(backend, self.composition, Some(self.mapping)).unwrap_or(
            fallback_composition_graph(self.composition, Some(self.mapping)),
        )
    }
}

impl TikzGraph for Composition {
    fn tikz_graph(&self, backend: &ProverBackend) -> String {
        smt_composition_graph(backend, self, None).unwrap_or(fallback_composition_graph(self, None))
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
                .any(|Edge(from, to, _oracle)| i == *from && !printed.contains(to))
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

                for Edge(from, to, oracle) in &composition.edges {
                    if i == *from {
                        writeln!(result, "\\draw[-latex,rounded corners] (node{}) -- ($(node{}.east) + (1,0)$) |- node[onarrow] {{\\O{{{}}}}} (node{});", from, from, oracle.name, to).unwrap();
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
    for Export(to, oracle) in &composition.exports {
        writeln!(result, "\\draw[-latex,rounded corners] (nodea) -- ($(nodea.east) + (1,0)$) |- node[onarrow] {{\\O{{{}}}}} (node{});", oracle.name, to).unwrap();
    }
    writeln!(result, "\\end{{tikzpicture}}").unwrap();
    result
}

fn smt_composition_graph(
    backend: &ProverBackend,
    composition: &Composition,
    reduction_mapping: Option<&ReductionMapping>,
) -> Option<String> {
    let mut result = String::new();
    let solution = solve_composition_graph(backend, composition);
    if let Some(model) = solution {
        writeln!(result, "\\begin{{tikzpicture}}").unwrap();

        for i in 0..composition.pkgs.len() {
            let pkgname = &composition.pkgs[i].name;
            let SmtModelEntry::IntEntry { value: top, .. } =
                model.get_value(&format!("{pkgname}-top")).unwrap();
            let SmtModelEntry::IntEntry { value: bottom, .. } =
                model.get_value(&format!("{pkgname}-bottom")).unwrap();
            let SmtModelEntry::IntEntry { value: column, .. } =
                model.get_value(&format!("{pkgname}-column")).unwrap();

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
                    .filter_map(|Edge(f, t, oracle)| {
                        if from == *f && to == *t {
                            Some(oracle.name.clone())
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

                let SmtModelEntry::IntEntry { value: height, .. } = model
                    .get_value(&format!("edge-{pkga}-{pkgb}-height"))
                    .unwrap();
                let SmtModelEntry::IntEntry { value: acolumn, .. } =
                    model.get_value(&format!("{pkga}-column")).unwrap();
                let SmtModelEntry::IntEntry { value: bcolumn, .. } =
                    model.get_value(&format!("{pkgb}-column")).unwrap();

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
                .filter_map(|Export(t, oracle)| {
                    if to == *t {
                        Some(oracle.name.clone())
                    } else {
                        None
                    }
                })
                .collect();
            if oracles.is_empty() {
                continue;
            }

            let pkgb = &composition.pkgs[to].name;

            let SmtModelEntry::IntEntry { value: height, .. } =
                model.get_value(&format!("edge---{pkgb}-height")).unwrap();
            let SmtModelEntry::IntEntry { value: acolumn, .. } =
                model.get_value("--column").unwrap();
            let SmtModelEntry::IntEntry { value: bcolumn, .. } =
                model.get_value(&format!("{pkgb}-column")).unwrap();

            let height = f64::from(height) / 2.0;
            let oracles = oracles
                .into_iter()
                .map(|o| format!("\\O{{{o}}}"))
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

fn composition_graph_smt_query(composition: &Composition) -> Result<String, std::fmt::Error> {
    let mut result = String::new();
    let mut edges: HashSet<(usize, usize)> = HashSet::new();

    writeln!(result, "(set-logic ALL)")?;
    writeln!(result, "(declare-const num-pkgs Int)")?;
    writeln!(result, "(declare-const width Int)")?;
    writeln!(result, "(declare-const height Int)")?;
    writeln!(result, "(assert (= num-pkgs {}))", composition.pkgs.len())?;

    // Adversary
    writeln!(result, "(declare-const --column Int)")?;
    writeln!(result, "(assert (= 0 --column))")?;
    writeln!(result, "(declare-const --top Int)")?;
    writeln!(result, "(declare-const --bottom Int)")?;
    writeln!(result, "(assert (< 0 --bottom (- --top 1) height))")?;

    for i in 0..composition.pkgs.len() {
        let pkg = &composition.pkgs[i].name;
        writeln!(result, "(declare-const {pkg}-column Int)")?;
        writeln!(result, "(assert (< 0 {pkg}-column width))")?;
        writeln!(result, "(declare-const {pkg}-top Int)")?;
        writeln!(result, "(declare-const {pkg}-bottom Int)")?;
        writeln!(result, "(assert (< 0 {pkg}-bottom (- {pkg}-top 1) height))")?;
    }

    for Edge(from, to, _oracle) in &composition.edges {
        if edges.contains(&(*from, *to)) {
            continue;
        };
        edges.insert((*from, *to));
        let pkga = &composition.pkgs[*from].name;
        let pkgb = &composition.pkgs[*to].name;

        writeln!(result, "(declare-const edge-{pkga}-{pkgb}-height Int)")?;
        writeln!(
            result,
            "(assert (< {pkga}-bottom edge-{pkga}-{pkgb}-height {pkga}-top))"
        )?;
        writeln!(
            result,
            "(assert (< {pkgb}-bottom edge-{pkga}-{pkgb}-height {pkgb}-top))"
        )?;
        writeln!(result, "(assert (< {pkga}-column {pkgb}-column))")?;
    }

    for Export(to, _oracle) in &composition.exports {
        if edges.contains(&(usize::MAX, *to)) {
            continue;
        };
        edges.insert((usize::MAX, *to));
        let pkga = "-";
        let pkgb = &composition.pkgs[*to].name;

        writeln!(result, "(declare-const edge-{pkga}-{pkgb}-height Int)")?;
        writeln!(
            result,
            "(assert (< {pkga}-bottom edge-{pkga}-{pkgb}-height {pkga}-top))"
        )?;
        writeln!(
            result,
            "(assert (< {pkgb}-bottom edge-{pkga}-{pkgb}-height {pkgb}-top))"
        )?;
        writeln!(result, "(assert (< {pkga}-column {pkgb}-column))")?;
    }

    for i in 0..composition.pkgs.len() {
        for j in 0..i {
            let pkga = &composition.pkgs[i].name;
            let pkgb = &composition.pkgs[j].name;
            writeln!(
                result,
                "
(assert (not (exists ((l Int))
               (and
                 (<= {pkga}-bottom l {pkga}-top)
                 (<= {pkgb}-bottom l {pkgb}-top)
                 (= {pkga}-column {pkgb}-column)))))"
            )?;
        }
    }

    for i in 0..composition.pkgs.len() {
        for Edge(from, to, _oracle) in &composition.edges {
            let pkga = &composition.pkgs[*from].name;
            let pkgb = &composition.pkgs[*to].name;
            let pkgc = &composition.pkgs[i].name;

            writeln!(
                result,
                "
(assert (not (and (< {pkga}-column {pkgc}-column {pkgb}-column)
                  (< (- {pkgc}-bottom 1) edge-{pkga}-{pkgb}-height (+ {pkgc}-top 1)))))"
            )?;
        }
        for Export(to, _oracle) in &composition.exports {
            let pkga = "-";
            let pkgb = &composition.pkgs[*to].name;
            let pkgc = &composition.pkgs[i].name;

            writeln!(
                result,
                "
(assert (not (and (<  {pkga}-column {pkgc}-column {pkgb}-column)
                  (< (- {pkgc}-bottom 1) edge-{pkga}-{pkgb}-height (+ {pkgc}-top 1)))))"
            )?;
        }
    }

    Ok(result)
}

pub(crate) fn solve_composition_graph(
    backend: &ProverBackend,
    composition: &Composition,
) -> Option<SmtModel> {
    let constraints = composition_graph_smt_query(composition).unwrap();
    let mut max_width;
    let mut min_width = 0;
    let mut max_height;
    let mut min_height = 0;

    let mut model;
    let mut comm = Communicator::new(*backend).unwrap();
    write!(comm, "{}", constraints).unwrap();

    if comm.check_sat().unwrap() != ProverResponse::Sat {
        return None;
    } else {
        model = comm.get_model().unwrap();
        let model = SmtModel::from_string(&model);
        let SmtModelEntry::IntEntry { value, .. } = model.get_value("width").unwrap();
        max_width = value + 1;
        let SmtModelEntry::IntEntry { value, .. } = model.get_value("height").unwrap();
        max_height = value + 1;
    }

    loop {
        let width = min_width + (max_width - min_width) / 2;

        let mut comm = Communicator::new(*backend).unwrap();
        write!(comm, "{}", constraints).unwrap();
        writeln!(comm, "(push 1)").unwrap();
        writeln!(comm, "(assert (< width {width}))").unwrap();

        if comm.check_sat().unwrap() == ProverResponse::Sat {
            log::debug!("Success: width = {width}");
            max_width = width;
            model = comm.get_model().unwrap();
            let model = SmtModel::from_string(&model);
            let SmtModelEntry::IntEntry { value, .. } = model.get_value("height").unwrap();
            max_height = value + 1;
        } else {
            log::debug!("Failure: width = {width}");
            min_width = width;
        }
        //writeln!(comm, "(pop 1)").unwrap();

        if min_width + 1 == max_width {
            break;
        }
    }
    debug_assert!(max_height > 0);

    loop {
        let height = min_height + (max_height - min_height) / 2;

        let mut comm = Communicator::new(*backend).unwrap();
        write!(comm, "{}", constraints).unwrap();
        writeln!(comm, "(push 1)").unwrap();
        writeln!(comm, "(assert (< height {height}))").unwrap();
        writeln!(comm, "(assert (< width {max_width}))").unwrap();

        if comm.check_sat().unwrap() == ProverResponse::Sat {
            log::debug!("Success: height = {height}");
            max_height = height;
        } else {
            log::debug!("Failure: height = {height} (width = {max_width})");
            min_height = height;
        }
        //writeln!(comm, "(pop 1)").unwrap();

        if min_height + 1 == max_height {
            break;
        }
    }

    log::debug!("Conclusion: height = {max_height}, width = {max_width}");
    let mut comm = Communicator::new(*backend).unwrap();
    write!(comm, "{}", constraints).unwrap();
    writeln!(comm, "(assert (< height {max_height}))").unwrap();
    writeln!(comm, "(assert (< width {max_width}))").unwrap();

    if comm.check_sat().unwrap() == ProverResponse::Sat {
        model = comm.get_model().unwrap();
        let model = SmtModel::from_string(&model);
        log::debug!("{}\n{:#?}", composition.name, model);
        Some(model)
    } else {
        unreachable!("Started from a feasible solution so this should never be reached");
    }
}
