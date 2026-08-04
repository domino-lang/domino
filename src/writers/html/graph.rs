use itertools::Itertools;
use maud::{html, Markup};

use std::fs::File;
use std::io::Write;
use std::path::Path;

use crate::{
    package::Composition, util::smtsolver::SmtSolverBackend, writers::util::graph::GraphLayout,
};

pub fn write_composition_graph(
    target: &Path,
    backend: &impl SmtSolverBackend,
    instance: &Composition,
) -> std::io::Result<()> {
    if let Some(svg) = composition_graph(backend, instance) {
        let fname = target.join(format!("Graph_{}.svg", instance.name,));
        let mut file = File::create(fname.clone())?;
        write!(file, "{}", svg.into_string())?;
    }
    Ok(())
}

pub fn composition_graph(
    backend: &impl SmtSolverBackend,
    instance: &Composition,
) -> Option<Markup> {
    let layout = GraphLayout::new(backend, instance);
    layout.map(|layout| {
        let model = layout.model();
        let width = model.get_value_as_int("width").unwrap();
        let height = model.get_value_as_int("height").unwrap();

        let pkgs = instance.pkgs.iter().map(|pkg| {
            let pkgname = &pkg.name;
            let top = model.get_value_as_int(&format!("{pkgname}-top")).unwrap();
            let bottom = model
                .get_value_as_int(&format!("{pkgname}-bottom"))
                .unwrap();
            let column = model
                .get_value_as_int(&format!("{pkgname}-column"))
                .unwrap();
            (
                f64::from(column) * 10.0,
                f64::from(top),
                f64::from(bottom),
                pkgname,
            )
        });
        let edges = (0..instance.pkgs.len())
            .cartesian_product(0..instance.pkgs.len())
            .filter_map(|(from, to)| {
                let oracles: Vec<_> = instance
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
                    return None;
                }
                let pkga = &instance.pkgs[from].name;
                let pkgb = &instance.pkgs[to].name;

                let height = model
                    .get_value_as_int(&format!("edge-{pkga}-{pkgb}-height"))
                    .unwrap();
                let acolumn = model.get_value_as_int(&format!("{pkga}-column")).unwrap();
                let bcolumn = model.get_value_as_int(&format!("{pkgb}-column")).unwrap();

                Some((
                    f64::from(acolumn) * 10.0,
                    f64::from(bcolumn) * 10.0,
                    f64::from(height),
                    oracles,
                ))
            })
            .chain((0..instance.pkgs.len()).filter_map(|to| {
                let oracles: Vec<_> = instance
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
                    return None;
                }

                let pkgb = &instance.pkgs[to].name;

                let height = model
                    .get_value_as_int(&format!("edge---{pkgb}-height"))
                    .unwrap();
                let acolumn = model.get_value_as_int("--column").unwrap();
                let bcolumn = model.get_value_as_int(&format!("{pkgb}-column")).unwrap();

                Some((
                    f64::from(acolumn) * 10.0,
                    f64::from(bcolumn) * 10.0,
                    f64::from(height),
                    oracles,
                ))
            }));

        html! {
            svg role="img"
                width=(format!("{}rem", (width)*10))
                height=(format!("{}rem", height+1))
            {
                @for (column, top, bottom, pkgname) in pkgs {
                    rect x=(format!("{}rem", column))
                        y=(format!("{}rem", bottom))
                        width="6rem"
                        height=(format!("{}rem", top-bottom))
                        fill="transparent"
                        stroke="black"
                    {}
                    text x=(format!("{}rem", column+0.5))
                        y=(format!("{}rem", bottom+(top-bottom)/2.0+0.5))
                    {(pkgname)}
                }
                @for (acol, bcol, height, oracles) in edges {
                    line stroke="black"
                        x1=(format!("{}rem", acol+6.0))
                        x2=(format!("{}rem", bcol))
                        y1=(format!("{}rem", height))
                        y2=(format!("{}rem", height))
                    {}
                    @for (id, oracle) in oracles.into_iter().enumerate() {
                        text font-size="75%"
                            x=(format!("{}rem", acol+6.0))
                            y=(format!("{}rem", height))
                            dy=(format!("{}rem", 0.5*(id as f64)))
                        {(oracle)}
                    }
                }
            }
        }
    })
}
