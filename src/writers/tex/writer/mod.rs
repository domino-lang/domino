use std::fs::File;
use std::io::Write;
use std::path::Path;

use itertools::MultiUnzip;

use crate::gamehops::GameHop;
use crate::package::{Composition, OracleDef, PackageInstance};
use crate::parser::ast::Identifier as _;
use crate::theorem::Theorem;
use crate::util::prover_process::ProverBackend;

use crate::writers::tex::{
    label::LatexLabel,
    tikzgraph::{ReductionGraph, TikzGraph},
};

pub(crate) mod block;

use block::BlockWriter;

pub fn tex_write_oracle(
    lossy: bool,
    oracle: &OracleDef,
    pkgname: &str,
    compname: &str,
    target: &Path,
) -> std::io::Result<String> {
    let fname = target.join(format!(
        "Oracle_{}_{}_in_{}{}.tex",
        pkgname,
        oracle.sig.name,
        compname,
        if lossy { "_lossy" } else { "" }
    ));
    let mut file = File::create(fname.clone())?;

    writeln!(
        file,
        "\\procedure{{$\\O{{{}}}({})$}}{{",
        oracle.sig.name.replace("_", "\\_"),
        oracle
            .sig
            .args
            .iter()
            .map(|(a, _)| { format!("\\n{{{}}}", a.replace("_", "\\_")) })
            .collect::<Vec<_>>()
            .join(", ")
    )?;

    let mut writer = BlockWriter::new(&mut file, lossy);
    let codeblock = &oracle.code;
    writer.write_codeblock(codeblock, 0)?;

    writeln!(file, "}}")?;
    Ok(fname.to_str().unwrap().to_string())
}

pub fn tex_write_package(
    lossy: bool,
    composition: &Composition,
    package: &PackageInstance,
    target: &Path,
) -> std::io::Result<String> {
    let fname = target.join(format!(
        "Package_{}_in_{}{}.tex",
        package.name,
        composition.name,
        if lossy { "_lossy" } else { "" }
    ));
    let mut file = File::create(fname.clone())?;

    writeln!(
        file,
        "\\begin{{pcvstack}}\\underline{{\\underline{{\\M{{{}}}}}}}\\\\\\begin{{pcvstack}}",
        package.name.replace('_', "\\_")
    )?;

    for oracle in &package.pkg.oracles {
        let oraclefname =
            tex_write_oracle(lossy, oracle, &package.name, &composition.name, target)?;
        let oraclefname = Path::new(&oraclefname)
            .strip_prefix(fname.clone().parent().unwrap())
            .unwrap()
            .to_str();
        writeln!(file, "\\input{{{}}}\\pcvspace", oraclefname.unwrap())?;
    }
    writeln!(file, "\\end{{pcvstack}}\\end{{pcvstack}}")?;

    Ok(fname.to_str().unwrap().to_string())
}

fn tex_write_document_header(mut file: &File) -> std::io::Result<()> {
    writeln!(file, "\\documentclass[a3paper]{{article}}")?;
    writeln!(file, "\\usepackage[margin=.25in]{{geometry}}")?;
    writeln!(
        file,
        "\\usepackage[sets,operators,adversary,advantage,probability]{{cryptocode}}"
    )?;
    writeln!(file, "\\usepackage{{tikz}}")?;
    writeln!(file, "\\usepackage{{amsmath}}")?;
    writeln!(file, "\\usepackage{{amsthm}}")?;
    writeln!(file, "\\usepackage{{hyperref}}")?;
    writeln!(file, "\\newcommand{{\\pcas}}{{~\\highlightkeyword{{as}}}}")?;
    writeln!(file, "\\newtheorem{{theorem}}{{Theorem}}")?;
    writeln!(file, "\\newtheorem{{claim}}{{Claim}}")?;
    writeln!(file, "\\theoremstyle{{definition}}")?;
    writeln!(file, "\\newtheorem{{definition}}{{Definition}}")?;
    writeln!(
        file,
        "\\newcommand\\lit[1]{{\\ensuremath{{\\mathtt{{#1}}}}}}"
    )?;
    writeln!(
        file,
        "\\renewcommand\\O[1]{{\\ensuremath{{\\mathsf{{#1}}}}}}"
    )?;
    writeln!(
        file,
        "\\newcommand{{\\M}}[1]{{\\ensuremath{{\\text{{\\texttt{{#1}}}}}}}}"
    )?;
    writeln!(
        file,
        "\\newcommand{{\\n}}[1]{{\\ensuremath{{\\mathit{{#1}}}}}}"
    )?;
    writeln!(file, "\\tikzstyle{{package}} = [inner sep=1pt,align=center,rounded corners,draw,minimum width=2cm,minimum height=1cm,font=\\small]")?;
    writeln!(file, "\\tikzstyle{{onarrow}} = [inner sep=1pt,font=\\scriptsize,anchor=west,at start,align=left,fill=white]")?;
    Ok(())
}

fn tex_write_composition_graph_file(
    backend: &Option<ProverBackend>,
    composition: &Composition,
    name: &str,
    target: &Path,
) -> std::io::Result<String> {
    let fname = target.join(format!("CompositionGraph_{name}.tex"));
    let mut file = File::create(fname.clone())?;

    write!(file, "{}", composition.tikz_graph(&backend.unwrap()))?;

    Ok(fname.to_str().unwrap().to_string())
}

pub fn tex_write_composition(
    backend: &Option<ProverBackend>,
    lossy: bool,
    composition: &Composition,
    name: &str,
    target: &Path,
) -> std::io::Result<()> {
    let fname = target.join(format!(
        "Composition_{}{}.tex",
        name,
        if lossy { "_lossy" } else { "" }
    ));
    let mut file = File::create(fname.clone())?;

    tex_write_document_header(&file)?;

    writeln!(file, "\\title{{{name} Game}}")?;
    writeln!(file, "\\begin{{document}}")?;
    writeln!(file, "\\maketitle")?;

    let graphfname = tex_write_composition_graph_file(backend, composition, name, target)?;
    let graphfname = Path::new(&graphfname)
        .strip_prefix(fname.clone().parent().unwrap())
        .unwrap()
        .to_str();
    writeln!(file, "\\begin{{center}}")?;
    writeln!(file, "\\input{{{}}}", graphfname.unwrap())?;
    writeln!(file, "\\end{{center}}")?;

    writeln!(file, "\\begin{{pchstack}}")?;
    for pkg in &composition.pkgs {
        let pkgfname = tex_write_package(lossy, composition, pkg, target)?;
        let pkgfname = Path::new(&pkgfname)
            .strip_prefix(fname.clone().parent().unwrap())
            .unwrap()
            .to_str();
        //writeln!(file, "\\begin{{center}}")?;
        writeln!(file, "\\input{{{}}}", pkgfname.unwrap())?;
        writeln!(file, "\\pchspace")?;
        //writeln!(file, "\\end{{center}}")?;
    }
    writeln!(file, "\\end{{pchstack}}")?;

    writeln!(file, "\\end{{document}}")?;

    Ok(())
}

pub fn tex_write_theorem(
    backend: &Option<ProverBackend>,
    lossy: bool,
    theorem: &Theorem,
    name: &str,
    target: &Path,
) -> std::io::Result<()> {
    let fname = target.join(format!(
        "Theorem_{}{}.tex",
        name,
        if lossy { "_lossy" } else { "" }
    ));
    let mut file = File::create(fname)?;

    tex_write_document_header(&file)?;

    writeln!(file, "\\title{{Theorem: {}}}", name.replace('_', "\\_"))?;
    writeln!(file, "\\begin{{document}}")?;
    writeln!(file, "\\maketitle")?;
    writeln!(file, "\\tableofcontents")?;
    writeln!(file, "\\clearpage")?;

    writeln!(file, "\\section{{Games}}")?;

    let mut fill = 0;
    for instance in &theorem.instances {
        let graphfname = format!(
            "CompositionGraph_{}.tex",
            instance.game_name().replace('_', "\\_")
        );

        writeln!(file, "\\begin{{minipage}}{{.245\\textwidth}}")?;
        writeln!(
            file,
            "\\subsection*{{\\hyperref[section:game:{}]{{{} Game}}}}",
            instance.name(),
            instance.name().replace('_', "\\_")
        )?;
        writeln!(file, "\\scalebox{{0.66}}{{\\input{{{graphfname}}}}}")?;
        writeln!(file, "\\end{{minipage}}")?;
        fill += 1;
        if fill == 4 {
            fill = 0;
            writeln!(file, "\\\\")?;
        }
    }

    writeln!(file, "\\clearpage")?;
    for instance in &theorem.instances {
        writeln!(
            file,
            "\\subsection{{{} Game}}",
            instance.name().replace('_', "\\_")
        )?;
        writeln!(file, "\\label{{section:game:{}}}", instance.name())?;

        let graphfname = format!(
            "CompositionGraph_{}.tex",
            instance.game_name().replace('_', "\\_")
        );
        writeln!(file, "\\begin{{center}}")?;
        writeln!(file, "\\input{{{graphfname}}}")?;
        writeln!(file, "\\end{{center}}")?;

        writeln!(file, "\\begin{{pchstack}}")?;
        for package in &instance.game().pkgs {
            let pkgfname = format!(
                "Package_{}_in_{}{}.tex",
                package.name.replace('_', "\\_"),
                instance.game().name.replace('_', "\\_"),
                if lossy { "_lossy" } else { "" }
            );
            //writeln!(file, "\\begin{{center}}")?;
            writeln!(file, "\\input{{{pkgfname}}}")?;
            //writeln!(file, "\\end{{center}}")?;
            writeln!(file, "\\pchspace")?;
        }
        writeln!(file, "\\end{{pchstack}}")?;
        writeln!(file, "\\clearpage")?;
    }

    writeln!(file, "\\section{{Advantages}}")?;

    for assumption in &theorem.assumptions {
        writeln!(file, "\\begin{{definition}}[{}]", assumption.name)?;
        writeln!(file, "\\label{{{}}}", assumption.latex_label("advantage"))?;
        let left = &assumption.left_name;
        let left_esc = left.replace('_', "\\_");
        let right = &assumption.right_name;
        let right_esc = right.replace('_', "\\_");
        write!(file, "For all adversaries $\\adv$, we define the asp-name advantage as\
                      \\[\
                      \\mathsf{{Adv}}(\\adv;{left},{right}):=\\abs{{\\begin{{array}}{{l}}\
                      \\phantom{{-}}\\prob{{1 = \\adv\\rightarrow {left}}}\\\\\
                      -\\prob{{1 = \\adv\\rightarrow {right}}}\
                      \\end{{array}}}},
                      \\]\
                      where {left_esc} and {right_esc} are defined in Sec.~\\ref{{section:game:{left}}} and Sec.~\\ref{{section:game:{right}}}, respectively.")?;
        writeln!(file, "\\end{{definition}}")?;
    }
    for thm in &theorem.proofs {
        writeln!(file, "\\begin{{definition}}[{}]", thm.name())?;
        writeln!(file, "\\label{{{}}}", thm.latex_label("advantage"))?;
        let left = thm.left_name();
        let left_esc = left.replace('_', "\\_");
        let right = thm.right_name();
        let right_esc = right.replace('_', "\\_");

        write!(file, "For all adversaries $\\adv$, we define the asp-name advantage as\
                      \\[\
                      \\mathsf{{Adv}}(\\adv;{left},{right}):=\\abs{{\\begin{{array}}{{l}}\
                      \\phantom{{-}}\\prob{{1 = \\adv\\rightarrow {left}}}\\\\\
                      -\\prob{{1 = \\adv\\rightarrow {right} }}\
                      \\end{{array}}}},
                      \\]\
                      where {left_esc} and {right_esc} are defined in Sec.~\\ref{{section:game:{left}}} and Sec.~\\ref{{section:game:{right}}}, respectively.")?;
        writeln!(file, "\\end{{definition}}")?;
    }

    for thm in &theorem.proofs {
        let thmname = thm.name();
        writeln!(file, "\\section{{Theorem: {thmname}}}",)?;

        let (reductions, reductiondefs, reductionadvs): (Vec<_>, Vec<_>, Vec<_>) = thm
            .reductions()
            .enumerate()
            .map(|(rednum, red)| {
                (
                    format!("$\\rdv_{{{}}}$", rednum + 1),
                    format!(
                        "reduction $\\rdv_{}$ is defined in Fig.~\\ref{{{}}}",
                        rednum + 1,
                        red.latex_label("figure")
                    ),
                    format!(
                        "\\mathsf{{Adv}}(\\adv\\rightarrow\\rdv_{{{}}},\\mathit{{{}}},\\mathit{{{}}})",
                        rednum+1,
                        red
                            .right()
                            .assumption_game_instance_name()
                            .as_str()
                            .replace('_', "\\_"),
                        red
                            .left()
                            .assumption_game_instance_name()
                            .as_str()
                            .replace('_', "\\_"),
                    ),
                )
            })
            .multiunzip();
        let reductions = reductions.join(", ");
        let reductiondefs = reductiondefs.join(", ");
        let reductionadvs = reductionadvs.join(" \\\\+ &");
        let adv = format!(
            "\\mathsf{{Adv}}(\\adv, {}, {}))",
            thm.left_name().replace('_', "\\_"),
            thm.right_name().replace('_', "\\_")
        );

        write!(
            file,
            "\\begin{{theorem}}[{thmname}]\n\
             We prove that for all adversaries $\\adv$, \
             there are reductions {reductions} \
             such that \\begin{{align*}}{adv} \\leq &{reductionadvs}\\end{{align*}} where {reductiondefs}\n\
             \\end{{theorem}}\n",
        )?;

        let mut redcount = 1;
        for game_hop in thm.game_hops() {
            writeln!(file, "\\begin{{claim}}")?;
            match game_hop {
                GameHop::Equivalence(eq) => {
                    let left = eq.left_name().replace('_', "\\_");
                    let right = eq.right_name().replace('_', "\\_");
                    write!(file, "For all adversaries $\\adv$, \\[\\mathsf{{Adv}}(\\adv,\\mathit{{{left}}},\\mathit{{{right}}})=0.\\]")?;
                }
                GameHop::Conjecture(con) => {
                    let left = con.left_name().as_str().replace('_', "\\_");
                    let right = con.right_name().as_str().replace('_', "\\_");
                    write!(file, "For all adversaries $\\adv$, \\[\\mathsf{{Adv}}(\\adv,\\mathit{{{left}}},\\mathit{{{right}}})=0.\\]")?;
                }
                GameHop::Reduction(red) => {
                    let left_cons = red
                        .left()
                        .construction_game_instance_name()
                        .as_str()
                        .replace('_', "\\_");
                    let right_cons = red
                        .right()
                        .construction_game_instance_name()
                        .as_str()
                        .replace('_', "\\_");
                    let left_ass = red
                        .left()
                        .assumption_game_instance_name()
                        .as_str()
                        .replace('_', "\\_");
                    let right_ass = red
                        .right()
                        .assumption_game_instance_name()
                        .as_str()
                        .replace('_', "\\_");
                    let label = red.latex_label("figure");
                    write!(file, "For all adversaries $\\adv$, \\[\\mathsf{{Adv}}(\\adv,\\mathit{{{left_cons}}},\\mathit{{{right_cons}}})\
                                  \\leq \\mathsf{{Adv}}(\\adv\\rightarrow\\rdv_{{{redcount}}},\\mathit{{{left_ass}}},\\mathit{{{right_ass}}}),\\] \
                                  where $\\rdv_{{{redcount}}}$ is defined in Fig.~\\ref{{{label}}}.")?;
                    redcount += 1;
                }
            }
            writeln!(file, "\\end{{claim}}")?;
        }
    }

    for reduction in theorem.reductions() {
        let left_game_name = reduction.left().construction_game_instance_name();
        let left_game = theorem.find_game_instance(left_game_name.as_str()).unwrap();
        let right_game_name = reduction.right().construction_game_instance_name();
        let right_game = theorem
            .find_game_instance(right_game_name.as_str())
            .unwrap();

        writeln!(file, "\\begin{{figure}}")?;
        write!(
            file,
            "\\hfill{}",
            ReductionGraph {
                composition: left_game.game(),
                mapping: reduction.left()
            }
            .tikz_graph(&backend.unwrap())
        )?;
        write!(
            file,
            "\\hfill{}",
            ReductionGraph {
                composition: right_game.game(),
                mapping: reduction.right()
            }
            .tikz_graph(&backend.unwrap())
        )?;
        writeln!(
            file,
            "\\hfill\\caption{{Reduction: {} $\\approx$ {} assuming {}. \
             The sub-graphs corresponding to {} and {}, respectively, are highlighted in red. \
             The remaining graph constitutes the reduction.}}\\label{{{}}}",
            reduction
                .left()
                .construction_game_instance_name()
                .as_str()
                .replace('_', "\\_"),
            reduction
                .right()
                .construction_game_instance_name()
                .as_str()
                .replace('_', "\\_"),
            reduction.assumption_name(),
            reduction
                .left()
                .assumption_game_instance_name()
                .as_str()
                .replace('_', "\\_"),
            reduction
                .right()
                .assumption_game_instance_name()
                .as_str()
                .replace('_', "\\_"),
            reduction.latex_label("figure")
        )?;
        writeln!(file, "\\end{{figure}}")?;
    }

    if theorem.proofs.is_empty() {
        writeln!(file, "\\section{{Gamehops}}")?;
        for game_hop in &theorem.game_hops {
            match &game_hop {
                GameHop::Reduction(red) => {
                    writeln!(
                        file,
                        "\\subsection{{Reduction to {}}}",
                        red.assumption_name().replace('_', "\\_")
                    )?;

                    writeln!(
                        file,
                        "\\subsubsection{{Game {} with Assumption Game {} highlighted in red}}",
                        red.left()
                            .construction_game_instance_name()
                            .as_str()
                            .replace('_', "\\_"),
                        red.left()
                            .assumption_game_instance_name()
                            .as_str()
                            .replace('_', "\\_")
                    )?;
                    writeln!(file, "\\begin{{center}}")?;
                    let left_game_instance = theorem
                        .instances
                        .iter()
                        .find(|instance| {
                            instance.name() == red.left().construction_game_instance_name().as_str()
                        })
                        .unwrap();
                    write!(
                        file,
                        "{}",
                        ReductionGraph {
                            composition: left_game_instance.game(),
                            mapping: red.left()
                        }
                        .tikz_graph(&backend.unwrap())
                    )?;

                    writeln!(file, "\\end{{center}}")?;

                    writeln!(
                        file,
                        "\\subsubsection{{Game {} with Assumption Game {} highlighted  in red}}",
                        red.right()
                            .construction_game_instance_name()
                            .as_str()
                            .replace('_', "\\_"),
                        red.right()
                            .assumption_game_instance_name()
                            .as_str()
                            .replace('_', "\\_"),
                    )?;
                    writeln!(file, "\\begin{{center}}")?;
                    let right_game_instance = theorem
                        .instances
                        .iter()
                        .find(|instance| {
                            instance.name()
                                == red.right().construction_game_instance_name().as_str()
                        })
                        .unwrap();
                    write!(
                        file,
                        "{}",
                        ReductionGraph {
                            composition: right_game_instance.game(),
                            mapping: red.right()
                        }
                        .tikz_graph(&backend.unwrap())
                    )?;
                    writeln!(file, "\\end{{center}}")?;
                }
                GameHop::Equivalence(equiv) => {
                    writeln!(
                        file,
                        "\\subsection{{Equivalence between {} and {}}}",
                        equiv.left_name().replace('_', "\\_"),
                        equiv.right_name().replace('_', "\\_")
                    )?;
                }
                GameHop::Conjecture(con) => {
                    writeln!(
                        file,
                        "\\subsection{{Conjectured Equivalence between {} and {}}}",
                        con.left_name().as_str().replace('_', "\\_"),
                        con.right_name().as_str().replace('_', "\\_")
                    )?;
                }
            }
        }
    }

    writeln!(file, "\\end{{document}}")?;
    Ok(())
}
