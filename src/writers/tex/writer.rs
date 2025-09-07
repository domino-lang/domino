// SPDX-License-Identifier: MIT OR Apache-2.0

use std::collections::HashSet;
use std::fs::File;
use std::io::Write;
use std::path::Path;

use crate::expressions::Expression;
use crate::gamehops::GameHop;
use crate::identifier::pkg_ident::PackageIdentifier;
use crate::identifier::pkg_ident::PackageOracleCodeLoopVarIdentifier;
use crate::identifier::Identifier;
use crate::package::{Composition, OracleDef, PackageInstance};
use crate::parser::ast::Identifier as _;
use crate::parser::package::ForComp;
use crate::statement::{CodeBlock, InvokeOracleStatement, Statement};
use crate::theorem::Theorem;
use crate::types::CountSpec;
use crate::types::Type;
use crate::util::prover_process::ProverBackend;

use super::{
    label::LatexLabel,
    tikzgraph::{ReductionGraph, TikzGraph},
};

// TODO: Move to struct so we can have verbose versions (e.g. writing types to expressions)

fn genindentation(cnt: u8) -> String {
    let mut acc = String::new();
    for _ in 0..cnt {
        acc = format!("{acc}\\pcind");
    }
    acc
}

struct BlockWriter<'a> {
    file: &'a mut File,
    lossy: bool,
}

impl<'a> BlockWriter<'a> {
    fn new(file: &'a mut File, lossy: bool) -> BlockWriter<'a> {
        BlockWriter { file, lossy }
    }

    fn ident_to_tex(&self, ident: &Identifier) -> String {
        format!("\\n{{{}}}", ident.ident().replace('_', "\\_"))
    }

    fn countspec_to_tex(&self, count_spec: &CountSpec) -> String {
        match count_spec {
            CountSpec::Identifier(identifier) => self.ident_to_tex(identifier),
            CountSpec::Literal(num) => format!("{num}"),
            CountSpec::Any => "*".to_string(),
        }
    }

    fn type_to_tex(&self, ty: &Type) -> String {
        match ty {
            Type::Bits(n) => format!("\\bin^{{{}}}", self.countspec_to_tex(n)),
            _ => format!("\\O{{{ty:?}}}"),
        }
    }

    fn type_to_tex_short(&self, ty: &Type) -> String {
        match ty {
            Type::Tuple(_) => "\\O{Tuple[..]}".to_string(),
            Type::Bits(n) => format!("\\bin^{{{}}}", self.countspec_to_tex(n)),
            _ => format!("\\O{{{ty:?}}}"),
        }
    }
    fn forcomp_to_tex(&self, forcomp: &ForComp) -> String {
        match forcomp {
            ForComp::Lt => "<",
            ForComp::Lte => "\\leq",
        }
        .to_string()
    }

    fn logic_to_matrix(&self, join: &str, list: &[String]) -> String {
        assert!(list.len() > 1);
        let trivial = list.join(join);
        if trivial.len() < 50 {
            trivial
        } else {
            let mut it = list.iter();
            let mut lines = vec![format!("\\phantom{{{}}}{}", join, it.next().unwrap())];
            let mut rest: Vec<_> = it.map(|s| format!("{join}{s}")).collect();
            lines.append(&mut rest);
            format!(
                "\\begin{{array}}{{c}}{}\\end{{array}}",
                lines.join("\\pclb")
            )
        }
    }

    fn list_to_matrix(&self, list: &[String]) -> String {
        let mut it = list.iter();
        let mut lines = Vec::new();
        let mut line = Vec::new();
        let mut len = 0;
        loop {
            // maybe this should be a minipage and latex figures linesbreaking ...
            match it.next() {
                None => {
                    if !line.is_empty() {
                        lines.push(line.join(", "));
                    }
                    break;
                }
                Some(s) => {
                    if len + s.len() > 20 {
                        line.push(String::new());
                        lines.push(line.join(", "));
                        line = Vec::new();
                        len = 0;
                    }
                    line.push(s.clone());
                    len = len + std::cmp::max(6, s.len()) - 4 // latex makes string length and text length quite different
                }
            }
        }
        format!(
            "\\begin{{array}}{{c}}{}\\end{{array}}",
            lines.join("\\pclb")
        )
    }

    fn expression_to_tex(&self, expr: &Expression) -> String {
        match expr {
            Expression::Bot => "\\bot".to_string(),
            Expression::IntegerLiteral(val) => format!("{val}"),
            Expression::BooleanLiteral(val) => format!("\\lit{{{val}}}"),
            Expression::Identifier(ident) => self.ident_to_tex(ident),
            Expression::Not(expr) => format!("\\neg {}", self.expression_to_tex(expr)),
            Expression::Unwrap(expr) => {
                if self.lossy {
                    self.expression_to_tex(expr)
                } else {
                    format!(
                        "\\O{{unwrap}}\\left({}\\right)",
                        self.expression_to_tex(expr)
                    )
                }
            }
            Expression::Some(expr) => {
                if self.lossy {
                    self.expression_to_tex(expr)
                } else {
                    format!("\\O{{some}}\\left({}\\right)", self.expression_to_tex(expr))
                }
            }
            Expression::None(ty) => {
                if self.lossy {
                    "\\bot".to_string()
                } else {
                    format!("\\O{{none}}\\left({}\\right)", self.type_to_tex_short(ty))
                }
            }
            Expression::Add(lhs, rhs) => format!(
                "({} + {})",
                self.expression_to_tex(lhs),
                self.expression_to_tex(rhs)
            ),
            Expression::TableAccess(ident, expr) => format!(
                "{}[{}]",
                self.ident_to_tex(ident),
                self.expression_to_tex(expr)
            ),
            Expression::Equals(exprs) => exprs
                .iter()
                .map(|expr| self.expression_to_tex(expr))
                .collect::<Vec<_>>()
                .join(" = "),
            Expression::Or(exprs) => format!(
                "\\left({}\\right)",
                self.logic_to_matrix(
                    " \\vee ",
                    &exprs
                        .iter()
                        .map(|expr| self.expression_to_tex(expr))
                        .collect::<Vec<_>>()
                )
            ),
            Expression::And(exprs) => format!(
                "\\left({}\\right)",
                self.logic_to_matrix(
                    " \\wedge ",
                    &exprs
                        .iter()
                        .map(|expr| self.expression_to_tex(expr))
                        .collect::<Vec<_>>()
                )
            ),
            Expression::Tuple(exprs) => {
                format!(
                    "\\left({}\\right)",
                    self.list_to_matrix(
                        &exprs
                            .iter()
                            .map(|expr| self.expression_to_tex(expr))
                            .collect::<Vec<_>>()
                    )
                )
            }
            Expression::FnCall(name, args) => {
                format!(
                    "\\O{{{}}}({})",
                    self.ident_to_tex(name),
                    args.iter()
                        .map(|expr| self.expression_to_tex(expr))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            _ => {
                format!("{expr:?}")
            }
        }
    }

    fn write_statement(&mut self, statement: &Statement, indentation: u8) -> std::io::Result<()> {
        match &statement {
            Statement::Abort(_) => {
                writeln!(self.file, "{} \\pcabort\\\\", genindentation(indentation))?;
            }
            Statement::Return(None, _) => {
                writeln!(self.file, "{} \\pcreturn\\\\", genindentation(indentation))?;
            }
            Statement::Return(Some(expr), _) => {
                writeln!(
                    self.file,
                    "{} \\pcreturn {}\\\\",
                    genindentation(indentation),
                    self.expression_to_tex(expr)
                )?;
            }
            Statement::Assign(ident, None, expr, _) => {
                writeln!(
                    self.file,
                    "{} {} \\gets {}\\\\",
                    genindentation(indentation),
                    self.ident_to_tex(ident),
                    self.expression_to_tex(expr)
                )?;
            }
            Statement::Assign(ident, Some(idxexpr), expr, _) => {
                writeln!(
                    self.file,
                    "{} {}[{}] \\gets {}\\\\",
                    genindentation(indentation),
                    self.ident_to_tex(ident),
                    self.expression_to_tex(idxexpr),
                    self.expression_to_tex(expr)
                )?;
            }
            Statement::Parse(ids, expr, _) => {
                writeln!(
                    self.file,
                    "{}\\pcparse {} \\pcas \\left({}\\right)\\\\",
                    genindentation(indentation),
                    self.expression_to_tex(expr),
                    self.list_to_matrix(
                        &ids.iter()
                            .map(|ident| self.ident_to_tex(ident))
                            .collect::<Vec<_>>()
                    )
                )?;
            }
            Statement::IfThenElse(ite) => {
                if ite.then_block.0.is_empty()
                    && ite.else_block.0.len() == 1
                    && matches!(ite.else_block.0[0], Statement::Abort(_))
                {
                    // Special Case for asserts
                    writeln!(
                        self.file,
                        "{}\\pcassert {} \\\\",
                        genindentation(indentation),
                        self.expression_to_tex(&ite.cond)
                    )?;
                } else {
                    //default
                    writeln!(
                        self.file,
                        "{}\\pcif {} \\pcthen\\\\",
                        genindentation(indentation),
                        self.expression_to_tex(&ite.cond)
                    )?;
                    self.write_codeblock(&ite.then_block, indentation + 1)?;
                    if !ite.else_block.0.is_empty() {
                        writeln!(self.file, "{}\\pcelse\\\\", genindentation(indentation))?;
                        self.write_codeblock(&ite.else_block, indentation + 1)?;
                    }
                }
            }
            Statement::For(var, from, to, code, _) => {
                println!("{var:?}");
                if let Identifier::PackageIdentifier(PackageIdentifier::CodeLoopVar(
                    PackageOracleCodeLoopVarIdentifier {
                        start_comp,
                        end_comp,
                        ..
                    },
                )) = var
                {
                    writeln!(
                        self.file,
                        "{}\\pcfor {} {} {} {} {} \\pcdo\\\\",
                        genindentation(indentation),
                        self.expression_to_tex(from),
                        self.forcomp_to_tex(start_comp),
                        self.ident_to_tex(var),
                        self.forcomp_to_tex(end_comp),
                        self.expression_to_tex(to)
                    )?;
                    self.write_codeblock(code, indentation + 1)?;
                } else {
                    unreachable!();
                }
            }
            Statement::Sample(ident, None, _, ty, Some(sample_name), _) => {
                writeln!(
                    self.file,
                    "{}{} \\stackrel{{{}}}{{\\sample}} {}\\\\",
                    genindentation(indentation),
                    self.ident_to_tex(ident),
                    sample_name,
                    self.type_to_tex(ty)
                )?;
            }
            Statement::Sample(ident, Some(idxexpr), _, ty, Some(sample_name), _) => {
                writeln!(
                    self.file,
                    "{}{}[{}] \\stackrel{{{}}}{{\\samples}} {}\\\\",
                    genindentation(indentation),
                    self.ident_to_tex(ident),
                    self.expression_to_tex(idxexpr),
                    sample_name,
                    self.type_to_tex(ty)
                )?;
            }
            Statement::Sample(_, _, _, _, None, _) => {
                unreachable!("Expected sample name")
            }
            Statement::InvokeOracle(InvokeOracleStatement {
                id: ident,
                opt_idx: None,
                name,
                args,
                target_inst_name: Some(target_inst_name),
                ty: _,
                ..
            }) => {
                writeln!(self.file,
                         "{}{} \\stackrel{{\\mathsf{{\\tiny{{invoke}}}}}}{{\\gets}} \\O{{{}}}({}) \\pccomment{{Pkg: {}}} \\\\",
                         genindentation(indentation),
                         self.ident_to_tex(ident), name.replace("_", "\\_"),
                         args.iter().map(|expr| self.expression_to_tex(expr)).collect::<Vec<_>>().join(", "),
                         target_inst_name.replace('_',"\\_")
                )?;
            }
            Statement::InvokeOracle(InvokeOracleStatement {
                id: ident,
                opt_idx: Some(idxexpr),
                name,
                args,
                target_inst_name: Some(target_inst_name),
                ty: _,
                ..
            }) => {
                writeln!(self.file,
                         "{}{}[{}] \\stackrel{{\\mathsf{{\\tiny invoke}}}}{{\\gets}} \\O{{{}}}({}) \\pccomment{{Pkg: {}}} \\\\",
                         genindentation(indentation),
                         self.ident_to_tex(ident),
                         self.expression_to_tex(idxexpr),
                         name.replace("_", "\\_"),
                         args.iter().map(|expr| self.expression_to_tex(expr)).collect::<Vec<_>>().join(", "),
                         target_inst_name.replace('_',"\\_")
                )?;
            }
            Statement::InvokeOracle(InvokeOracleStatement {
                target_inst_name: None,
                ..
            }) => {
                unreachable!("Expect oracle-lowlevelified input")
            }
        }
        Ok(())
    }

    fn write_codeblock(&mut self, codeblock: &CodeBlock, indentation: u8) -> std::io::Result<()> {
        for stmt in &codeblock.0 {
            self.write_statement(stmt, indentation)?
        }
        Ok(())
    }
}

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
    let mut writer = BlockWriter::new(&mut file, lossy);

    writeln!(
        writer.file,
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

    let codeblock = &oracle.code;
    writer.write_codeblock(codeblock, 0)?;

    writeln!(writer.file, "}}")?;
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
    writeln!(file, "\\usepackage[sets,operators,adversary]{{cryptocode}}")?;
    writeln!(file, "\\usepackage{{tikz}}")?;
    writeln!(file, "\\usepackage{{amsmath}}")?;
    writeln!(file, "\\usepackage{{amsthm}}")?;
    writeln!(file, "\\usepackage{{hyperref}}")?;
    writeln!(file, "\\newcommand{{\\pcas}}{{~\\highlightkeyword{{as}}}}")?;
    writeln!(file, "\\newtheorem{{theorem}}{{Theorem}}")?;
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

    writeln!(file, "\\section{{Games}}")?;

    let mut fill = 0;
    for instance in &theorem.instances {
        let graphfname = format!(
            "CompositionGraph_{}.tex",
            instance.game_name().replace('_', "\\_")
        );

        writeln!(file, "\\begin{{minipage}}{{.33\\textwidth}}")?;
        writeln!(
            file,
            "\\subsection*{{\\hyperref[{} Game]{{{} Game}}}}",
            instance.name(),
            instance.name().replace('_', "\\_")
        )?;
        writeln!(file, "\\input{{{graphfname}}}")?;
        writeln!(file, "\\end{{minipage}}")?;
        fill += 1;
        if fill == 3 {
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
        writeln!(file, "\\label{{{} Game}}", instance.name())?;

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

    for thm in &theorem.theorems {
        writeln!(file, "\\section{{Theorem: {}}}", thm.name())?;

        let (reductions, reductiondefs): (Vec<_>, Vec<_>) = thm
            .reductions()
            .enumerate()
            .map(|(rednum, red)| {
                (
                    format!("$\\rdv_{}$", rednum + 1),
                    format!(
                        "reduction $\\rdv_{}$ is defined in Fig.~\\ref{{{}}}",
                        rednum + 1,
                        red.latex_label("figure")
                    ),
                )
            })
            .unzip();
        let reductions = reductions.join(", ");
        let reductiondefs = reductiondefs.join(", ");

        write!(
            file,
            "\\begin{{theorem}}\n\
             We prove that for all adversaries $\\adv$, \
             there are reductions {reductions} \
             such that {{\\color{{red}}todo: advantage-relation}} where {reductiondefs}\n\
             \\end{{theorem}}\n",
        )?;
    }

    for reduction in theorem.reductions() {
        let left_game_name = reduction.left().construction_game_instance_name();
        let left_game = theorem.find_game_instance(left_game_name.as_str()).unwrap();
        let right_game_name = reduction.right().construction_game_instance_name();
        let right_game = theorem
            .find_game_instance(right_game_name.as_str())
            .unwrap();

        writeln!(file, "\\begin{{figure}}")?;
        writeln!(
            file,
            "{}",
            ReductionGraph {
                composition: left_game.game(),
                mapping: reduction.left()
            }
            .tikz_graph(&backend.unwrap())
        )?;
        writeln!(
            file,
            "{}",
            ReductionGraph {
                composition: right_game.game(),
                mapping: reduction.right()
            }
            .tikz_graph(&backend.unwrap())
        )?;
        writeln!(
            file,
            "\\caption{{Reduction: {} $\\approx$ {} assuming {}}}\\label{{{}}}",
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
            reduction.latex_label("figure")
        )?;
        writeln!(file, "\\end{{figure}}")?;
    }

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
                        instance.name() == red.right().construction_game_instance_name().as_str()
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
            GameHop::Conjecture(conj) => {
                writeln!(
                    file,
                    "\\section{{Conjectured Indistinguishability between {} and {}}}",
                    conj.left_name().as_str().replace('_', "\\_"),
                    conj.right_name().as_str().replace('_', "\\_")
                )?;
            }
        }
    }

    writeln!(file, "\\end{{document}}")?;
    Ok(())
}
