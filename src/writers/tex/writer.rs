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
use crate::package::{Composition, Edge, Export, OracleDef, PackageInstance};
use crate::parser::ast::Identifier as _;
use crate::parser::package::ForComp;
use crate::parser::reduction::ReductionMappingEntry;
use crate::statement::{CodeBlock, InvokeOracleStatement, Statement};
use crate::theorem::Theorem;
use crate::types::CountSpec;
use crate::types::Type;
use crate::util::prover::process::ProverBackend;
use crate::util::prover::process::{Communicator, ProverResponse};
use crate::util::smtmodel::{SmtModel, SmtModelEntry};

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
    writeln!(file, "\\documentclass[a0paper]{{article}}")?;
    writeln!(file, "\\usepackage[margin=.25in]{{geometry}}")?;
    writeln!(file, "\\usepackage[sets,operators]{{cryptocode}}")?;
    writeln!(file, "\\usepackage{{tikz}}")?;
    writeln!(file, "\\usepackage{{hyperref}}")?;
    writeln!(file, "\\newcommand{{\\pcas}}{{~\\highlightkeyword{{as}}}}")?;
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

fn tex_solve_composition_graph(
    backend: &Option<ProverBackend>,
    composition: &Composition,
) -> Option<SmtModel> {
    use std::fmt::Write;

    let mut model;
    let write_model = |comm: &mut crate::util::prover::process::Communicator| {
        let mut edges: HashSet<(usize, usize)> = HashSet::new();

        writeln!(comm, "(declare-const num-pkgs Int)").unwrap();
        writeln!(comm, "(declare-const width Int)").unwrap();
        writeln!(comm, "(declare-const height Int)").unwrap();
        writeln!(comm, "(assert (= num-pkgs {}))", composition.pkgs.len()).unwrap();

        // Adversary
        writeln!(comm, "(declare-const --column Int)").unwrap();
        writeln!(comm, "(assert (= 0 --column))").unwrap();
        writeln!(comm, "(declare-const --top Int)").unwrap();
        writeln!(comm, "(declare-const --bottom Int)").unwrap();
        writeln!(comm, "(assert (< 0 --bottom (- --top 1) height))").unwrap();

        for i in 0..composition.pkgs.len() {
            let pkg = &composition.pkgs[i].name;
            writeln!(comm, "(declare-const {pkg}-column Int)").unwrap();
            writeln!(comm, "(assert (< 0 {pkg}-column width))").unwrap();
            writeln!(comm, "(declare-const {pkg}-top Int)").unwrap();
            writeln!(comm, "(declare-const {pkg}-bottom Int)").unwrap();
            writeln!(comm, "(assert (< 0 {pkg}-bottom (- {pkg}-top 1) height))").unwrap();
        }

        for Edge(from, to, _oracle) in &composition.edges {
            if edges.contains(&(*from, *to)) {
                continue;
            };
            edges.insert((*from, *to));
            let pkga = &composition.pkgs[*from].name;
            let pkgb = &composition.pkgs[*to].name;

            writeln!(comm, "(declare-const edge-{pkga}-{pkgb}-height Int)").unwrap();
            writeln!(
                comm,
                "(assert (< {pkga}-bottom edge-{pkga}-{pkgb}-height {pkga}-top))"
            )
            .unwrap();
            writeln!(
                comm,
                "(assert (< {pkgb}-bottom edge-{pkga}-{pkgb}-height {pkgb}-top))"
            )
            .unwrap();
            writeln!(comm, "(assert (< {pkga}-column {pkgb}-column))").unwrap();
        }

        for Export(to, _oracle) in &composition.exports {
            if edges.contains(&(usize::MAX, *to)) {
                continue;
            };
            edges.insert((usize::MAX, *to));
            let pkga = "-";
            let pkgb = &composition.pkgs[*to].name;

            writeln!(comm, "(declare-const edge-{pkga}-{pkgb}-height Int)").unwrap();
            writeln!(
                comm,
                "(assert (< {pkga}-bottom edge-{pkga}-{pkgb}-height {pkga}-top))"
            )
            .unwrap();
            writeln!(
                comm,
                "(assert (< {pkgb}-bottom edge-{pkga}-{pkgb}-height {pkgb}-top))"
            )
            .unwrap();
            writeln!(comm, "(assert (< {pkga}-column {pkgb}-column))").unwrap();
        }

        for i in 0..composition.pkgs.len() {
            for j in 0..i {
                let pkga = &composition.pkgs[i].name;
                let pkgb = &composition.pkgs[j].name;
                writeln!(
                    comm,
                    "
(assert (not (exists ((l Int))
               (and
                 (<= {pkga}-bottom l {pkga}-top)
                 (<= {pkgb}-bottom l {pkgb}-top)
                 (= {pkga}-column {pkgb}-column)))))"
                )
                .unwrap();
            }
        }

        for i in 0..composition.pkgs.len() {
            for Edge(from, to, _oracle) in &composition.edges {
                let pkga = &composition.pkgs[*from].name;
                let pkgb = &composition.pkgs[*to].name;
                let pkgc = &composition.pkgs[i].name;

                writeln!(
                    comm,
                    "
(assert (not (and (< {pkga}-column {pkgc}-column {pkgb}-column)
                  (< (- {pkgc}-bottom 1) edge-{pkga}-{pkgb}-height (+ {pkgc}-top 1)))))"
                )
                .unwrap();
            }
            for Export(to, _oracle) in &composition.exports {
                let pkga = "-";
                let pkgb = &composition.pkgs[*to].name;
                let pkgc = &composition.pkgs[i].name;

                writeln!(
                    comm,
                    "
(assert (not (and (<  {pkga}-column {pkgc}-column {pkgb}-column)
                  (< (- {pkgc}-bottom 1) edge-{pkga}-{pkgb}-height (+ {pkgc}-top 1)))))"
                )
                .unwrap();
            }
        }
    };

    let _min_width = 50;

    // Check if it is at all solvable
    let mut comm = Communicator::new(backend.unwrap()).unwrap();
    write_model(&mut comm);

    let mut max_width;
    let mut min_width = 0;
    if comm.check_sat().unwrap() != ProverResponse::Sat {
        return None;
    } else {
        model = comm.get_model().unwrap();
        let model = SmtModel::from_string(&model);
        let SmtModelEntry::IntEntry { value, .. } = model.get_value("width").unwrap();

        max_width = value;
    }

    let mut max_height = 0;
    let mut min_height = 0;
    let opt_width;
    loop {
        let mut comm = Communicator::new(backend.unwrap()).unwrap();

        let width = min_width + (max_width - min_width) / 2;
        write_model(&mut comm);
        writeln!(comm, "(assert (< width {width}))").unwrap();

        if comm.check_sat().unwrap() == ProverResponse::Sat {
            max_width = width;
            model = comm.get_model().unwrap();
            let model = SmtModel::from_string(&model);
            let SmtModelEntry::IntEntry { value, .. } = model.get_value("height").unwrap();

            max_height = value;
        } else {
            min_width = width;
        }
        if min_width + 1 == max_width {
            opt_width = max_width;
            break;
        }
    }

    if min_height != max_height {
        loop {
            let mut comm = Communicator::new(backend.unwrap()).unwrap();

            let height = min_height + (max_height - min_height) / 2;
            write_model(&mut comm);
            writeln!(comm, "(assert (< height {height}))").unwrap();
            writeln!(comm, "(assert (< width {opt_width}))").unwrap();

            if comm.check_sat().unwrap() == ProverResponse::Sat {
                max_height = height;
            } else {
                min_height = height;
            }
            if min_height + 1 == max_height {
                break;
            }
        }
    }

    if model.is_empty() {
        None
    } else {
        let model = SmtModel::from_string(&model);
        println!("{}\n{:#?}", composition.name, model);
        Some(model)
    }
}

fn tex_write_composition_graph(
    backend: &Option<ProverBackend>,
    mut file: &File,
    composition: &Composition,
    pkgmap: &[ReductionMappingEntry],
) -> std::io::Result<()> {
    let write_node = |mut file: &File,
                      pkgname: &str,
                      _compname: &str,
                      idx,
                      top,
                      bottom,
                      column|
     -> std::io::Result<()> {
        let fill = if pkgmap
            .iter()
            .any(|entry| pkgname == entry.assumption().as_str())
        {
            "red!50"
        } else {
            "white"
        };

        writeln!(
            file,
            "\\node[anchor=south west,align=center,package,minimum height={}cm,fill={fill}]
    (node{}) at ({},{})
    {{\\M{{{}}}}};",
            f64::from(top - bottom) / 2.0,
            idx,
            column * 4,
            f64::from(bottom) / 2.0,
            //compname.replace('_', "\\_"),
            pkgname.replace('_', "\\_")
        )?;
        Ok(())
    };

    let solution = tex_solve_composition_graph(backend, composition);

    if let Some(model) = solution {
        writeln!(file, "\\begin{{tikzpicture}}")?;
        //writeln!(file, "\\draw[gray!50,step=.5] (-1,-1) grid (10,5);")?;
        for i in 0..composition.pkgs.len() {
            let pkgname = &composition.pkgs[i].name;
            let SmtModelEntry::IntEntry { value: top, .. } =
                model.get_value(&format!("{pkgname}-top")).unwrap();
            let SmtModelEntry::IntEntry { value: bottom, .. } =
                model.get_value(&format!("{pkgname}-bottom")).unwrap();
            let SmtModelEntry::IntEntry { value: column, .. } =
                model.get_value(&format!("{pkgname}-column")).unwrap();

            write_node(file, pkgname, &composition.name, i, top, bottom, column)?;
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
                    file,
                    "\\draw[-latex,rounded corners]
    ({},{}) -- node[onarrow] {{{}}} ({},{});",
                    acolumn * 4 + 2,
                    height,
                    oracles,
                    bcolumn * 4,
                    height
                )?;
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
                file,
                "\\draw[-latex,rounded corners]
    ({},{}) -- node[onarrow] {{{}}} ({},{});",
                acolumn * 4 + 2,
                height,
                oracles,
                bcolumn * 4,
                height
            )?;
        }
        //writeln!(file, "\\draw[red,fill=red] (0,0) circle (.2);")?;
        writeln!(file, "\\end{{tikzpicture}}")?;
    } else {
        let mut printed = Vec::new();
        let mut newly = Vec::new();

        let mut tikzx = 0;
        let mut tikzy = 0;

        writeln!(file, "\\begin{{tikzpicture}}")?;
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
                    write_node(
                        file,
                        &composition.pkgs[i].name,
                        &composition.name,
                        i,
                        tikzy + 1,
                        tikzy,
                        tikzx,
                    )?;
                    newly.push(i);
                    tikzy -= 2;

                    for Edge(from, to, oracle) in &composition.edges {
                        if i == *from {
                            writeln!(file, "\\draw[-latex,rounded corners] (node{}) -- ($(node{}.east) + (1,0)$) |- node[onarrow] {{\\O{{{}}}}} (node{});", from, from, oracle.name, to)?;
                        }
                    }
                }
            }
            printed.append(&mut newly);
            tikzx -= 4;
            tikzy = tikzx / 4;
        }

        writeln!(
            file,
            "\\node[package] (nodea) at ({tikzx}, {tikzy}) {{$A$}};"
        )?;
        for Export(to, oracle) in &composition.exports {
            writeln!(file, "\\draw[-latex,rounded corners] (nodea) -- ($(nodea.east) + (1,0)$) |- node[onarrow] {{\\O{{{}}}}} (node{});", oracle.name, to)?;
        }
        writeln!(file, "\\end{{tikzpicture}}")?;
    }
    Ok(())
}

fn tex_write_composition_graph_file(
    backend: &Option<ProverBackend>,
    composition: &Composition,
    name: &str,
    target: &Path,
) -> std::io::Result<String> {
    let fname = target.join(format!("CompositionGraph_{name}.tex"));
    let file = File::create(fname.clone())?;

    tex_write_composition_graph(backend, &file, composition, &Vec::new())?;

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

    for game_hop in &theorem.game_hops {
        match &game_hop {
            GameHop::Reduction(red) => {
                writeln!(
                    file,
                    "\\section{{Reduction to {}}}",
                    red.assumption_name().replace('_', "\\_")
                )?;

                writeln!(
                    file,
                    "\\subsection{{Game {} with Assumption Game {} highlighted in red}}",
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
                tex_write_composition_graph(
                    backend,
                    &file,
                    left_game_instance.game(),
                    red.left().entries(),
                )?;
                writeln!(file, "\\end{{center}}")?;

                writeln!(
                    file,
                    "\\subsection{{Game {} with Assumption Game {} highlighted  in red}}",
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
                tex_write_composition_graph(
                    backend,
                    &file,
                    right_game_instance.game(),
                    red.right().entries(),
                )?;
                writeln!(file, "\\end{{center}}")?;
            }
            GameHop::Equivalence(equiv) => {
                writeln!(
                    file,
                    "\\section{{Equivalence between {} and {}}}",
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
