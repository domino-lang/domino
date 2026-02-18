// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::project;
use std::io::Write;

use crate::parser::{Rule, SspParser};
use pest::iterators::Pair;

mod context;

use context::FormatContext;

fn create_oracle_sig(
    ctx: &mut FormatContext,
    prefix: &str,
    suffix: &str,
    name: &str,
    args: &[String],
    ty: &str,
) {
    let one_line = format!("{}{}({}){}{}", prefix, name, args.join(", "), ty, suffix);
    if one_line.len() > 80 {
        ctx.push_line(&format!("{prefix}{name}("));
        ctx.add_indent();
        ctx.push_lines(&args.join(",\n").split('\n').collect::<Vec<_>>());
        ctx.remove_indent();
        ctx.push_line(&format!("){ty}{suffix}"));
    } else {
        ctx.push_line(&one_line);
    }
}

fn format_oracle_sig(
    ctx: &mut FormatContext,
    oracle_sig_ast: Pair<Rule>,
) -> Result<(), project::error::Error> {
    let mut inner = oracle_sig_ast.into_inner();
    let name = inner.next().unwrap().as_str();
    let maybe_arglist = inner.next().unwrap();
    let args = if maybe_arglist.as_str() == "" {
        vec![]
    } else {
        let arglist = maybe_arglist.into_inner().next().unwrap();
        arglist
            .into_inner()
            .map(|arg| {
                let mut inner = arg.into_inner();
                let id = inner.next().unwrap().as_str();
                let ty = format_type(inner.next().unwrap())?;
                Ok(format!("{id}: {ty}"))
            })
            .collect::<Result<Vec<String>, project::error::Error>>()?
    };

    let maybe_ty = inner.next();
    let ty = match maybe_ty {
        None => "",
        Some(t) => {
            let typestr = format_type(t)?;
            if typestr == "()" {
                ""
            } else {
                &format!(" -> {typestr}")
            }
        }
    };

    create_oracle_sig(ctx, "oracle ", " {", name, &args, ty);
    Ok(())
}

fn format_type(ty_ast: Pair<Rule>) -> Result<String, project::error::Error> {
    Ok(match ty_ast.as_rule() {
        Rule::type_tuple => {
            let inner = ty_ast
                .into_inner()
                .map(|t| format_type(t))
                .collect::<Result<Vec<_>, _>>()?
                .join(", ");
            format!("({inner})")
        }
        Rule::type_table => {
            let mut inner = ty_ast.into_inner();
            let indextype = format_type(inner.next().unwrap())?;
            let valuetype = format_type(inner.next().unwrap())?;
            format!("Table({indextype}, {valuetype})")
        }
        _ => ty_ast.as_str().to_owned(),
    })
}

fn format_pattern(pattern: Pair<Rule>) -> Result<String, project::error::Error> {
    Ok(match pattern.as_rule() {
        Rule::pattern_ident => pattern.as_str().to_string(),
        Rule::pattern_table => {
            let mut inner = pattern.into_inner();
            let ident = inner.next().unwrap().as_str();
            let index = format_expr(inner.next().unwrap())?;
            format!("{ident}[{index}]")
        }
        Rule::pattern_tuple => {
            let idents: Vec<_> = pattern
                .into_inner()
                .map(|p| format_pattern(p))
                .collect::<Result<_, _>>()?;
            format!("({})", idents.join(", "))
        }
        _ => unreachable!("unexpected pattern rule: {:?}", pattern.as_rule()),
    })
}

fn format_oracle_expr(oracle_expr: Pair<Rule>) -> Result<String, project::error::Error> {
    Ok(match oracle_expr.as_rule() {
        Rule::oracle_expr_sample => {
            let mut inner = oracle_expr.into_inner();
            let ty = inner.next().unwrap().as_str();

            // Check for optional sample_name
            let sample_name_part = if let Some(name) = inner.next() {
                format!(" sample-name {}", name.as_str())
            } else {
                String::new()
            };

            // Format with $ to match the nicer-looking <-$ syntax
            format!("${ty}{sample_name_part}")
        }
        Rule::oracle_expr_invoke => {
            let mut inner = oracle_expr.into_inner();
            let oracle_call = inner.next().unwrap();
            let mut call_inner = oracle_call.into_inner();
            let oracle_name = call_inner.next().unwrap().as_str();

            let mut argstring = String::new();
            for ast in call_inner {
                let arglist: Vec<_> = ast
                    .into_inner()
                    .map(|expr| format_expr(expr))
                    .collect::<Result<_, _>>()?;
                argstring.push_str(&arglist.join(", "));
            }

            format!("invoke {oracle_name}({argstring})")
        }
        _ => {
            // It's a regular expression
            format_expr(oracle_expr)?
        }
    })
}

fn format_expr(expr_ast: Pair<Rule>) -> Result<String, project::error::Error> {
    Ok(match expr_ast.as_rule() {
        Rule::expr_add => {
            let mut inner = expr_ast.into_inner();
            let lhs = format_expr(inner.next().unwrap())?;
            let rhs = format_expr(inner.next().unwrap())?;
            format!("({lhs} + {rhs})")
        }
        Rule::expr_sub => {
            let mut inner = expr_ast.into_inner();
            let lhs = format_expr(inner.next().unwrap())?;
            let rhs = format_expr(inner.next().unwrap())?;
            format!("({lhs} - {rhs})")
        }
        Rule::expr_equals => {
            let concat_expr = expr_ast
                .into_inner()
                .map(|expr| format_expr(expr))
                .collect::<Result<Vec<_>, _>>()?
                .join(" == ");
            format!("({concat_expr})")
        }
        Rule::expr_not_equals => {
            let concat_expr = expr_ast
                .into_inner()
                .map(|expr| format_expr(expr))
                .collect::<Result<Vec<_>, _>>()?
                .join(" != ");
            format!("({concat_expr})")
        }
        Rule::expr_or => {
            let concat_expr = expr_ast
                .into_inner()
                .map(|expr| format_expr(expr))
                .collect::<Result<Vec<_>, _>>()?
                .join(" or ");
            format!("({concat_expr})")
        }
        Rule::expr_xor => {
            let concat_expr = expr_ast
                .into_inner()
                .map(|expr| format_expr(expr))
                .collect::<Result<Vec<_>, _>>()?
                .join(" xor ");
            format!("({concat_expr})")
        }
        Rule::expr_and => {
            let concat_expr = expr_ast
                .into_inner()
                .map(|expr| format_expr(expr))
                .collect::<Result<Vec<_>, _>>()?
                .join(" and ");
            format!("({concat_expr})")
        }
        Rule::expr_tuple => {
            let concat_expr = expr_ast
                .into_inner()
                .map(|expr| format_expr(expr))
                .collect::<Result<Vec<_>, _>>()?
                .join(", ");
            format!("({concat_expr})")
        }
        Rule::expr_not => {
            let inner = format_expr(expr_ast.into_inner().next().unwrap())?;
            format!("not {inner}")
        }
        Rule::expr_none => {
            let inner = format_type(expr_ast.into_inner().next().unwrap())?;
            format!("None as {inner}")
        }
        Rule::expr_untyped_none => "None".to_string(),
        Rule::expr_some => {
            let inner = format_expr(expr_ast.into_inner().next().unwrap())?;
            format!("Some({inner})")
        }
        Rule::expr_unwrap => {
            let inner = format_expr(expr_ast.into_inner().next().unwrap())?;
            format!("Unwrap({inner})")
        }
        Rule::expr_newtable => {
            let mut inner = expr_ast.into_inner();
            let idxty = format_type(inner.next().unwrap())?;
            let valty = format_type(inner.next().unwrap())?;
            format!("new Table({idxty}, {valty})")
        }
        Rule::fn_call => {
            let mut inner = expr_ast.into_inner();
            let ident = inner.next().unwrap().as_str();
            let args = match inner.next() {
                None => vec![],
                Some(inner_args) => inner_args
                    .into_inner()
                    .map(|expr| format_expr(expr))
                    .collect::<Result<_, _>>()?,
            }
            .join(", ");
            format!("{ident}({args})")
        }
        Rule::literal_boolean | Rule::literal_integer => expr_ast.as_str().trim().to_string(),
        Rule::identifier => {
            let name = expr_ast.as_str();
            name.to_owned()
        }
        Rule::table_access => {
            let mut inner = expr_ast.into_inner();
            let ident_ast = inner.next().unwrap();
            let ident = ident_ast.as_str();
            let idx_expr = format_expr(inner.next().unwrap())?;
            format!("{ident}[{idx_expr}]")
        }
        _ => unreachable!("Unhandled expression {:#?}", expr_ast),
    })
}

fn format_code(ctx: &mut FormatContext, code_ast: Pair<Rule>) -> Result<(), project::error::Error> {
    for stmt in code_ast.into_inner() {
        match stmt.as_rule() {
            Rule::ite => {
                let mut inner = stmt.into_inner();
                let cond_expr = format_expr(inner.next().unwrap())?;

                ctx.push_line(&format!("if {cond_expr} {{"));
                ctx.add_indent();
                format_code(ctx, inner.next().unwrap())?;
                ctx.remove_indent();

                match inner.next() {
                    None => {}
                    Some(c) => {
                        ctx.push_line("} else {");
                        ctx.add_indent();
                        format_code(ctx, c)?;
                        ctx.remove_indent();
                    }
                }

                ctx.push_line("}");
            }
            Rule::return_stmt => {
                let mut inner = stmt.into_inner();

                match inner.next() {
                    None => {
                        ctx.push_line("return;");
                    }
                    Some(e) => {
                        ctx.push_line(&format!("return {};", format_expr(e)?));
                    }
                }
            }
            Rule::assert => {
                let mut inner = stmt.into_inner();

                ctx.push_line(&format!("assert {};", format_expr(inner.next().unwrap())?));
            }
            Rule::abort => {
                ctx.push_line("abort;");
            }
            Rule::invoke_stmt => {
                let mut inner = stmt.into_inner();
                let oracle_call = inner.next().unwrap();
                let mut call_inner = oracle_call.into_inner();
                let oracle_name = call_inner.next().unwrap().as_str();

                let mut argstring = String::new();
                for ast in call_inner {
                    let arglist: Vec<_> = ast
                        .into_inner()
                        .map(format_expr)
                        .collect::<Result<_, _>>()?;
                    argstring.push_str(&arglist.join(", "));
                }

                ctx.push_line(&format!("invoke {oracle_name}({argstring});"));
            }
            Rule::assign => {
                let mut inner = stmt.into_inner();
                let pattern_ast = inner.next().unwrap();
                let oracle_expr_ast = inner.next().unwrap();

                // Format the pattern (left-hand side)
                let lhs = format_pattern(pattern_ast)?;

                // Format the oracle expression (right-hand side)
                let rhs = format_oracle_expr(oracle_expr_ast)?;

                ctx.push_line(&format!("{lhs} <- {rhs};"));
            }
            Rule::for_ => {
                let mut parsed: Vec<Pair<Rule>> = stmt.into_inner().collect();
                let decl_var_name = parsed[0].as_str();
                let lower_bound = format_expr(parsed.remove(1))?;
                let lower_bound_type = parsed[1].as_str();
                let upper_bound_type = parsed[3].as_str();
                let upper_bound = format_expr(parsed.remove(4))?;
                let loopvar = decl_var_name.to_string();

                ctx.push_line(&format!("for {loopvar}: {lower_bound} {lower_bound_type} {loopvar} {upper_bound_type} {upper_bound} {{"));
                ctx.add_indent();

                format_code(ctx, parsed.remove(4))?;

                ctx.remove_indent();
                ctx.push_line("}");
            }
            _ => {
                unreachable!("{:#?}", stmt)
            }
        }
    }

    Ok(())
}

fn format_oracle_def(
    ctx: &mut FormatContext,
    oracle_def_ast: Pair<Rule>,
) -> Result<(), project::error::Error> {
    let mut inner = oracle_def_ast.into_inner();

    ctx.push_line("");
    format_oracle_sig(ctx, inner.next().unwrap())?;
    ctx.add_indent();

    format_code(ctx, inner.next().unwrap())?;

    ctx.remove_indent();
    ctx.push_line("}");

    Ok(())
}

fn format_types_block(
    ctx: &mut FormatContext,
    types_ast: Pair<Rule>,
) -> Result<(), project::error::Error> {
    let inner = types_ast.into_inner();
    for typeentry in inner {
        //println!("{:?}", inner);
        let typename = typeentry.as_str();
        //let typedef = format_type(inner.next().unwrap())?;
        ctx.push_line(&format!("{typename},"));
    }
    Ok(())
}

fn format_decl_list(
    ctx: &mut FormatContext,
    decl_list_ast: Pair<Rule>,
) -> Result<(), project::error::Error> {
    for entry in decl_list_ast.into_inner() {
        let mut inner = entry.into_inner();
        let declname = inner.next().unwrap().as_str();
        let decldef = format_type(inner.next().unwrap())?;
        ctx.push_line(&format!("{declname}: {decldef},"));
    }
    Ok(())
}

fn format_import_oracles(
    ctx: &mut FormatContext,
    decl_list_ast: Pair<Rule>,
) -> Result<(), project::error::Error> {
    for entry in decl_list_ast.into_inner() {
        debug_assert!(matches!(entry.as_rule(), Rule::import_oracles_oracle_sig));
        let mut inner = entry.into_inner();
        let ident = inner.next().unwrap().as_str();
        let mut args = inner.next().unwrap();
        let ident = if !matches!(args.as_rule(), Rule::oracle_maybe_arglist) {
            let results = args
                .into_inner()
                .map(|pair| format_expr(pair))
                .collect::<Result<Vec<_>, _>>()?;
            args = inner.next().unwrap();
            &format!("{}[{}]", ident, results.join(", "))
        } else {
            ident
        };

        let args = args.into_inner().next();
        let args = if let Some(args) = args {
            args.into_inner()
                .map(|arg| {
                    let mut inner = arg.into_inner();
                    let arg = inner.next().unwrap().as_str();
                    let ty = format_type(inner.next().unwrap())?;
                    Ok::<String, project::error::Error>(format!("{arg}: {ty}"))
                })
                .collect::<Result<Vec<String>, _>>()?
        } else {
            Vec::new()
        };

        let return_type = inner.next();
        let return_type = match return_type {
            None => "",
            Some(t) => {
                let rettype = format_type(t)?;
                if rettype != "()" {
                    &format!(" -> {rettype}")
                } else {
                    ""
                }
            }
        };
        create_oracle_sig(ctx, "", ",", ident, &args, return_type);
    }
    Ok(())
}

fn format_pkg_spec(
    ctx: &mut FormatContext,
    pkg_spec_ast: Pair<Rule>,
) -> Result<(), project::error::Error> {
    // sort different types consistently when generating output
    let specs: Vec<_> = pkg_spec_ast.into_inner().collect();

    let types_rules: Vec<_> = specs
        .iter()
        .filter(|x| matches!(x.as_rule(), Rule::types))
        .collect();
    let params_rules: Vec<_> = specs
        .iter()
        .filter(|x| matches!(x.as_rule(), Rule::params))
        .collect();
    let state_rules: Vec<_> = specs
        .iter()
        .filter(|x| matches!(x.as_rule(), Rule::state))
        .collect();
    let import_rules: Vec<_> = specs
        .iter()
        .filter(|x| matches!(x.as_rule(), Rule::import_oracles))
        .collect();
    let oracle_def_rules: Vec<_> = specs
        .iter()
        .filter(|x| matches!(x.as_rule(), Rule::oracle_def))
        .collect();

    if !types_rules.is_empty() {
        ctx.push_line("types {");
        ctx.add_indent();
        for type_block in types_rules {
            let inner = type_block.clone().into_inner().next();
            if let Some(inner) = inner {
                format_types_block(ctx, inner)?;
            }
        }
        ctx.remove_indent();
        ctx.push_line("}");
        ctx.push_line("");
    }

    if !params_rules.is_empty() {
        ctx.push_line("params {");
        ctx.add_indent();
        for param_block in params_rules {
            let inner = param_block.clone().into_inner().next();
            if let Some(inner) = inner {
                format_decl_list(ctx, inner)?;
            }
        }
        ctx.remove_indent();
        ctx.push_line("}");
        ctx.push_line("");
    }

    if !state_rules.is_empty() {
        ctx.push_line("state {");
        ctx.add_indent();
        for state_block in state_rules {
            let inner = state_block.clone().into_inner().next();
            if let Some(inner) = inner {
                format_decl_list(ctx, inner)?;
            }
        }
        ctx.remove_indent();
        ctx.push_line("}");
        ctx.push_line("");
    }

    if !import_rules.is_empty() {
        ctx.push_line("import oracles {");
        ctx.add_indent();
        for import_block in import_rules {
            format_import_oracles(ctx, import_block.clone().into_inner().next().unwrap())?;
        }
        ctx.remove_indent();
        ctx.push_line("}");
        ctx.push_line("");
    }

    for oracle_def in oracle_def_rules {
        format_oracle_def(ctx, oracle_def.clone())?;
    }

    Ok(())
}

fn format_pkg(ctx: &mut FormatContext, pkg_ast: Pair<Rule>) -> Result<(), project::error::Error> {
    let mut inner = pkg_ast.into_inner();
    let pkg_name = inner.next().unwrap().as_str();
    let spec = inner.next().unwrap();

    ctx.push_line(&format!("package {pkg_name} {{"));
    ctx.add_indent();

    format_pkg_spec(ctx, spec)?;

    ctx.remove_indent();
    ctx.push_line("}");
    Ok(())
}

fn format_compose_rule(
    ctx: &mut FormatContext,
    compose: &Pair<Rule>,
) -> Result<(), project::error::Error> {
    debug_assert!(matches!(compose.as_rule(), Rule::compose_decl));
    let inner = compose.clone().into_inner();
    for compblock in inner {
        let mut compblock = compblock.into_inner();
        let importer = compblock.next().unwrap().as_str();
        let imports = compblock
            .next()
            .unwrap()
            .into_inner()
            .map(|pair| {
                let mut pairs = pair.into_inner();
                let oracle = pairs.next().unwrap().as_str();
                let package = pairs.next().unwrap().as_str();
                (oracle, package)
            })
            .collect::<Vec<_>>();
        ctx.push_line(&format!("{importer}: {{"));
        ctx.add_indent();
        for (oracle, package) in imports {
            ctx.push_line(&format!("{oracle}: {package},"));
        }
        ctx.remove_indent();
        ctx.push_line("}");
    }
    Ok(())
}

fn format_game_spec(
    ctx: &mut FormatContext,
    specs: &Vec<Pair<Rule>>,
) -> Result<(), project::error::Error> {
    let const_rules: Vec<_> = specs
        .iter()
        .filter(|x| matches!(x.as_rule(), Rule::const_decl))
        .collect();

    let compose_rules: Vec<_> = specs
        .iter()
        .filter(|x| matches!(x.as_rule(), Rule::compose_decl))
        .collect();

    for const_rule in const_rules {
        let mut inner = const_rule.clone().into_inner();
        let varname = inner.next().unwrap().as_str();
        let vartype = format_type(inner.next().unwrap())?;
        ctx.push_line(&format!("const {varname}: {vartype};"))
    }

    for spec in specs {
        match spec.as_rule() {
            Rule::const_decl => { /* handled separately */ }
            Rule::instance_decl => {
                ctx.push_line("");
                let mut inner = spec.clone().into_inner();
                let instname = inner.next().unwrap().as_str();
                let next = inner.next().unwrap();
                let gamename = next.as_str();
                ctx.push_line(&format!("instance {instname} = {gamename} {{"));
                ctx.add_indent();

                let instance_inner: Vec<_> = inner.next().unwrap().into_inner().collect();
                let params_rules: Vec<_> = instance_inner
                    .iter()
                    .filter(|x| matches!(x.as_rule(), Rule::params_def))
                    .collect();
                let types_rules: Vec<_> = instance_inner
                    .iter()
                    .filter(|x| matches!(x.as_rule(), Rule::types_def))
                    .collect();

                if !params_rules.is_empty() {
                    ctx.push_line("params {");
                    ctx.add_indent();
                    for param_block in params_rules {
                        let inner = param_block.clone().into_inner().next();
                        if let Some(inner) = inner {
                            for block in inner.into_inner() {
                                let mut inner = block.into_inner();
                                let paramname = inner.next().unwrap().as_str();
                                let paramexpr = format_expr(inner.next().unwrap())?;
                                ctx.push_line(&format!("{paramname}: {paramexpr},"))
                            }
                        }
                    }
                    ctx.remove_indent();
                    ctx.push_line("}");
                    ctx.push_line("");
                }

                if !types_rules.is_empty() {
                    ctx.push_line("types {");
                    ctx.add_indent();
                    for types_block in types_rules {
                        let inner = types_block.clone().into_inner().next();
                        if let Some(inner) = inner {
                            for block in inner.into_inner() {
                                let mut inner = block.into_inner();
                                let typealias = format_type(inner.next().unwrap())?;
                                let realtype = format_type(inner.next().unwrap())?;
                                ctx.push_line(&format!("{typealias}: {realtype},"))
                            }
                        }
                    }
                    ctx.remove_indent();
                    ctx.push_line("}");
                    ctx.push_line("");
                }
                ctx.remove_indent();
                ctx.push_line("}");
            }
            Rule::compose_decl => { /* handled separately */ }
            _ => {
                println!("unhandled rule in format_game_spec: {}", ctx.to_str());
                unreachable!("{:?}", spec)
            }
        }
    }

    if !compose_rules.is_empty() {
        ctx.push_line("compose {");
        ctx.add_indent();

        for compose_rule in compose_rules {
            format_compose_rule(ctx, compose_rule)?;
        }

        ctx.remove_indent();
        ctx.push_line("}");
    }
    Ok(())
}

fn format_game(ctx: &mut FormatContext, pkg_ast: Pair<Rule>) -> Result<(), project::error::Error> {
    let mut inner = pkg_ast.into_inner();
    let pkg_name = inner.next().unwrap().as_str();
    let spec = inner.next().unwrap();

    ctx.push_line(&format!("composition {pkg_name} {{"));
    ctx.add_indent();

    let specs: Vec<_> = spec.into_inner().collect();
    format_game_spec(ctx, &specs)?;

    ctx.remove_indent();
    ctx.push_line("}");
    Ok(())
}

pub fn format_file(file: &std::path::PathBuf) -> Result<(), project::error::Error> {
    //println!("{:?}", file);
    if file.is_dir() {
        for file in file.read_dir().unwrap() {
            format_file(&file?.path())?;
        }
        Ok(())
    } else {
        let file_content = std::fs::read_to_string(file)?;
        let mut handled = false;

        let absname = std::path::absolute(file)?;
        let dirname = absname.parent().unwrap();
        let mut target = tempfile::NamedTempFile::new_in(dirname)?;
        let mut ctx = FormatContext::new(file.to_str().unwrap(), &file_content);

        if ctx.is_package() {
            let mut ast =
                SspParser::parse_package(&file_content).map_err(|e| (file.to_str().unwrap(), e))?;
            format_pkg(&mut ctx, ast.next().unwrap())?;
            handled = true;
        }
        if ctx.is_game() {
            let mut ast = SspParser::parse_composition(&file_content)
                .map_err(|e| (file.to_str().unwrap(), e))?;
            format_game(&mut ctx, ast.next().unwrap())?;
            handled = true;
        }

        if handled {
            write!(target, "{}", ctx.to_str())?;

            match target.persist(file) {
                Ok(_) => Ok(()),
                Err(e) => Err(e.error),
            }?;
        }
        Ok(())
    }
}
