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
            Rule::sample => {
                let mut inner = stmt.into_inner();
                let name_ast = inner.next().unwrap();
                let ty = inner.next().unwrap().as_str();
                let ident = name_ast.as_str();

                ctx.push_line(&format!("{ident} <-$ {ty};"));
            }

            Rule::assign => {
                let mut inner = stmt.into_inner();
                let name_ast = inner.next().unwrap();
                let name = name_ast.as_str();
                let expr = format_expr(inner.next().unwrap())?;

                ctx.push_line(&format!("{name} <- {expr};"));
            }

            Rule::table_sample => {
                let mut inner = stmt.into_inner();
                let name_ast = inner.next().unwrap();
                let ident = name_ast.as_str();
                let index = format_expr(inner.next().unwrap())?;
                let ty = inner.next().unwrap().as_str();

                ctx.push_line(&format!("{ident}[{index}] <-$ {ty};"));
            }

            Rule::table_assign => {
                let mut inner = stmt.into_inner();
                let name_ast = inner.next().unwrap();
                let name = name_ast.as_str();
                let index = format_expr(inner.next().unwrap())?;
                let expr = format_expr(inner.next().unwrap())?;

                ctx.push_line(&format!("{name}[{index}] <- {expr};"));
            }

            Rule::invocation => {
                let mut inner = stmt.into_inner();
                let target_ident_name_ast = inner.next().unwrap();
                let ident = target_ident_name_ast.as_str();
                let maybe_index = inner.next().unwrap();
                let (index, oracle_inv) = if maybe_index.as_rule() == Rule::table_index {
                    let mut inner_index = maybe_index.into_inner();
                    (
                        format!("[{}]", format_expr(inner_index.next().unwrap())?),
                        inner.next().unwrap(),
                    )
                } else {
                    ("".to_owned(), maybe_index)
                };
                let mut inner = oracle_inv.into_inner();
                let oracle_name_ast = inner.next().unwrap();
                let oracle_name = oracle_name_ast.as_str();
                let mut multi_instance = String::new();
                let mut argstring = String::new();

                for ast in inner {
                    match ast.as_rule() {
                        Rule::oracle_call_index => {
                            let index_expr_ast = ast.into_inner().next().unwrap();
                            multi_instance = format!("[{}]", format_expr(index_expr_ast)?);
                        }
                        Rule::fn_call_arglist => {
                            let arglist: Vec<_> = ast
                                .into_inner()
                                .map(|expr| format_expr(expr))
                                .collect::<Result<Vec<_>, _>>()?;
                            argstring.push_str(&arglist.join(", "));
                        }
                        _ => unreachable!(),
                    }
                }

                if !index.is_empty() {
                    ctx.push_line(&format!(
                        "{ident}[{index}] <- invoke {oracle_name}{multi_instance}({argstring});"
                    ));
                } else {
                    ctx.push_line(&format!(
                        "{ident} <- invoke {oracle_name}{multi_instance}({argstring});"
                    ));
                }
            }
            Rule::parse => {
                let mut inner = stmt.into_inner();
                let list = inner.next().unwrap();
                let expr = format_expr(inner.next().unwrap())?;
                let idents = list
                    .into_inner()
                    .map(|ident_name| ident_name.as_str().to_string())
                    .collect::<Vec<_>>()
                    .join(", ");

                ctx.push_line(&format!("({idents}) <- parse {expr};"));
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
        match entry.as_rule() {
            Rule::import_oracles_oracle_sig => {
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
                let args = if args.is_none() {
                    Vec::new()
                } else {
                    args.unwrap()
                        .into_inner()
                        .map(|arg| {
                            let mut inner = arg.into_inner();
                            let arg = inner.next().unwrap().as_str();
                            let ty = format_type(inner.next().unwrap())?;
                            Ok::<String, project::error::Error>(format!("{arg}: {ty}"))
                        })
                        .collect::<Result<Vec<String>, _>>()?
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
            Rule::import_oracles_for => {
                let mut parsed: Vec<Pair<Rule>> = entry.into_inner().collect();
                let decl_var_name = parsed[0].as_str();
                let lower_bound = format_expr(parsed.remove(1))?;
                let lower_bound_type = parsed[1].as_str();
                let upper_bound_type = parsed[3].as_str();
                let upper_bound = format_expr(parsed.remove(4))?;
                let loopvar = decl_var_name.to_string();

                ctx.push_line(&format!("for {loopvar}: {lower_bound} {lower_bound_type} {loopvar} {upper_bound_type} {upper_bound} {{"));
                ctx.add_indent();

                format_import_oracles(ctx, parsed.remove(4))?;

                ctx.remove_indent();
                ctx.push_line("}");
            }
            _ => {
                unreachable!("")
            }
        }
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
            if inner.is_some() {
                format_types_block(ctx, inner.unwrap())?;
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
            if inner.is_some() {
                format_decl_list(ctx, inner.unwrap())?;
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
            if inner.is_some() {
                format_decl_list(ctx, inner.unwrap())?;
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
    compose_rule: &Pair<Rule>,
) -> Result<(), project::error::Error> {
    match compose_rule.as_rule() {
        Rule::compose_decl | Rule::compose_decl_multi_inst => {
            let inner = compose_rule.clone().into_inner();
            for compblock in inner {
                let mut compblock = compblock.into_inner();
                let importer = compblock.next().unwrap().as_str();
                let indices = if compblock.peek().unwrap().as_rule() == Rule::indices_ident {
                    let indices = compblock.next().unwrap();
                    &format!(
                        "[{}]",
                        indices
                            .into_inner()
                            .map(|x| { x.as_str() })
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                } else {
                    ""
                };

                let imports = compblock
                    .next()
                    .unwrap()
                    .into_inner()
                    .map(|pair| {
                        let mut pairs = pair.into_inner();
                        let with_indices = if pairs.peek().unwrap().as_rule()
                            == Rule::compose_assign_modifier_with_index
                        {
                            Ok::<String, project::error::Error>(format!(
                                "with index [{}] ",
                                pairs
                                    .next()
                                    .unwrap()
                                    .into_inner()
                                    .next()
                                    .unwrap()
                                    .into_inner()
                                    .map(|x| { format_expr(x) })
                                    .collect::<Result<Vec<_>, _>>()?
                                    .join(", ")
                            ))
                        } else {
                            Ok::<String, project::error::Error>(String::new())
                        }?;
                        let oracle = pairs.next().unwrap().as_str();
                        let package = pairs.next().unwrap().as_str();
                        Ok::<(String, &str, &str), project::error::Error>((
                            with_indices,
                            oracle,
                            package,
                        ))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                ctx.push_line(&format!("{importer}{indices}: {{"));
                ctx.add_indent();
                for (with_indices, oracle, package) in imports {
                    ctx.push_line(&format!("{with_indices}{oracle}: {package},"));
                }
                ctx.remove_indent();
                ctx.push_line("}");
            }
        }
        _ => unreachable!(),
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
        .filter(|x| {
            matches!(
                x.as_rule(),
                Rule::compose_decl | Rule::compose_decl_multi_inst
            )
        })
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
            Rule::game_for => {
                let mut parsed: Vec<Pair<Rule>> = spec.clone().into_inner().collect::<Vec<_>>();
                let decl_var_name = parsed[0].as_str();
                let lower_bound = format_expr(parsed.remove(1))?;
                let lower_bound_type = parsed[1].as_str();
                let upper_bound_type = parsed[3].as_str();
                let upper_bound = format_expr(parsed.remove(4))?;
                let loopvar = decl_var_name.to_string();

                ctx.push_line(&format!("for {loopvar}: {lower_bound} {lower_bound_type} {loopvar} {upper_bound_type} {upper_bound} {{"));
                ctx.add_indent();

                let content = parsed.remove(4);
                format_game_spec(ctx, &content.into_inner().collect())?;

                ctx.remove_indent();

                ctx.push_line("}");
            }
            Rule::instance_decl => {
                ctx.push_line("");
                let mut inner = spec.clone().into_inner();
                let instname = inner.next().unwrap().as_str();
                let next = inner.next().unwrap();
                if next.as_rule() == Rule::indices_expr {
                    let results = next
                        .into_inner()
                        .map(|pair| format_expr(pair))
                        .collect::<Result<Vec<_>, _>>()?;
                    let gamename = inner.next().unwrap().as_str();
                    let indices = results.join(", ");
                    ctx.push_line(&format!("instance {instname}[{indices}] = {gamename} {{"));
                    ctx.add_indent();
                } else {
                    let gamename = next.as_str();
                    ctx.push_line(&format!("instance {instname} = {gamename} {{"));
                    ctx.add_indent();
                }

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
                        if inner.is_some() {
                            for block in inner.unwrap().into_inner() {
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
                        if inner.is_some() {
                            for block in inner.unwrap().into_inner() {
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
            Rule::compose_decl_multi_inst => { /* handled separately */ }
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
