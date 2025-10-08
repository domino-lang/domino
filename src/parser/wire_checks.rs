use std::convert::TryInto as _;

use itertools::Itertools;
use pest::iterators::Pair;

use crate::{
    identifier::pkg_ident::PackageImportsLoopVarIdentifier,
    types::Type,
    writers::smt::{
        exprs::{SmtEq2, SmtExpr, SmtIte, SmtLt, SmtLte},
        patterns::FunctionPattern,
        sorts::Sort,
    },
};

use super::{
    error::ForLoopIdentifersDontMatchError,
    package::{handle_expression, ForComp, ParsePackageContext, ParsePackageError},
    Rule,
};

#[derive(Clone)]
struct MultiplicityFunctionPattern {
    name: String,
    args: Vec<String>,
}

impl FunctionPattern for MultiplicityFunctionPattern {
    fn function_name(&self) -> String {
        format!("multiset-multiplicity-{name}", name = self.name)
    }

    fn function_args(&self) -> Vec<(String, Sort)> {
        self.args
            .iter()
            .map(|name| ((*name).to_string(), Sort::Int))
            .chain(Some(("queryElem".to_string(), Sort::Int)))
            .collect()
    }

    fn function_return_sort(&self) -> Sort {
        Sort::Int
    }

    fn function_args_count(&self) -> usize {
        // args + query element
        self.args.len() + 1
    }
}

impl MultiplicityFunctionPattern {
    pub fn package_imports(pkg_name: &str, imports_ast: Pair<Rule>) -> (Self, impl Into<SmtExpr>) {
        assert_eq!(imports_ast.as_rule(), Rule::import_oracles_body);

        (
            Self {
                name: format!("-package-imports-{pkg_name}"),
                args: vec![],
            },
            ("+", "1", "2"),
        )
    }
}

#[derive(Clone)]
struct FunctionDefinition {
    pattern: MultiplicityFunctionPattern,
    body: SmtExpr,
}

fn parse_import_oracles(
    ctx: &ParsePackageContext,
    ast: Pair<Rule>,
) -> Result<(FunctionDefinition, Vec<FunctionDefinition>), ParsePackageError> {
    assert_eq!(ast.as_rule(), Rule::import_oracles);
    let pkg_name = ctx.pkg_name;

    let pattern = MultiplicityFunctionPattern {
        name: format!("-package-imports-{pkg_name}"),
        args: vec![],
    };

    let (query_arg_name, _) = &pattern.function_args()[0];

    let defs = parse_import_oracles_body(ctx, ast, 0, &[])?;

    let deps = defs
        .iter()
        .flat_map(|(_, _, deps)| deps)
        .cloned()
        .collect_vec();

    let body = SmtExpr::List(
        ["+".into()]
            .iter()
            .cloned()
            .chain(defs.iter().map(|(_, call, _)| call.clone()))
            .collect_vec(),
    );

    let fndef = FunctionDefinition { pattern, body };

    Ok((fndef, deps))
}

fn parse_import_oracles_body(
    ctx: &ParsePackageContext,
    ast: Pair<Rule>,
    i: usize,
    stack: &[PackageImportsLoopVarIdentifier],
) -> Result<Vec<(FunctionDefinition, SmtExpr, Vec<FunctionDefinition>)>, ParsePackageError> {
    assert_eq!(ast.as_rule(), Rule::import_oracles_body);

    ast.into_inner()
        .enumerate()
        .map(|(i, ast)| match ast.as_rule() {
            Rule::import_oracles_for => parse_import_oracles_for(ctx, i, ast, stack),
            Rule::import_oracles_oracle_sig => parse_import_oracles_oracle_sig(ctx, i, ast, stack),
            _ => unreachable!(),
        })
        .collect::<Result<Vec<_>, _>>()
}

fn parse_import_oracles_oracle_sig(
    ctx: &ParsePackageContext,
    i: usize,
    ast: Pair<Rule>,
    stack: &[PackageImportsLoopVarIdentifier],
) -> Result<(FunctionDefinition, SmtExpr, Vec<FunctionDefinition>), ParsePackageError> {
    assert_eq!(ast.as_rule(), Rule::import_oracles_oracle_sig);
    let pkg_name = ctx.pkg_name;

    let mut inner_iter = ast.into_inner();
    let oracle_name = inner_iter.next().unwrap().as_str();

    let index_ast = inner_iter.next().unwrap();
    let has_index = index_ast.as_rule() == Rule::indices_expr;
    if !stack.is_empty() && !has_index {
        panic!("if we import the same oracle over and over again, it is imported more than once")
    }
    let index = index_ast.as_str();

    let name_suffix = stack
        .iter()
        .map(|id| format!("{oracle_name}_{i}_{}", id.name))
        .join("-");

    let args = stack.iter().map(|id| id.name.clone()).collect_vec();

    let pattern = MultiplicityFunctionPattern {
        name: format!("-package-imports-{pkg_name}-{name_suffix}"),
        args: args.clone(),
    };

    let call_args = stack.iter().map(|id| id.name.clone().into()).collect_vec();

    let call = pattern.call(&call_args).unwrap();

    let body = SmtIte {
        cond: SmtEq2 {
            lhs: index,
            rhs: "queryElem",
        },
        then: 1,
        els: 0,
    }
    .into();

    let fndef = FunctionDefinition { pattern, body };
    let deps = vec![];

    Ok((fndef, call, deps))
}

fn parse_import_oracles_for(
    ctx: &ParsePackageContext,
    i: usize,
    ast: Pair<Rule>,
    stack: &[PackageImportsLoopVarIdentifier],
) -> Result<(FunctionDefinition, SmtExpr, Vec<FunctionDefinition>), ParsePackageError> {
    assert_eq!(ast.as_rule(), Rule::import_oracles_for);
    let pkg_name = ctx.pkg_name;
    let mut for_ast = ast.into_inner();

    let ident_ast = for_ast.next().unwrap();
    let for_start_ast = for_ast.next().unwrap();
    let start_comp_ast = for_ast.next().unwrap();
    let ident2_ast = for_ast.next().unwrap();
    let end_comp_ast = for_ast.next().unwrap();
    let for_end_ast = for_ast.next().unwrap();

    let ident = ident_ast.as_str().to_string();
    let ident2 = ident2_ast.as_str().to_string();

    let ident_span = ident_ast.as_span();
    let ident2_span = ident2_ast.as_span();
    let for_start = handle_expression(&ctx.parse_ctx(), for_start_ast, Some(&Type::Integer))?;
    let for_end = handle_expression(&ctx.parse_ctx(), for_end_ast, Some(&Type::Integer))?;

    // the grammar ensures that try_into doesn't fail
    let start_comp: ForComp = start_comp_ast.as_str().try_into().unwrap();
    let end_comp: ForComp = end_comp_ast.as_str().try_into().unwrap();

    let body_ast = for_ast.next().unwrap();

    if ident != ident2 {
        return Err(ForLoopIdentifersDontMatchError {
            source_code: ctx.named_source(),
            at_fst: (ident_span.start()..ident_span.end()).into(),
            at_snd: (ident2_span.start()..ident2_span.end()).into(),
            fst: ident,
            snd: ident2,
        }
        .into());
    }

    let ident_data = PackageImportsLoopVarIdentifier {
        pkg_name: pkg_name.to_string(),
        name: ident.clone(),
        start: Box::new(for_start.clone()),
        end: Box::new(for_end.clone()),
        start_comp,
        end_comp,
        pkg_inst_name: None,
        game_name: None,
        game_inst_name: None,
        theorem_name: None,
    };

    let stack: Vec<_> = stack.iter().chain([&ident_data]).cloned().collect();

    let defs = parse_import_oracles_body(ctx, body_ast, i, &stack)?;

    let name_suffix = stack
        .iter()
        .map(|id| format!("For{i}_{}", id.name))
        .join("-");
    let args = stack.iter().map(|id| id.name.clone()).collect_vec();

    let pattern = MultiplicityFunctionPattern {
        name: format!("-package-imports-{pkg_name}-{name_suffix}"),
        args: args.clone(),
    };

    // the + symbol
    let plus_iter = vec!["+".to_string()].into_iter().map(SmtExpr::Atom);

    // the inner calls
    let inner_iter = defs.iter().map(|(_, call, _)| call.clone());

    // the recursive call to the next iteration
    let next_iter = vec![pattern
        .call(
            &stack
                .iter()
                .map(|id| -> SmtExpr {
                    if id.name != ident_data.name {
                        id.name.clone().into()
                    } else {
                        ("+", 1, id.name.clone()).into()
                    }
                })
                .collect_vec(),
        )
        .unwrap()]
    .into_iter();

    let body = SmtIte {
        // if we are in range
        cond: {
            let type_inference_hack: SmtExpr = match ident_data.end_comp {
                ForComp::Lt => SmtLt(&ident_data.name, ident_data.end.as_ref().clone()).into(),
                ForComp::Lte => SmtLte(&ident_data.name, ident_data.end.as_ref().clone()).into(),
            };
            type_inference_hack
        },
        // then we return an actual value
        then: SmtExpr::List(plus_iter.chain(inner_iter).chain(next_iter).collect_vec()),
        // otherwise we return zero
        els: SmtExpr::Atom("0".to_string()),
    }
    .into();

    let deps = defs.into_iter().flat_map(|(_, _, deps)| deps).collect_vec();

    let fndef = FunctionDefinition { pattern, body };

    let start_call_args = stack
        .iter()
        .map(|id| {
            if id.name == ident_data.name {
                match ident_data.start_comp {
                    ForComp::Lt => fndef
                        .pattern
                        .call(&[("+", 1, ident_data.start.as_ref().clone()).into()])
                        .unwrap(),
                    ForComp::Lte => fndef
                        .pattern
                        .call(&[ident_data.start.as_ref().clone().into()])
                        .unwrap(),
                }
            } else {
                id.name.clone().into()
            }
        })
        .collect_vec();

    let start_call = fndef.pattern.call(&start_call_args).unwrap();

    Ok((fndef, start_call, deps))
}
