// SPDX-License-Identifier: MIT OR Apache-2.0

use super::ast::*;
use super::render::{render_expr, render_expr_block, render_file, render_record_block, render_type};

fn var(name: &str) -> EcExpr {
    EcExpr::Var(name.to_string())
}

fn int(n: i64) -> EcExpr {
    EcExpr::Int(n)
}

fn binop(op: EcBinop, lhs: EcExpr, rhs: EcExpr) -> EcExpr {
    EcExpr::Binop {
        op,
        lhs: Box::new(lhs),
        rhs: Box::new(rhs),
    }
}

// --- §3.2 acceptance criteria: "Precedence tests" ------------------------
//
// One row per entry in the precedence table (docs/stories/easycrypt/01-…md
// §3.2), each checked for the minimal correct parenthesisation.

#[test]
fn precedence_and_binds_tighter_than_or_left() {
    // a /\ b \/ c  ==  (a /\ b) \/ c, so no parens are needed.
    let e = binop(
        EcBinop::Or,
        binop(EcBinop::And, var("a"), var("b")),
        var("c"),
    );
    assert_eq!(render_expr(&e), "a /\\ b \\/ c");
}

#[test]
fn precedence_or_forced_into_and_needs_parens() {
    let e = binop(
        EcBinop::And,
        binop(EcBinop::Or, var("a"), var("b")),
        var("c"),
    );
    assert_eq!(render_expr(&e), "(a \\/ b) /\\ c");
}

#[test]
fn precedence_not_over_and_needs_parens() {
    let e = EcExpr::Unop {
        op: EcUnop::Not,
        arg: Box::new(binop(EcBinop::And, var("a"), var("b"))),
    };
    assert_eq!(render_expr(&e), "!(a /\\ b)");
}

#[test]
fn precedence_eq_binds_tighter_than_and() {
    let e = binop(
        EcBinop::And,
        binop(EcBinop::Eq, var("a"), var("b")),
        binop(EcBinop::Eq, var("c"), var("d")),
    );
    assert_eq!(render_expr(&e), "a = b /\\ c = d");
}

#[test]
fn precedence_eq_is_not_associative_needs_parens_on_both_sides() {
    // Unlike `<`/`<=`/`>`/`>=` (which chain fine syntactically and only
    // fail to typecheck), EasyCrypt's grammar makes `=`/`<>` genuinely
    // non-associative: `a = b = c` is a parse error, so an `Eq`/`Ne`
    // operand nested under another `Eq`/`Ne` always needs parentheses.
    let e = binop(
        EcBinop::Eq,
        binop(EcBinop::Eq, var("a"), var("b")),
        binop(EcBinop::Eq, var("c"), var("d")),
    );
    assert_eq!(render_expr(&e), "(a = b) = (c = d)");
}

#[test]
fn precedence_add_forced_into_mul_needs_parens() {
    let e = binop(
        EcBinop::Mul,
        binop(EcBinop::Add, var("a"), var("b")),
        var("c"),
    );
    assert_eq!(render_expr(&e), "(a + b) * c");
}

#[test]
fn precedence_implies_is_right_associative() {
    let e = binop(
        EcBinop::Implies,
        var("a"),
        binop(EcBinop::Implies, var("b"), var("c")),
    );
    assert_eq!(render_expr(&e), "a => b => c");
}

// --- Story 43 §3.1: `/\` and `\/` are right-associative --------------------
//
// `ecParser.mly` declares `%right ANDA AND` and `%right ORA OR`, so
// EasyCrypt reads `a /\ b /\ c` as `a /\ (b /\ c)`.

#[test]
fn a_right_nested_conjunction_renders_flat() {
    let e = binop(EcBinop::And, var("a"), binop(EcBinop::And, var("b"), var("c")));
    assert_eq!(render_expr(&e), "a /\\ b /\\ c");
}

#[test]
fn a_left_nested_conjunction_keeps_its_parentheses() {
    let e = binop(EcBinop::And, binop(EcBinop::And, var("a"), var("b")), var("c"));
    assert_eq!(render_expr(&e), "(a /\\ b) /\\ c");
}

#[test]
fn a_right_nested_disjunction_renders_flat() {
    let e = binop(EcBinop::Or, var("a"), binop(EcBinop::Or, var("b"), var("c")));
    assert_eq!(render_expr(&e), "a \\/ b \\/ c");
}

#[test]
fn a_left_nested_disjunction_keeps_its_parentheses() {
    let e = binop(EcBinop::Or, binop(EcBinop::Or, var("a"), var("b")), var("c"));
    assert_eq!(render_expr(&e), "(a \\/ b) \\/ c");
}

#[test]
fn a_left_nested_implication_keeps_its_parentheses() {
    let e = binop(EcBinop::Implies, binop(EcBinop::Implies, var("a"), var("b")), var("c"));
    assert_eq!(render_expr(&e), "(a => b) => c");
}

// --- Story 43 §3.2: operator bodies are laid out one fact per line --------

fn field(expr: &str, name: &str) -> EcExpr {
    EcExpr::Field {
        expr: Box::new(var(expr)),
        field: name.to_string(),
    }
}

fn app(head: &str, args: Vec<EcExpr>) -> EcExpr {
    EcExpr::App {
        head: head.to_string(),
        args,
    }
}

fn op_def(name: &str, args: &[(&str, &str)], body: EcExpr) -> String {
    let file = EcFile {
        header: vec![],
        requires: vec![],
        items: vec![EcItem::OpDef {
            name: name.to_string(),
            args: args
                .iter()
                .map(|(n, ty)| (n.to_string(), EcType::Named(ty.to_string())))
                .collect(),
            ret: Some(EcType::Bool),
            body,
        }],
    };
    render_file(&file)
}

#[test]
fn an_op_body_chain_puts_every_operator_first_on_its_own_line() {
    // The story's own example: `inv` of `H1_1 ~ H2_0`, whose last conjunct
    // is itself a `=>` chain and so becomes a parenthesised block.
    let body = binop(
        EcBinop::And,
        app("params_inv", vec![var("l"), var("r")]),
        binop(
            EcBinop::And,
            binop(EcBinop::Eq, field("l", "l_abort_flag"), field("r", "r_abort_flag")),
            binop(
                EcBinop::Implies,
                EcExpr::Unop {
                    op: EcUnop::Not,
                    arg: Box::new(field("l", "l_abort_flag")),
                },
                app("Domino_invariant", vec![var("l"), var("r")]),
            ),
        ),
    );
    assert_eq!(
        op_def("inv", &[("l", "H1_1_state"), ("r", "H2_0_state")], body),
        concat!(
            "op inv (l : H1_1_state) (r : H2_0_state) : bool =\n",
            "     params_inv l r\n",
            "  /\\ l.`l_abort_flag = r.`r_abort_flag\n",
            "  /\\ (   !l.`l_abort_flag\n",
            "      => Domino_invariant l r).\n",
        )
    );
}

#[test]
fn a_chain_nested_in_a_chain_is_its_own_aligned_block() {
    // `a /\ (b \/ c \/ d) /\ e`, then `(a /\ b) /\ c`: a left-nested chain is
    // a parenthesised operand of the outer one, never flattened into it.
    let disjunction = binop(EcBinop::Or, var("b"), binop(EcBinop::Or, var("c"), var("d")));
    let body = binop(
        EcBinop::And,
        var("a"),
        binop(EcBinop::And, disjunction, var("e")),
    );
    assert_eq!(
        render_expr_block(&body, 2),
        concat!(
            "   a\n",
            "  /\\ (   b\n",
            "      \\/ c\n",
            "      \\/ d)\n",
            "  /\\ e",
        )
    );

    let left_nested = binop(EcBinop::And, binop(EcBinop::And, var("a"), var("b")), var("c"));
    assert_eq!(
        render_expr_block(&left_nested, 0),
        concat!(
            "   (   a\n",
            "    /\\ b)\n",
            "/\\ c",
        )
    );
}

#[test]
fn a_forall_body_goes_on_the_next_line_two_spaces_in() {
    let body = EcExpr::Quant {
        kind: Quantifier::Forall,
        binders: vec![("k".to_string(), EcType::Int)],
        body: Box::new(binop(
            EcBinop::Implies,
            binop(EcBinop::Eq, var("k"), int(0)),
            binop(EcBinop::Eq, var("x"), var("y")),
        )),
    };
    assert_eq!(
        op_def("p", &[], body),
        concat!(
            "op p : bool =\n",
            "  forall (k : int),\n",
            "       k = 0\n",
            "    => x = y.\n",
        )
    );
}

#[test]
fn a_let_body_goes_on_the_next_line_two_spaces_in() {
    let body = EcExpr::Let {
        name: "x".to_string(),
        value: Box::new(binop(EcBinop::Add, var("a"), int(1))),
        body: Box::new(EcExpr::Let {
            name: "y".to_string(),
            value: Box::new(var("x")),
            body: Box::new(binop(
                EcBinop::And,
                binop(EcBinop::Lt, int(0), var("x")),
                binop(EcBinop::Lt, int(0), var("y")),
            )),
        }),
    };
    assert_eq!(
        op_def("p", &[], body),
        concat!(
            "op p : bool =\n",
            "  let x = a + 1 in\n",
            "    let y = x in\n",
            "         0 < x\n",
            "      /\\ 0 < y.\n",
        )
    );
}

fn record(fields: Vec<(&str, EcExpr)>) -> EcExpr {
    EcExpr::RecordLit {
        fields: fields.into_iter().map(|(f, v)| (f.to_string(), v)).collect(),
    }
}

fn mem_read(path: &[&str], mem: u8) -> EcExpr {
    EcExpr::Qualified {
        path: path.iter().map(|p| p.to_string()).collect(),
        mem: Some(mem),
    }
}

#[test]
fn a_record_literal_puts_one_field_per_line_and_a_nested_one_under_its_field() {
    // Story 42 nests a package-state literal in a field of the game-state
    // literal; its fields line up under its own first field.
    let lit = record(vec![
        (
            "l_pkg_KX",
            record(vec![
                ("KX_d_LTK", mem_read(&["Comp_H1", "Pkg_Inst_KX", "d_LTK"], 1)),
                ("KX_d_State", mem_read(&["Comp_H1", "Pkg_Inst_KX", "d_State"], 1)),
            ]),
        ),
        ("l_pkg_KX_b", mem_read(&["Comp_H1", "Pkg_Inst_KX", "b"], 1)),
        ("l_abort_flag", mem_read(&["Comp_H1", "Game_H1", "abort_flag"], 1)),
    ]);
    assert_eq!(
        render_record_block(&lit, 10),
        concat!(
            "{| l_pkg_KX = {| KX_d_LTK = Comp_H1.Pkg_Inst_KX.d_LTK{1};\n",
            "                           KX_d_State = Comp_H1.Pkg_Inst_KX.d_State{1} |};\n",
            "             l_pkg_KX_b = Comp_H1.Pkg_Inst_KX.b{1};\n",
            "             l_abort_flag = Comp_H1.Game_H1.abort_flag{1} |}",
        )
    );
    // A one-field literal is already one fact.
    assert_eq!(
        render_record_block(&record(vec![("a", int(1))]), 4),
        "{| a = 1 |}"
    );
}

#[test]
fn a_record_literal_in_an_op_body_stays_on_one_line() {
    // §3.2: only chains, quantifiers and `let`s are laid out in an `op`; the
    // record block is for the invariant `call` (§3.3).
    let lit = record(vec![("a", var("x")), ("b", var("y"))]);
    assert_eq!(render_expr_block(&lit, 2), "{| a = x; b = y |}");
}

#[test]
fn a_long_atom_stays_on_one_line() {
    let long = (0..40).map(|i| format!("arg{i}")).collect::<Vec<_>>();
    let application = app("f", long.iter().map(|a| var(a)).collect());
    let equality = binop(EcBinop::Eq, application.clone(), var("y"));
    assert_eq!(
        op_def("p", &[], equality.clone()),
        format!("op p : bool =\n  {}.\n", render_expr(&equality))
    );
    assert!(render_expr_block(&application, 2).len() > 200);
    assert!(!render_expr_block(&application, 2).contains('\n'));
}

// --- Negative-literal edge case -------------------------------------------
//
// `f -1` lexes as `f - 1` in EasyCrypt (verified by compiling), so a
// negative literal used as an application argument needs parens.

#[test]
fn negative_literal_as_app_argument_gets_parens() {
    let e = EcExpr::App {
        head: "idfun".to_string(),
        args: vec![int(-1)],
    };
    assert_eq!(render_expr(&e), "idfun (-1)");
}

#[test]
fn negative_literal_as_binop_operand_needs_no_parens() {
    let e = binop(EcBinop::Add, var("a"), int(-1));
    assert_eq!(render_expr(&e), "a + -1");
}

// --- `Some` with a non-atomic argument -------------------------------------

#[test]
fn some_of_application_gets_parens() {
    let e = EcExpr::Some_(Box::new(EcExpr::App {
        head: "f".to_string(),
        args: vec![var("x")],
    }));
    assert_eq!(render_expr(&e), "Some (f x)");
}

// --- EcType spellings -------------------------------------------------------

#[test]
fn type_spellings() {
    assert_eq!(render_type(&EcType::Int), "int");
    assert_eq!(render_type(&EcType::Bool), "bool");
    assert_eq!(render_type(&EcType::Unit), "unit");
    assert_eq!(render_type(&EcType::Named("bits_n".into())), "bits_n");
    assert_eq!(
        render_type(&EcType::Option(Box::new(EcType::Named("bits_n".into())))),
        "bits_n option"
    );
    assert_eq!(
        render_type(&EcType::Fmap(
            Box::new(EcType::Named("k".into())),
            Box::new(EcType::Named("v".into()))
        )),
        "(k, v) fmap"
    );
    assert_eq!(
        render_type(&EcType::Distr(Box::new(EcType::Named("bits_n".into())))),
        "bits_n distr"
    );
    assert_eq!(
        render_type(&EcType::Fun(Box::new(EcType::Int), Box::new(EcType::Bool))),
        "int -> bool"
    );
    assert_eq!(
        render_type(&EcType::Tuple(vec![EcType::Int, EcType::Bool])),
        "(int * bool)"
    );
}

#[test]
fn type_parenthesises_fun_inside_compound_type() {
    let fun_ty = EcType::Fun(Box::new(EcType::Int), Box::new(EcType::Int));
    assert_eq!(
        render_type(&EcType::Fun(Box::new(fun_ty), Box::new(EcType::Int))),
        "(int -> int) -> int"
    );
}

// --- Determinism ------------------------------------------------------------

#[test]
fn rendering_is_deterministic() {
    let file = kitchen_sink();
    assert_eq!(render_file(&file), render_file(&file));
}

// --- §4 acceptance criteria: kitchen-sink golden file -----------------------

fn kitchen_sink() -> EcFile {
    EcFile {
        header: vec!["generated by domino easycrypt exporter — story 01 kitchen sink".to_string()],
        requires: vec![Require {
            import: true,
            names: vec![
                "AllCore".to_string(),
                "Bool".to_string(),
                "Distr".to_string(),
                "FMap".to_string(),
                "IntDiv".to_string(),
                "Base".to_string(),
            ],
        }],
        items: vec![
            EcItem::Comment(
                "exercises every EcItem, EcStmt, EcExpr and EcType variant".to_string(),
            ),
            EcItem::TypeAbstract {
                name: "bits_n".to_string(),
            },
            EcItem::TypeAlias {
                name: "pair_t".to_string(),
                ty: EcType::Tuple(vec![EcType::Int, EcType::Bool]),
            },
            EcItem::Record {
                name: "rec_t".to_string(),
                fields: vec![
                    ("fld_a".to_string(), EcType::Int),
                    ("fld_b".to_string(), EcType::Bool),
                ],
            },
            EcItem::OpDecl {
                name: "zero_n".to_string(),
                ty: EcType::Named("bits_n".to_string()),
            },
            EcItem::OpDecl {
                name: "dbits".to_string(),
                ty: EcType::Distr(Box::new(EcType::Named("bits_n".to_string()))),
            },
            EcItem::OpDecl {
                name: "kitchen_fun_ty".to_string(),
                ty: EcType::Fun(
                    Box::new(EcType::Fun(Box::new(EcType::Int), Box::new(EcType::Int))),
                    Box::new(EcType::Int),
                ),
            },
            EcItem::OpDef {
                name: "idfun_helper".to_string(),
                args: vec![("x".to_string(), EcType::Int)],
                ret: Some(EcType::Int),
                body: var("x"),
            },
            EcItem::OpDef {
                name: "mk_rec".to_string(),
                args: vec![("a".to_string(), EcType::Int), ("b".to_string(), EcType::Bool)],
                ret: Some(EcType::Named("rec_t".to_string())),
                body: EcExpr::RecordLit {
                    fields: vec![
                        ("fld_a".to_string(), var("a")),
                        ("fld_b".to_string(), var("b")),
                    ],
                },
            },
            EcItem::OpDef {
                name: "kitchen_tuple_and_proj".to_string(),
                args: vec![("s".to_string(), EcType::Tuple(vec![EcType::Int, EcType::Int]))],
                ret: Some(EcType::Int),
                body: binop(
                    EcBinop::Add,
                    EcExpr::Proj {
                        expr: Box::new(var("s")),
                        index: 1,
                    },
                    EcExpr::Proj {
                        expr: Box::new(var("s")),
                        index: 2,
                    },
                ),
            },
            EcItem::OpDef {
                name: "kitchen_field".to_string(),
                args: vec![("r".to_string(), EcType::Named("rec_t".to_string()))],
                ret: Some(EcType::Int),
                body: EcExpr::Field {
                    expr: Box::new(var("r")),
                    field: "fld_a".to_string(),
                },
            },
            EcItem::OpDef {
                name: "kitchen_option".to_string(),
                args: vec![("x".to_string(), EcType::Option(Box::new(EcType::Int)))],
                ret: Some(EcType::Int),
                body: EcExpr::Oget(Box::new(var("x"))),
            },
            EcItem::OpDef {
                name: "kitchen_some".to_string(),
                args: vec![],
                ret: Some(EcType::Option(Box::new(EcType::Int))),
                body: EcExpr::Some_(Box::new(int(3))),
            },
            EcItem::OpDef {
                name: "kitchen_none".to_string(),
                args: vec![],
                ret: Some(EcType::Option(Box::new(EcType::Int))),
                body: EcExpr::None_(EcType::Int),
            },
            EcItem::OpDef {
                name: "kitchen_map_get".to_string(),
                args: vec![
                    (
                        "m".to_string(),
                        EcType::Fmap(Box::new(EcType::Int), Box::new(EcType::Bool)),
                    ),
                    ("k".to_string(), EcType::Int),
                ],
                ret: Some(EcType::Option(Box::new(EcType::Bool))),
                body: EcExpr::MapGet {
                    map: Box::new(var("m")),
                    key: Box::new(var("k")),
                },
            },
            EcItem::OpDef {
                name: "kitchen_map_set".to_string(),
                args: vec![
                    (
                        "m".to_string(),
                        EcType::Fmap(Box::new(EcType::Int), Box::new(EcType::Bool)),
                    ),
                    ("k".to_string(), EcType::Int),
                    ("v".to_string(), EcType::Bool),
                ],
                ret: Some(EcType::Fmap(Box::new(EcType::Int), Box::new(EcType::Bool))),
                body: EcExpr::MapSet {
                    map: Box::new(var("m")),
                    key: Box::new(var("k")),
                    value: Box::new(var("v")),
                },
            },
            EcItem::OpDef {
                name: "kitchen_map_rem".to_string(),
                args: vec![
                    (
                        "m".to_string(),
                        EcType::Fmap(Box::new(EcType::Int), Box::new(EcType::Bool)),
                    ),
                    ("k".to_string(), EcType::Int),
                ],
                ret: Some(EcType::Fmap(Box::new(EcType::Int), Box::new(EcType::Bool))),
                body: EcExpr::MapRem {
                    map: Box::new(var("m")),
                    key: Box::new(var("k")),
                },
            },
            EcItem::OpDef {
                name: "kitchen_map_empty".to_string(),
                args: vec![],
                ret: Some(EcType::Fmap(Box::new(EcType::Int), Box::new(EcType::Bool))),
                body: EcExpr::MapEmpty,
            },
            EcItem::OpDef {
                name: "kitchen_app".to_string(),
                args: vec![("x".to_string(), EcType::Int)],
                ret: Some(EcType::Int),
                body: EcExpr::App {
                    head: "idfun_helper".to_string(),
                    args: vec![var("x")],
                },
            },
            EcItem::OpDef {
                name: "kitchen_neg_lit".to_string(),
                args: vec![],
                ret: Some(EcType::Int),
                body: EcExpr::App {
                    head: "idfun_helper".to_string(),
                    args: vec![int(-1)],
                },
            },
            EcItem::OpDef {
                name: "kitchen_unop".to_string(),
                args: vec![("b".to_string(), EcType::Bool)],
                ret: Some(EcType::Bool),
                body: EcExpr::Unop {
                    op: EcUnop::Not,
                    arg: Box::new(var("b")),
                },
            },
            EcItem::OpDef {
                name: "kitchen_neg".to_string(),
                args: vec![("x".to_string(), EcType::Int)],
                ret: Some(EcType::Int),
                body: EcExpr::Unop {
                    op: EcUnop::Neg,
                    arg: Box::new(var("x")),
                },
            },
            EcItem::OpDef {
                name: "kitchen_bool_lit".to_string(),
                args: vec![],
                ret: Some(EcType::Bool),
                body: EcExpr::Bool(true),
            },
            EcItem::OpDef {
                name: "kitchen_unit".to_string(),
                args: vec![],
                ret: Some(EcType::Unit),
                body: EcExpr::Unit,
            },
            // EasyCrypt's standard library only gives `real` a `>`/`>=`
            // (`theories/datatypes/Real.ec`); `int` has none, so a bare
            // `a > b` on ints resolves to `Real.>` and fails to typecheck.
            // Define local int overloads so `kitchen_cmp` below can exercise
            // `EcBinop::Gt`/`Ge`.
            EcItem::OpDef {
                name: "(>)".to_string(),
                args: vec![("x".to_string(), EcType::Int), ("y".to_string(), EcType::Int)],
                ret: Some(EcType::Bool),
                body: binop(EcBinop::Lt, var("y"), var("x")),
            },
            EcItem::OpDef {
                name: "(>=)".to_string(),
                args: vec![("x".to_string(), EcType::Int), ("y".to_string(), EcType::Int)],
                ret: Some(EcType::Bool),
                body: binop(EcBinop::Le, var("y"), var("x")),
            },
            EcItem::OpDef {
                name: "kitchen_cmp".to_string(),
                args: vec![("a".to_string(), EcType::Int), ("b".to_string(), EcType::Int)],
                ret: Some(EcType::Bool),
                body: binop(
                    EcBinop::Implies,
                    binop(
                        EcBinop::Or,
                        binop(
                            EcBinop::And,
                            binop(EcBinop::Eq, var("a"), var("b")),
                            binop(EcBinop::Ne, var("a"), var("b")),
                        ),
                        binop(
                            EcBinop::Xor,
                            binop(EcBinop::Lt, var("a"), var("b")),
                            binop(EcBinop::Le, var("a"), var("b")),
                        ),
                    ),
                    binop(
                        EcBinop::Or,
                        binop(EcBinop::Gt, var("a"), var("b")),
                        binop(EcBinop::Ge, var("a"), var("b")),
                    ),
                ),
            },
            EcItem::OpDef {
                name: "kitchen_arith".to_string(),
                args: vec![("a".to_string(), EcType::Int), ("b".to_string(), EcType::Int)],
                ret: Some(EcType::Int),
                body: binop(
                    EcBinop::Sub,
                    binop(EcBinop::Add, var("a"), var("b")),
                    binop(
                        EcBinop::Mod,
                        binop(
                            EcBinop::Mul,
                            var("a"),
                            binop(EcBinop::Div, var("b"), binop(EcBinop::Add, var("b"), int(1))),
                        ),
                        int(2),
                    ),
                ),
            },
            EcItem::OpDef {
                name: "kitchen_if".to_string(),
                args: vec![
                    ("b".to_string(), EcType::Bool),
                    ("x".to_string(), EcType::Int),
                    ("y".to_string(), EcType::Int),
                ],
                ret: Some(EcType::Int),
                body: EcExpr::If {
                    cond: Box::new(var("b")),
                    then_expr: Box::new(var("x")),
                    else_expr: Box::new(var("y")),
                },
            },
            EcItem::OpDef {
                name: "kitchen_let".to_string(),
                args: vec![("x".to_string(), EcType::Int)],
                ret: Some(EcType::Int),
                body: EcExpr::Let {
                    name: "y".to_string(),
                    value: Box::new(binop(EcBinop::Add, var("x"), int(1))),
                    body: Box::new(binop(EcBinop::Mul, var("y"), var("y"))),
                },
            },
            EcItem::OpDef {
                name: "kitchen_quant".to_string(),
                args: vec![],
                ret: Some(EcType::Bool),
                body: EcExpr::Quant {
                    kind: Quantifier::Forall,
                    binders: vec![("x".to_string(), EcType::Int)],
                    body: Box::new(EcExpr::Quant {
                        kind: Quantifier::Exists,
                        binders: vec![("y".to_string(), EcType::Int)],
                        body: Box::new(binop(
                            EcBinop::Or,
                            binop(EcBinop::Eq, var("x"), var("y")),
                            binop(EcBinop::Ne, var("x"), var("y")),
                        )),
                    }),
                },
            },
            EcItem::OpDef {
                name: "kitchen_qualified".to_string(),
                args: vec![],
                ret: Some(EcType::Int),
                body: EcExpr::Qualified {
                    path: vec!["Base".to_string(), "dummy".to_string()],
                    mem: None,
                },
            },
            EcItem::Axiom {
                name: "top_axiom".to_string(),
                formula: binop(
                    EcBinop::Eq,
                    EcExpr::Qualified {
                        path: vec!["zero_n".to_string()],
                        mem: None,
                    },
                    EcExpr::Qualified {
                        path: vec!["zero_n".to_string()],
                        mem: None,
                    },
                ),
            },
            EcItem::ModuleType {
                name: "Proto".to_string(),
                params: vec![],
                includes: vec![],
                procs: vec![ProcSig {
                    name: "init".to_string(),
                    args: vec![("seed".to_string(), EcType::Int)],
                    ret: EcType::Unit,
                }],
            },
            EcItem::ModuleType {
                name: "Adv".to_string(),
                params: vec![("O".to_string(), "Proto".to_string())],
                includes: vec![],
                procs: vec![ProcSig {
                    name: "run".to_string(),
                    args: vec![],
                    ret: EcType::Bool,
                }],
            },
            EcItem::Clone {
                base: "Base".to_string(),
                as_name: "BaseInst".to_string(),
                overrides: vec![
                    CloneOverride::Type {
                        lhs: "t".to_string(),
                        rhs: EcType::Int,
                    },
                    CloneOverride::Op {
                        lhs: "dummy".to_string(),
                        rhs: int(3),
                    },
                ],
            },
            EcItem::Module(EcModule {
                name: "Impl".to_string(),
                params: vec![],
                implements: Some("Proto".to_string()),
                vars: vec![("st".to_string(), EcType::Int)],
                procs: vec![EcProc {
                    name: "init".to_string(),
                    args: vec![("seed".to_string(), EcType::Int)],
                    ret: EcType::Unit,
                    locals: vec![],
                    body: EcBlock(vec![
                        EcStmt::Comment("record the seed as our state".to_string()),
                        EcStmt::Assign {
                            lhs: EcLvalue::Var("st".to_string()),
                            rhs: var("seed"),
                        },
                    ]),
                    ret_expr: Some(EcExpr::Unit),
                }],
            }),
            EcItem::Module(EcModule {
                name: "Fctr".to_string(),
                params: vec![("P".to_string(), "Proto".to_string())],
                implements: None,
                vars: vec![],
                procs: vec![EcProc {
                    name: "run".to_string(),
                    args: vec![],
                    ret: EcType::Unit,
                    locals: vec![],
                    body: EcBlock(vec![EcStmt::Call {
                        lhs: None,
                        module: "P".to_string(),
                        proc: "init".to_string(),
                        args: vec![int(0)],
                    }]),
                    ret_expr: Some(EcExpr::Unit),
                }],
            }),
            EcItem::ModuleAlias {
                name: "Inst".to_string(),
                functor: "Fctr".to_string(),
                args: vec!["Impl".to_string()],
            },
            EcItem::Module(EcModule {
                name: "Stateful".to_string(),
                params: vec![],
                implements: None,
                vars: vec![
                    (
                        "tbl".to_string(),
                        EcType::Fmap(Box::new(EcType::Int), Box::new(EcType::Bool)),
                    ),
                    ("ctr".to_string(), EcType::Int),
                ],
                procs: vec![
                    EcProc {
                        name: "reset".to_string(),
                        args: vec![],
                        ret: EcType::Unit,
                        locals: vec![],
                        body: EcBlock(vec![
                            EcStmt::Comment("reset the table and counter".to_string()),
                            EcStmt::Assign {
                                lhs: EcLvalue::Var("tbl".to_string()),
                                rhs: EcExpr::MapEmpty,
                            },
                            EcStmt::Assign {
                                lhs: EcLvalue::Var("ctr".to_string()),
                                rhs: int(0),
                            },
                        ]),
                        ret_expr: Some(EcExpr::Unit),
                    },
                    EcProc {
                        name: "flip".to_string(),
                        args: vec![("k".to_string(), EcType::Int)],
                        ret: EcType::Bool,
                        locals: vec![
                            (
                                "cur".to_string(),
                                EcType::Option(Box::new(EcType::Bool)),
                                None,
                            ),
                            ("result".to_string(), EcType::Bool, None),
                        ],
                        body: EcBlock(vec![
                            EcStmt::Assign {
                                lhs: EcLvalue::Var("cur".to_string()),
                                rhs: EcExpr::MapGet {
                                    map: Box::new(var("tbl")),
                                    key: Box::new(var("k")),
                                },
                            },
                            EcStmt::If {
                                cond: binop(EcBinop::Eq, var("cur"), EcExpr::None_(EcType::Bool)),
                                then_block: EcBlock(vec![EcStmt::Assign {
                                    lhs: EcLvalue::Var("result".to_string()),
                                    rhs: EcExpr::Bool(true),
                                }]),
                                else_block: Some(EcBlock(vec![EcStmt::Assign {
                                    lhs: EcLvalue::Var("result".to_string()),
                                    rhs: EcExpr::Unop {
                                        op: EcUnop::Not,
                                        arg: Box::new(EcExpr::Oget(Box::new(var("cur")))),
                                    },
                                }])),
                            },
                            EcStmt::Assign {
                                lhs: EcLvalue::MapSet {
                                    map: "tbl".to_string(),
                                    key: var("k"),
                                },
                                rhs: var("result"),
                            },
                            EcStmt::Assign {
                                lhs: EcLvalue::Var("ctr".to_string()),
                                rhs: binop(EcBinop::Add, var("ctr"), int(1)),
                            },
                        ]),
                        ret_expr: Some(var("result")),
                    },
                    EcProc {
                        name: "sample_bit".to_string(),
                        args: vec![],
                        ret: EcType::Named("bits_n".to_string()),
                        locals: vec![(
                            "x".to_string(),
                            EcType::Named("bits_n".to_string()),
                            None,
                        )],
                        body: EcBlock(vec![EcStmt::Sample {
                            lhs: EcLvalue::Var("x".to_string()),
                            distr: var("dbits"),
                        }]),
                        ret_expr: Some(var("x")),
                    },
                    EcProc {
                        name: "pair".to_string(),
                        args: vec![],
                        ret: EcType::Tuple(vec![EcType::Int, EcType::Int]),
                        locals: vec![
                            (
                                "p".to_string(),
                                EcType::Tuple(vec![EcType::Int, EcType::Int]),
                                None,
                            ),
                            ("a".to_string(), EcType::Int, Some(int(0))),
                            ("b".to_string(), EcType::Int, Some(int(0))),
                        ],
                        body: EcBlock(vec![
                            EcStmt::Assign {
                                lhs: EcLvalue::Tuple(vec!["a".to_string(), "b".to_string()]),
                                rhs: EcExpr::Tuple(vec![var("ctr"), var("ctr")]),
                            },
                            EcStmt::Assign {
                                lhs: EcLvalue::Var("p".to_string()),
                                rhs: EcExpr::Tuple(vec![var("a"), var("b")]),
                            },
                        ]),
                        ret_expr: Some(var("p")),
                    },
                ],
            }),
            EcItem::Module(EcModule {
                name: "Caller".to_string(),
                params: vec![],
                implements: None,
                vars: vec![],
                procs: vec![EcProc {
                    name: "call_flip".to_string(),
                    args: vec![("k".to_string(), EcType::Int)],
                    ret: EcType::Bool,
                    locals: vec![("r".to_string(), EcType::Bool, None)],
                    body: EcBlock(vec![EcStmt::Call {
                        lhs: Some(EcLvalue::Var("r".to_string())),
                        module: "Stateful".to_string(),
                        proc: "flip".to_string(),
                        args: vec![var("k")],
                    }]),
                    ret_expr: Some(var("r")),
                }],
            }),
            EcItem::Section(EcSection {
                declares: vec![DeclareModule {
                    name: "A".to_string(),
                    module_type: "Proto".to_string(),
                    restrictions: vec!["Impl".to_string()],
                }],
                items: vec![EcItem::Axiom {
                    name: "section_axiom".to_string(),
                    formula: binop(EcBinop::Eq, int(1), int(1)),
                }],
                lemmas: vec![
                    EcLemma {
                        name: "typed_lemma".to_string(),
                        binders: vec![LemmaBinder::Typed {
                            name: "b".to_string(),
                            ty: EcType::Bool,
                        }],
                        statement: binop(
                            EcBinop::Or,
                            var("b"),
                            EcExpr::Unop {
                                op: EcUnop::Not,
                                arg: Box::new(var("b")),
                            },
                        ),
                        proof: vec![
                            ProofLine::Tactic {
                                indent: 0,
                                bullet: None,
                                text: "case: b.".to_string(),
                            },
                            ProofLine::Tactic {
                                indent: 0,
                                bullet: Some('+'),
                                text: "trivial.".to_string(),
                            },
                            ProofLine::Tactic {
                                indent: 0,
                                bullet: Some('+'),
                                text: "trivial.".to_string(),
                            },
                        ],
                    },
                    EcLemma {
                        name: "mem_tag_lemma".to_string(),
                        binders: vec![LemmaBinder::Memory("1".to_string())],
                        statement: binop(
                            EcBinop::Eq,
                            EcExpr::Qualified {
                                path: vec!["Impl".to_string(), "st".to_string()],
                                mem: Some(1),
                            },
                            EcExpr::Qualified {
                                path: vec!["Impl".to_string(), "st".to_string()],
                                mem: Some(1),
                            },
                        ),
                        proof: vec![ProofLine::Tactic {
                            indent: 0,
                            bullet: None,
                            text: "trivial.".to_string(),
                        }],
                    },
                ],
            }),
        ],
    }
}

#[test]
fn kitchen_sink_matches_golden_file() {
    // Fixture regenerated by rendering `kitchen_sink()` and saving the
    // output to testdata/easycrypt/story01/kitchen-sink.ec.
    let expected = include_str!("../../../testdata/easycrypt/story01/kitchen-sink.ec");
    assert_eq!(render_file(&kitchen_sink()), expected);
}

#[test]
fn kitchen_sink_compiles_under_easycrypt() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/testdata/easycrypt/story01");
    let file = format!("{dir}/kitchen-sink.ec");
    super::test_support::assert_compiles(dir, &file);
}
