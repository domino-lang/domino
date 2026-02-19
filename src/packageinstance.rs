// SPDX-License-Identifier: MIT OR Apache-2.0

use itertools::Itertools as _;

use crate::{
    expressions::{Expression, ExpressionKind},
    identifier::{
        pkg_ident::{PackageConstIdentifier, PackageIdentifier},
        Identifier,
    },
    package::{OracleDef, OracleSig, Package},
    types::{CountSpec, Type, TypeKind},
};

use self::instantiate::InstantiationContext;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct PackageInstance {
    pub name: String,

    // we need these two to compare whether two instances of a same package have the same
    // parameters (both constants and types).
    // We need to compare that when checking the mapping of game and an assumption:
    // A mapping is only valid if the package instances in the game and the assumption
    // are excatly the same, i.e. they are different instances of the same package with
    // the same parameters.
    // TODO: this should probably just be (String, Expression)
    pub params: Vec<(PackageConstIdentifier, Expression)>,
    pub types: Vec<(String, Type)>,

    // this is the package - it has been rewritten, though!
    pub pkg: Package,
}

impl PackageInstance {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn pkg_name(&self) -> &str {
        &self.pkg.name
    }

    pub fn get_oracle_sigs(&self) -> Vec<OracleSig> {
        self.pkg
            .oracles
            .clone()
            .into_iter()
            .map(|d| d.sig)
            .collect()
    }

    pub fn params(&self) -> Vec<(&str, &Expression)> {
        let mut params: Vec<_> = self
            .params
            .iter()
            .map(|(name, expr)| (name.name.as_str(), expr))
            .collect();
        params.sort();
        params
    }

    /// instantiates the provided oraclae signature. this means that occurrences package parameters
    /// are replaced with the assigned values.
    ///
    /// this is needed for Bits(n), since the `n` is different in game and package.
    pub(crate) fn instantiate_oracle_signature(&self, sig: OracleSig) -> OracleSig {
        OracleSig {
            args: sig
                .args
                .into_iter()
                .map(|(name, ty)| (name, self.instantiate_type(ty)))
                .collect(),
            ty: self.instantiate_type(sig.ty),
            ..sig
        }
    }

    /// instantiates the provided type. this means that occurrences package parameters
    /// are replaced with the assigned values.
    ///
    /// This also means that the types somehow don't match 100%, this will just ignore that type and
    /// leave it as-is. But that shouldn't really happen, since we compare the types in the package
    /// params with the types in the code. But it could be the source of annoying-to-debug bugs.
    ///
    /// this is needed for Bits(n), since the `n` is different in game and package.
    pub(crate) fn instantiate_type(&self, ty: Type) -> Type {
        // we only want the ints, because the maybe be in Bits(n)
        let int_params = self
            .params
            .iter()
            .filter(|(_, expr)| matches!(expr.get_type().kind(), TypeKind::Integer))
            .map(|(ident, expr)| {
                let assigned_value = match expr.kind() {
                    ExpressionKind::Identifier(ident) => {
                        CountSpec::Identifier(Box::new(ident.clone()))
                    }
                    ExpressionKind::IntegerLiteral(num) => CountSpec::Literal(*num as u64),
                    _ => unreachable!(),
                };

                (
                    Type::bits(crate::types::CountSpec::Identifier(Box::new(
                        ident.clone().into(),
                    ))),
                    Type::bits(assigned_value),
                )
            })
            .collect_vec();

        // Also include type parameter rewrites
        let type_param_rules: Vec<_> = self
            .types
            .iter()
            .map(|(name, ty)| (Type::type_param(name.to_string()), ty.clone()))
            .collect();

        let all_rules: Vec<_> = int_params.into_iter().chain(type_param_rules).collect();

        ty.rewrite_type(&all_rules)
    }
}

impl PackageInstance {
    pub(crate) fn new(
        pkg_inst_name: &str,
        game_name: &str,
        pkg: &Package,
        params: Vec<(PackageConstIdentifier, Expression)>,
        types: Vec<(String, Type)>,
    ) -> PackageInstance {
        let inst_ctx: InstantiationContext =
            InstantiationContext::new_package_instantiation_context(
                pkg_inst_name,
                game_name,
                &params,
                &types,
            );

        let new_params = pkg
            .params
            .iter()
            .cloned()
            .map(|(name, ty, span)| (name, inst_ctx.rewrite_type(ty), span))
            .collect();

        let new_state = pkg
            .state
            .iter()
            .cloned()
            .map(|(name, ty, span)| (name, inst_ctx.rewrite_type(ty), span))
            .collect();

        let new_imports = pkg
            .imports
            .iter()
            .cloned()
            .map(|(sig, span)| (inst_ctx.rewrite_oracle_sig(sig), span))
            .collect();

        let new_oracles = pkg
            .oracles
            .iter()
            .map(|oracle_def| inst_ctx.rewrite_oracle_def(oracle_def.clone()))
            .collect();

        let pkg = Package {
            oracles: new_oracles,
            state: new_state,
            params: new_params,
            imports: new_imports,
            ..pkg.clone()
        };

        PackageInstance {
            params,
            types,
            pkg,
            name: pkg_inst_name.to_string(),
        }
    }
}

pub(crate) mod instantiate {
    use super::*;
    use crate::{
        identifier::{
            game_ident::{GameConstIdentifier, GameIdentifier},
            pkg_ident::{
                PackageLocalIdentifier, PackageOracleArgIdentifier, PackageStateIdentifier,
            },
        },
        statement::{InvokeOracle, *},
        types::TypeKind,
    };

    #[derive(Debug, Clone, Copy)]
    pub(crate) enum InstantiationSource<'a> {
        Package {
            const_assignments: &'a [(PackageConstIdentifier, Expression)],
        },

        Game {
            const_assignments: &'a [(GameConstIdentifier, Expression)],
        },
    }

    #[derive(Debug, Clone, Copy)]
    pub(crate) struct InstantiationContext<'a> {
        src: InstantiationSource<'a>,

        inst_name: &'a str,
        parent_name: &'a str,

        type_assignments: &'a [(String, Type)],
    }

    impl<'a> InstantiationContext<'a> {
        pub(crate) fn new_package_instantiation_context(
            inst_name: &'a str,
            parent_name: &'a str,
            consts: &'a [(PackageConstIdentifier, Expression)],
            types: &'a [(String, Type)],
        ) -> Self {
            Self {
                src: InstantiationSource::Package {
                    const_assignments: consts,
                },
                inst_name,
                parent_name,
                type_assignments: types,
            }
        }

        pub(crate) fn new_game_instantiation_context(
            inst_name: &'a str,
            parent_name: &'a str,
            consts: &'a [(GameConstIdentifier, Expression)],
            types: &'a [(String, Type)],
        ) -> Self {
            Self {
                src: InstantiationSource::Game {
                    const_assignments: consts,
                },
                inst_name,
                parent_name,
                type_assignments: types,
            }
        }

        pub(crate) fn rewrite_oracle_def(&self, oracle_def: OracleDef) -> OracleDef {
            OracleDef {
                sig: self.rewrite_oracle_sig(oracle_def.sig),
                code: self.rewrite_oracle_code(oracle_def.code),
                file_pos: oracle_def.file_pos,
            }
        }

        pub(crate) fn rewrite_count_spec(&self, count_spec: CountSpec) -> CountSpec {
            match count_spec {
                CountSpec::Identifier(id) => {
                    let src = &self.src;
                    match (src, *id) {
                        (
                            InstantiationSource::Package { const_assignments },
                            Identifier::PackageIdentifier(PackageIdentifier::Const(
                                mut pkg_const_ident,
                            )),
                        ) => {
                            let (_, assigned_expr) = const_assignments
                                .iter()
                                .find(|(ident, _)| ident.name == pkg_const_ident.name)
                                .expect("TODO todo: this should be a propoer error");

                            pkg_const_ident.set_pkg_inst_info(
                                self.inst_name.to_string(),
                                self.parent_name.to_string(),
                            );
                            pkg_const_ident.game_assignment = Some(Box::new(assigned_expr.clone()));

                            CountSpec::Identifier(Box::new(Identifier::PackageIdentifier(
                                PackageIdentifier::Const(pkg_const_ident),
                            )))
                        }

                        (
                            InstantiationSource::Game { const_assignments },
                            Identifier::GameIdentifier(GameIdentifier::Const(mut game_const_ident)),
                        ) => {
                            let (_, assigned_expr) = const_assignments
                                .iter()
                                .find(|(ident, _)| ident.name == game_const_ident.name)
                                .expect("TODO todo: this should be a propoer error");

                            game_const_ident.set_game_inst_info(
                                self.inst_name.to_string(),
                                self.parent_name.to_string(),
                            );
                            game_const_ident.assigned_value = Some(Box::new(assigned_expr.clone()));

                            CountSpec::Identifier(Box::new(Identifier::GameIdentifier(
                                GameIdentifier::Const(game_const_ident),
                            )))
                        }

                        // In this case we don't want to look up the value for the package const itself,
                        // but for the game const that is inside. We also make sure the names are set
                        // correctly. One thing we cannot do is set the assigned value on the package const
                        // itself: we can only look up values in the assignment of the game instance.
                        //
                        (
                            InstantiationSource::Game { .. },
                            Identifier::PackageIdentifier(PackageIdentifier::Const(
                                mut pkg_const_ident,
                            )),
                        ) => {
                            pkg_const_ident.set_game_inst_info(
                                self.inst_name.to_string(),
                                self.parent_name.to_string(),
                            );
                            CountSpec::Identifier(Box::new(Identifier::PackageIdentifier(
                                PackageIdentifier::Const(
                                    if let Some(expr) = pkg_const_ident.game_assignment {
                                        PackageConstIdentifier {
                                            game_assignment: Some(Box::new(
                                                self.rewrite_expression(expr.as_ref()),
                                            )),
                                            ..pkg_const_ident
                                        }
                                    } else {
                                        // XXX: is this a valid case, o should we be expect that every package
                                        // instance is already resolved up to the game at this point?
                                        pkg_const_ident
                                    },
                                ),
                            )))
                        }
                        (_, id) => CountSpec::Identifier(Box::new(id)),
                    }
                }
                other @ (CountSpec::Any | CountSpec::Literal(_)) => other,
            }
        }

        /// Returns rewrite rules for three cases:
        /// - Rewrites user-defined types to what they are assigned (which is currently not really supported)
        /// - Rewrite Bits(some_ident) such that some_ident has the instantiation information set, both
        ///   - for package instantiation
        ///   - for game instatiantion
        pub(crate) fn base_rewrite_rules(&self) -> Vec<(Type, Type)> {
            let mut type_rewrite_rules = self
                .type_assignments
                .iter()
                .map(|(name, ty)| (Type::type_param(name.to_string()), ty.clone()))
                .collect_vec();

            match self.src {
                InstantiationSource::Package { const_assignments } => {
                    type_rewrite_rules.extend(const_assignments.iter().map(|(ident, expr)| {
                        (
                            Type::bits(CountSpec::Identifier(Box::new(
                                Identifier::PackageIdentifier(PackageIdentifier::Const(
                                    ident.clone(),
                                )),
                            ))),
                            Type::bits(CountSpec::Identifier(Box::new(
                                Identifier::PackageIdentifier(PackageIdentifier::Const({
                                    let mut fixed_ident: PackageConstIdentifier = ident.clone();

                                    fixed_ident.set_pkg_inst_info(
                                        self.inst_name.to_string(),
                                        self.parent_name.to_string(),
                                    );
                                    fixed_ident.game_assignment = Some(Box::new(expr.clone()));

                                    fixed_ident
                                })),
                            ))),
                        )
                    }));
                }

                InstantiationSource::Game { const_assignments } => {
                    type_rewrite_rules.extend(const_assignments.iter().map(|(ident, expr)| {
                        (
                            Type::bits(CountSpec::Identifier(Box::new(
                                Identifier::GameIdentifier(GameIdentifier::Const(ident.clone())),
                            ))),
                            Type::bits(CountSpec::Identifier(Box::new(
                                Identifier::GameIdentifier(GameIdentifier::Const({
                                    let mut fixed_ident: GameConstIdentifier = ident.clone();

                                    fixed_ident.set_game_inst_info(
                                        self.inst_name.to_string(),
                                        self.parent_name.to_string(),
                                    );

                                    fixed_ident.assigned_value = Some(Box::new(expr.clone()));

                                    fixed_ident
                                })),
                            ))),
                        )
                    }));
                }
            }

            type_rewrite_rules
        }

        pub(crate) fn rewrite_type(&self, ty: Type) -> Type {
            let fix_vec = |tys: Vec<Type>| -> Vec<Type> {
                tys.into_iter().map(|ty| self.rewrite_type(ty)).collect()
            };

            match ty.into_kind() {
                TypeKind::Bits(cs) => Type::bits(self.rewrite_count_spec(cs)),
                TypeKind::Tuple(tys) => Type::tuple(fix_vec(tys)),
                TypeKind::Table(kty, vty) => {
                    Type::table(self.rewrite_type(*kty), self.rewrite_type(*vty))
                }
                TypeKind::Fn(arg_tys, ret_ty) => {
                    Type::fun(fix_vec(arg_tys), self.rewrite_type(*ret_ty))
                }

                TypeKind::List(ty) => Type::list(self.rewrite_type(*ty)),
                TypeKind::Maybe(ty) => Type::maybe(self.rewrite_type(*ty)),
                TypeKind::Set(ty) => Type::set(self.rewrite_type(*ty)),
                other => Type::from_kind(other),
            }
        }

        pub(crate) fn rewrite_oracle_sig(&self, oracle_sig: OracleSig) -> OracleSig {
            {
                OracleSig {
                    name: oracle_sig.name,
                    args: oracle_sig
                        .args
                        .into_iter()
                        .map(|(name, ty)| (name.clone(), self.rewrite_type(ty)))
                        .collect(),
                    ty: self.rewrite_type(oracle_sig.ty),
                }
            }
        }

        pub(crate) fn rewrite_oracle_code(&self, code: CodeBlock) -> CodeBlock {
            CodeBlock(
                code.0
                    .into_iter()
                    .map(|stmt| self.rewrite_statement(stmt))
                    .collect(),
            )
        }

        // pub(crate) fn rewrite_split_oracle_sig(
        //     &self,
        //     split_oracle_sig: &SplitOracleSig,
        // ) -> SplitOracleSig {
        //     let type_rewrite_rules: Vec<_> = self
        //         .type_assignments
        //         .iter()
        //         .map(|(name, ty)| (Type::UserDefined(name.to_string()), ty.clone()))
        //         .collect();
        //
        //     SplitOracleSig {
        //         name: split_oracle_sig.name.clone(),
        //         args: split_oracle_sig
        //             .args
        //             .iter()
        //             .map(|(name, ty)| (name.clone(), ty.rewrite(&type_rewrite_rules)))
        //             .collect(),
        //         partial_vars: split_oracle_sig
        //             .partial_vars
        //             .iter()
        //             .map(|(name, ty)| (name.clone(), ty.rewrite(&type_rewrite_rules)))
        //             .collect(),
        //         path: SplitPath::new(
        //             split_oracle_sig
        //                 .path
        //                 .path()
        //                 .iter()
        //                 .map(|component| crate::split::SplitPathComponent {
        //                     pkg_inst_name: component.pkg_inst_name.clone(),
        //                     oracle_name: component.oracle_name.clone(),
        //                     split_type: match &component.split_type {
        //                         SplitType::Plain
        //                         | SplitType::IfBranch
        //                         | SplitType::ElseBranch
        //                         | SplitType::Invoc(_) => component.split_type.clone(),
        //                         SplitType::ForStep(ident, start, end) => SplitType::ForStep(
        //                             ident.clone(),
        //                             self.rewrite_expression(start),
        //                             self.rewrite_expression(end),
        //                         ),
        //                         SplitType::IfCondition(expr) => {
        //                             SplitType::IfCondition(self.rewrite_expression(expr))
        //                         }
        //                     },
        //                     split_range: component.split_range.clone(),
        //                 })
        //                 .collect(),
        //         ),
        //         ty: split_oracle_sig.ty.rewrite(&type_rewrite_rules),
        //     }
        // }
        //
        // pub(crate) fn rewrite_split_oracle_def(
        //     &self,
        //     split_oracle_def: SplitOracleDef,
        // ) -> SplitOracleDef {
        //     SplitOracleDef {
        //         sig: self.rewrite_split_oracle_sig(&split_oracle_def.sig),
        //         code: self.rewrite_oracle_code(split_oracle_def.code),
        //     }
        // }

        pub(crate) fn rewrite_statement(&self, stmt: Statement) -> Statement {
            use crate::statement::{Assignment, AssignmentRhs, Pattern};
            let type_rewrite_rules = self.base_rewrite_rules();
            match stmt {
                Statement::Abort(_) => stmt.clone(),
                Statement::Return(expr, pos) => {
                    Statement::Return(expr.as_ref().map(|expr| self.rewrite_expression(expr)), pos)
                }

                Statement::Assignment(Assignment { pattern, rhs }, span) => {
                    let rewritten_pattern = match pattern {
                        Pattern::Ident(ident) => Pattern::Ident(self.rewrite_identifier(ident)),
                        Pattern::Table { ident, index } => Pattern::Table {
                            ident: self.rewrite_identifier(ident),
                            index: self.rewrite_expression(&index),
                        },
                        Pattern::Tuple(idents) => Pattern::Tuple(
                            idents
                                .into_iter()
                                .map(|ident| self.rewrite_identifier(ident))
                                .collect(),
                        ),
                    };

                    let rewritten_rhs = match rhs {
                        AssignmentRhs::Expression(expr) => {
                            AssignmentRhs::Expression(self.rewrite_expression(&expr))
                        }
                        AssignmentRhs::Sample {
                            ty,
                            sample_name,
                            sample_id,
                        } => AssignmentRhs::Sample {
                            ty: self.rewrite_type(ty),
                            sample_name,
                            sample_id,
                        },
                        AssignmentRhs::Invoke {
                            oracle_name,
                            args,
                            edge,
                            return_type,
                        } => AssignmentRhs::Invoke {
                            oracle_name,
                            args: args
                                .iter()
                                .map(|expr| self.rewrite_expression(expr))
                                .collect(),
                            edge,
                            return_type: return_type
                                .as_ref()
                                .map(|ty| ty.rewrite_type(&type_rewrite_rules)),
                        },
                    };

                    Statement::Assignment(
                        Assignment {
                            pattern: rewritten_pattern,
                            rhs: rewritten_rhs,
                        },
                        span,
                    )
                }

                Statement::InvokeOracle(InvokeOracle {
                    oracle_name,
                    args,
                    edge,
                    file_pos,
                }) => Statement::InvokeOracle(InvokeOracle {
                    oracle_name,
                    args: args
                        .iter()
                        .map(|expr| self.rewrite_expression(expr))
                        .collect(),
                    edge,
                    file_pos,
                }),

                Statement::IfThenElse(ite) => Statement::IfThenElse(IfThenElse {
                    cond: self.rewrite_expression(&ite.cond),
                    then_block: self.rewrite_oracle_code(ite.then_block),
                    else_block: self.rewrite_oracle_code(ite.else_block),
                    ..ite
                }),
                Statement::For(ident, start, end, code, pos) => Statement::For(
                    ident.clone(),
                    self.rewrite_expression(&start),
                    self.rewrite_expression(&end),
                    self.rewrite_oracle_code(code),
                    pos,
                ),
            }
        }
    }

    impl InstantiationContext<'_> {
        pub(crate) fn rewrite_expression(&self, expr: &Expression) -> Expression {
            expr.map(|expr| {
                let kind = match expr.into_kind() {
                    ExpressionKind::Identifier(ident) => {
                        ExpressionKind::Identifier(self.rewrite_identifier(ident))
                    }

                    // can only happen in oracle code, i.e. package code
                    ExpressionKind::TableAccess(ident, expr) => {
                        ExpressionKind::TableAccess(self.rewrite_identifier(ident), expr)
                    }
                    ExpressionKind::EmptyTable(ty) => {
                        ExpressionKind::EmptyTable(self.rewrite_type(ty))
                    }
                    ExpressionKind::FnCall(ident, args) => {
                        ExpressionKind::FnCall(self.rewrite_identifier(ident), args)
                    }
                    ExpressionKind::None(ty) => ExpressionKind::None(self.rewrite_type(ty)),
                    ExpressionKind::Sample(ty) => ExpressionKind::Sample(self.rewrite_type(ty)),
                    ExpressionKind::BitsLiteral(content, ty) => {
                        ExpressionKind::BitsLiteral(content, self.rewrite_type(ty))
                    }

                    expr => expr,
                };

                Expression::from_kind(kind)
            })
        }

        pub(crate) fn rewrite_pkg_identifier(
            &self,
            mut pkg_ident: PackageIdentifier,
        ) -> PackageIdentifier {
            match self.src {
                InstantiationSource::Package { const_assignments } => {
                    pkg_ident.set_pkg_inst_info(
                        self.inst_name.to_string(),
                        self.parent_name.to_string(),
                    );

                    if let PackageIdentifier::Const(pkg_const_ident) = &mut pkg_ident {
                        let (_, ref assignment) = const_assignments
                            .iter()
                            .find(|(assignment_const_ident, _)| {
                                assignment_const_ident.name == pkg_const_ident.name
                            })
                            .unwrap();

                        pkg_const_ident.set_assignment(assignment.clone());
                    }

                    pkg_ident
                }
                InstantiationSource::Game { .. } => {
                    if let Some(ident) = &mut pkg_ident.as_const_mut() {
                        if let Some(assignment) = ident.game_assignment.as_mut() {
                            if let ExpressionKind::Identifier(ident) =
                                assignment.as_mut().kind_mut()
                            {
                                *ident = self.rewrite_identifier(ident.clone())
                            }
                        }
                    }

                    pkg_ident.set_game_inst_info(
                        self.inst_name.to_string(),
                        self.parent_name.to_string(),
                    );
                    pkg_ident
                }
            }
        }

        pub(crate) fn rewrite_game_identifier(
            &self,
            mut game_ident: GameIdentifier,
        ) -> GameIdentifier {
            match self.src {
                InstantiationSource::Game { const_assignments } => {
                    game_ident.set_game_inst_info(
                        self.inst_name.to_string(),
                        self.parent_name.to_string(),
                    );
                    if let GameIdentifier::Const(game_const_ident) = &mut game_ident {
                        let (_, ref assignment) = const_assignments
                            .iter()
                            .find(|(assignment_const_ident, _)| {
                                assignment_const_ident.name == game_const_ident.name
                            })
                            .unwrap();

                        game_const_ident.set_assignment(assignment.clone());
                    }
                    game_ident
                }
                InstantiationSource::Package { .. } => {
                    unreachable!(
                        r#"found game identifier `{name}' when instantiating package
    identifier: {game_ident:?}
    inst ctx:   {self:?}"#,
                        name = game_ident.ident(),
                    )
                }
            }
        }

        pub(crate) fn rewrite_identifier(&self, ident: Identifier) -> Identifier {
            let type_rewrite_rules = self.base_rewrite_rules();

            // extend the identifier with the instance and parent names
            let ident = match ident {
                Identifier::PackageIdentifier(pkg_ident) => {
                    self.rewrite_pkg_identifier(pkg_ident).into()
                }
                Identifier::GameIdentifier(game_ident) => {
                    self.rewrite_game_identifier(game_ident).into()
                }

                ident @ Identifier::TheoremIdentifier(_) | ident @ Identifier::Generated(_, _) => {
                    ident
                }
            };

            // rewrite the types
            #[allow(clippy::let_and_return)]
            let new_ident = match ident {
                Identifier::PackageIdentifier(pkg_ident) => {
                    let pkg_ident = match pkg_ident {
                        PackageIdentifier::Const(const_ident) => {
                            PackageIdentifier::Const(PackageConstIdentifier {
                                ty: const_ident.ty.rewrite_type(&type_rewrite_rules),
                                ..const_ident
                            })
                        }
                        PackageIdentifier::State(state_ident) => {
                            PackageIdentifier::State(PackageStateIdentifier {
                                ty: state_ident.ty.rewrite_type(&type_rewrite_rules),
                                ..state_ident
                            })
                        }
                        PackageIdentifier::Local(local_ident) => {
                            PackageIdentifier::Local(PackageLocalIdentifier {
                                ty: local_ident.ty.rewrite_type(&type_rewrite_rules),
                                ..local_ident
                            })
                        }
                        // XXX: A bit unclear whether we keep this variant... it conflicts witht he
                        // Oracle variant of Declaration, so we only need one and so far we use the
                        // other.
                        PackageIdentifier::OracleImport(_) => todo!(),

                        PackageIdentifier::OracleArg(arg_ident) => {
                            PackageIdentifier::OracleArg(PackageOracleArgIdentifier {
                                ty: arg_ident.ty.rewrite_type(&type_rewrite_rules),
                                ..arg_ident.clone()
                            })
                        }
                        // no types to rewrite here
                        ident @ PackageIdentifier::ImportsLoopVar(_) => ident,
                        ident @ PackageIdentifier::CodeLoopVar(_) => ident,
                    };

                    Identifier::PackageIdentifier(pkg_ident)
                }

                Identifier::GameIdentifier(_) => ident.clone(),

                Identifier::TheoremIdentifier(_) => unreachable!(
                    "unexpected theorem identifier when instantiating package: {:?}",
                    ident
                ),

                other => unreachable!("won't rewrite deprecated identifier {:?}", other),
            };

            new_ident
        }
    }
}
