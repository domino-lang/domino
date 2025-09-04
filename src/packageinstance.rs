use itertools::Itertools as _;

use crate::{
    expressions::Expression,
    identifier::{
        pkg_ident::{PackageConstIdentifier, PackageIdentifier},
        Identifier,
    },
    package::{OracleDef, OracleSig, Package},
    parser::package::MultiInstanceIndices,
    types::{CountSpec, Type},
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

    // These are probably deprecated?
    pub multi_instance_indices: MultiInstanceIndices,
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
            .filter(|(_, expr)| matches!(expr.get_type(), Type::Integer))
            .map(|(ident, expr)| {
                let assigned_value = match expr {
                    Expression::Identifier(ident) => CountSpec::Identifier(ident.clone()),
                    Expression::IntegerLiteral(num) => CountSpec::Literal(*num as u64),
                    _ => unreachable!(),
                };

                (
                    Type::Bits(Box::new(crate::types::CountSpec::Identifier(
                        ident.clone().into(),
                    ))),
                    Type::Bits(Box::new(assigned_value)),
                )
            })
            .collect_vec();

        ty.rewrite_type(&int_params)
    }
}

impl PackageInstance {
    pub(crate) fn new(
        pkg_inst_name: &str,
        game_name: &str,
        pkg: &Package,
        multi_instance_indices: MultiInstanceIndices,
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
            multi_instance_indices,
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
        statement::*,
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
            match (self.src, count_spec) {
                (
                    InstantiationSource::Package { const_assignments },
                    CountSpec::Identifier(Identifier::PackageIdentifier(PackageIdentifier::Const(
                        mut pkg_const_ident,
                    ))),
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

                    CountSpec::Identifier(Identifier::PackageIdentifier(PackageIdentifier::Const(
                        pkg_const_ident,
                    )))
                }

                (
                    InstantiationSource::Game { const_assignments },
                    CountSpec::Identifier(Identifier::GameIdentifier(GameIdentifier::Const(
                        mut game_const_ident,
                    ))),
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

                    CountSpec::Identifier(Identifier::GameIdentifier(GameIdentifier::Const(
                        game_const_ident,
                    )))
                }

                // In this case we don't want to look up the value for the package const itself,
                // but for the game const that is inside. We also make sure the names are set
                // correctly. One thing we cannot do is set the assigned value on the package const
                // itself: we can only look up values in the assignment of the game instance.
                //
                (
                    InstantiationSource::Game { .. },
                    CountSpec::Identifier(Identifier::PackageIdentifier(PackageIdentifier::Const(
                        mut pkg_const_ident,
                    ))),
                ) => {
                    pkg_const_ident.set_game_inst_info(
                        self.inst_name.to_string(),
                        self.parent_name.to_string(),
                    );
                    CountSpec::Identifier(Identifier::PackageIdentifier(PackageIdentifier::Const(
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
                    )))
                }

                (_, other @ (CountSpec::Any | CountSpec::Literal(_))) => other,

                // not entirely sure about this one:
                (_, other) => other,
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
                .map(|(name, ty)| (Type::UserDefined(name.to_string()), ty.clone()))
                .collect_vec();

            match self.src {
                InstantiationSource::Package { const_assignments } => {
                    type_rewrite_rules.extend(const_assignments.iter().map(|(ident, expr)| {
                        (
                            Type::Bits(Box::new(CountSpec::Identifier(
                                Identifier::PackageIdentifier(PackageIdentifier::Const(
                                    ident.clone(),
                                )),
                            ))),
                            Type::Bits(Box::new(CountSpec::Identifier(
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
                            Type::Bits(Box::new(CountSpec::Identifier(
                                Identifier::GameIdentifier(GameIdentifier::Const(ident.clone())),
                            ))),
                            Type::Bits(Box::new(CountSpec::Identifier(
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
            let fix_box = |bxty: Box<Type>| -> Box<Type> { Box::new(self.rewrite_type(*bxty)) };
            let fix_vec = |tys: Vec<Type>| -> Vec<Type> {
                tys.into_iter().map(|ty| self.rewrite_type(ty)).collect()
            };

            match ty {
                Type::Bits(cs) => Type::Bits(Box::new(self.rewrite_count_spec(*cs))),
                Type::Tuple(tys) => Type::Tuple(fix_vec(tys)),
                Type::Table(kty, vty) => Type::Table(fix_box(kty), fix_box(vty)),
                Type::Fn(arg_tys, ret_ty) => Type::Fn(fix_vec(arg_tys), fix_box(ret_ty)),

                Type::List(ty) => Type::List(fix_box(ty)),
                Type::Maybe(ty) => Type::Maybe(fix_box(ty)),
                Type::Set(ty) => Type::Set(fix_box(ty)),
                other => other,
            }
        }

        pub(crate) fn rewrite_oracle_sig(&self, oracle_sig: OracleSig) -> OracleSig {
            {
                OracleSig {
                    name: oracle_sig.name,
                    multi_inst_idx: oracle_sig.multi_inst_idx,
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
            let type_rewrite_rules = self.base_rewrite_rules();
            match stmt {
                Statement::Abort(_) => stmt.clone(),
                Statement::Return(expr, pos) => {
                    Statement::Return(expr.as_ref().map(|expr| self.rewrite_expression(expr)), pos)
                }

                Statement::Assign(ident, index, value, pos) => Statement::Assign(
                    self.rewrite_identifier(ident),
                    index.as_ref().map(|expr| self.rewrite_expression(expr)),
                    self.rewrite_expression(&value),
                    pos,
                ),
                Statement::Parse(idents, expr, pos) => Statement::Parse(
                    idents
                        .into_iter()
                        .map(|ident| self.rewrite_identifier(ident))
                        .collect(),
                    self.rewrite_expression(&expr),
                    pos,
                ),
                Statement::Sample(ident, index, sample_id, ty, sample_name, pos) => {
                    Statement::Sample(
                        self.rewrite_identifier(ident),
                        index.as_ref().map(|expr| self.rewrite_expression(expr)),
                        sample_id,
                        self.rewrite_type(ty),
                        sample_name,
                        pos,
                    )
                }
                Statement::InvokeOracle(InvokeOracleStatement {
                    id,
                    opt_idx,
                    opt_dst_inst_idx,
                    name,
                    args,
                    target_inst_name,
                    ty,
                    file_pos,
                }) => Statement::InvokeOracle(InvokeOracleStatement {
                    name,
                    target_inst_name,
                    file_pos,

                    id: self.rewrite_identifier(id),
                    opt_idx: opt_idx.as_ref().map(|expr| self.rewrite_expression(expr)),
                    opt_dst_inst_idx: opt_dst_inst_idx
                        .as_ref()
                        .map(|expr| self.rewrite_expression(expr)),
                    args: args
                        .iter()
                        .map(|expr| self.rewrite_expression(expr))
                        .collect(),
                    ty: ty.as_ref().map(|ty| ty.rewrite_type(&type_rewrite_rules)),
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
            expr.map(|expr| match expr {
                Expression::Identifier(ident) => {
                    Expression::Identifier(self.rewrite_identifier(ident))
                }

                // can only happen in oracle code, i.e. package code
                Expression::TableAccess(ident, expr) => {
                    Expression::TableAccess(self.rewrite_identifier(ident), expr)
                }
                Expression::EmptyTable(ty) => Expression::EmptyTable(self.rewrite_type(ty)),
                Expression::FnCall(ident, args) => {
                    Expression::FnCall(self.rewrite_identifier(ident), args)
                }
                Expression::None(ty) => Expression::None(self.rewrite_type(ty)),
                Expression::Sample(ty) => Expression::Sample(self.rewrite_type(ty)),

                expr => expr,
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
                            if let Expression::Identifier(ident) = assignment.as_mut() {
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
                        // other. Also this one doesn't seem to support multi instance
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
