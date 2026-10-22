use crate::{
    identifier::{
        pkg_ident::{PackageIdentifier, PackageStateIdentifier},
        Identifier,
    },
    package::OracleDef,
    writers::smt::{
        contexts::PackageInstanceContext,
        exprs::{SmtExpr, SmtLet},
        patterns::{
            pkg_consts, variables::GameStatePattern, DatastructurePattern, FunctionPattern,
            PackageStateSelector,
        },
    },
};

impl<'a> PackageInstanceContext<'a> {
    pub(crate) fn smt_define_oracle_fn(&self, def: &OracleDef) -> SmtExpr {
        let pkg_inst_name = &self.pkg_inst_name();
        let oracle_sig = &def.sig;
        let oracle_name = &oracle_sig.name;

        let octx = self
            .oracle_ctx_by_name(oracle_name)
            .expect("couldn't find oracle with name {oracle_name}");

        let var_globalstate = &GameStatePattern;
        let pkg_state = self
            .game_ctx
            .smt_access_gamestate_pkgstate(var_globalstate, pkg_inst_name)
            .unwrap();

        let inner = octx.smt_codeblock(def.code.clone());

        let pkgstate_bindings = self.pkg().state.iter().map(|(name, _ty, _)| {
            (
                name.clone(),
                self.smt_access_pkgstate(pkg_state.clone(), name).unwrap(),
            )
        });

        let pkg_consts = self
            .function_pkg_const_pattern()
            .call(&["<game-consts>".into()])
            .unwrap();

        let const_bindwrapped = pkg_consts::bind_pkg_consts(self.pkg(), &pkg_consts, inner);

        let state_bindwrapped = SmtLet {
            bindings: pkgstate_bindings.collect(),
            body: const_bindwrapped,
        };

        log::debug!("pkg inst params: {:?}", self.pkg_params());

        octx.oracle_pattern().define_fun(state_bindwrapped).into()
    }

    pub(crate) fn smt_access_pkgstate<S: Into<SmtExpr>>(
        &self,
        pkg_state: S,
        field_name: &str,
    ) -> Option<SmtExpr> {
        let pkg = &self.game().pkgs[self.inst_offs].pkg;

        let pkg_state_pattern = self.pkg_state_pattern();
        let pkg_state_spec = pkg_state_pattern.datastructure_spec(pkg);
        let pkg_state_field = self.field_selector(field_name)?;

        pkg_state_pattern.access(&pkg_state_spec, &pkg_state_field, pkg_state)
    }

    pub(crate) fn smt_update_pkgstate_from_locals(&self) -> Option<SmtExpr> {
        let game = self.game();
        let game_inst = self.game_inst();
        let pkg_inst = &game.pkgs[self.inst_offs];
        let pkg = &pkg_inst.pkg;
        let pkg_name = &pkg.name;

        let pkg_state_pattern = self.pkg_state_pattern();
        let pkg_state_spec = pkg_state_pattern.datastructure_spec(pkg);

        pkg_state_pattern.call_constructor(&pkg_state_spec, vec![], &(), |sel| {
            let PackageStateSelector { name, ty } = *sel;
            Some(
                Identifier::PackageIdentifier(PackageIdentifier::State(PackageStateIdentifier {
                    pkg_name: pkg_name.clone(),
                    name: name.to_string(),
                    ty: ty.clone(),
                    pkg_inst_name: Some(pkg_inst.name.clone()),
                    game_name: Some(game.name.clone()),
                    game_inst_name: Some(game_inst.name.clone()),
                    theorem_name: None,
                }))
                .into(),
            )
        })
    }
}
