use super::pkg_inst_context::PackageInstanceContext;

/**
*
* An Oracle Context contains
* * theorem name
* * game instance name
* * game name
* * package instance name
* * The package name
*
* It is passed into all the operations on statements and expressions in oracles.
* This way they can include necessary context as needed.
*
* The reason we include the intance context here is that we actually need to generate different
* code for different package instances, because the same package will call different oracles
* depending on how it is wired up. This is instance-dependent.
*
* Note: Sometimes we may only process one package instance per package type. For example when
* generating the structs. In those cases we must not access the instance fields. This is a bit
* hacky and the caller needs to keep track of which fields it accessis in these situations.
*
*
*/

#[derive(Clone, Debug, Copy)]
pub(crate) struct OracleContext<'a> {
    pub(crate) pkg_inst_context: PackageInstanceContext<'a>,
    pub(crate) oracle_name: &'a str,
}
