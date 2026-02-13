#[derive(Clone, Debug, Copy)]
pub(crate) struct PackageInstanceContext<'a> {
    pub(crate) theorem_name: &'a str,
    pub(crate) game_inst_name: &'a str,
    pub(crate) game_name: &'a str,
    pub(crate) pkg_inst_name: &'a str,
    pub(crate) pkg_name: &'a str,
}
