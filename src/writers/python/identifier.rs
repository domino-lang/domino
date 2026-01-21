use core::fmt::Display;

macro_rules! ident_type {
    ($name:ident, $format:literal) => {
        #[derive(Clone, Copy, Debug)]
        pub(crate) struct $name<'a>(pub(crate) &'a str);
        impl<'a> Display for $name<'a> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                let Self(name) = self;
                write!(f, $format, name)
            }
        }
        impl<'a> $name<'a> {
            pub(crate) fn name(self) -> &'a str {
                self.0
            }
        }
    };
}

// not using macro for this because it has more than one field
#[derive(Clone, Copy, Debug)]
pub(crate) struct OracleFunctionName<'a> {
    pub(crate) pkg_inst_name: &'a str,
    pub(crate) oracle_name: &'a str,
}

impl<'a> Display for OracleFunctionName<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self {
            pkg_inst_name,
            oracle_name,
        } = self;
        write!(f, "oracle_{pkg_inst_name}_{oracle_name}")
    }
}

ident_type!(GameStateTypeName, "GameState_{}");
ident_type!(PackageStateTypeName, "PackageState_{}");
ident_type!(PackageStateFieldName, "{}");
ident_type!(PackageConstParamsTypeName, "PackageConstParams_{}");
ident_type!(PackageConstParamsFieldName, "{}");
ident_type!(FunctionName, "{}");
ident_type!(FunctionArgName, "{}");

ident_type!(PureFunctionName, "fun_{}");
ident_type!(PureFunctionArg, "{}");
ident_type!(VariableName, "{}");

#[derive(Clone, Copy)]
pub(super) enum GameStateFieldName<'a> {
    PackageConstParams(&'a str),
    PackageState(&'a str),
    Randomness(&'a str),
}

#[derive(Clone, Copy)]
pub(crate) enum OracleFunctionArg<'a> {
    GameState,
    PackageInstanceName,
    OracleArg(&'a str),
}

impl<'a> Display for GameStateFieldName<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GameStateFieldName::PackageConstParams(name) => write!(f, "consts_{name}"),
            GameStateFieldName::PackageState(name) => write!(f, "pkg_{name}"),
            GameStateFieldName::Randomness(_) => todo!(),
        }
    }
}
