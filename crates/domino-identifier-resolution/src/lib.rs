use domino_ast::{
    arena::Ref,
    ast_nodes::{identifier, oracles, package, statements},
};

pub mod diag;
mod scope;

mod resolve_package;
pub use resolve_package::PackageVisitor;

#[derive(Debug, Clone, Copy)]
pub enum BuiltinType {
    Integer,
    Bool,
    Bits,
    Table,
    Maybe,
}

#[derive(Debug, Clone, Copy)]
pub enum BuiltinValue {
    True,
    False,
    Some,
    None,
}

#[derive(Debug, Clone, Copy)]
pub enum Declaration {
    Package(Ref<package::Package>),
    OracleImport(Ref<oracles::OracleSignature>),

    BuiltinType(BuiltinType),
    TypeParam(Ref<identifier::PackageTypeIdentifier>),

    Const(Ref<package::PackageConstDecl>),
    State(Ref<package::PackageConstDecl>),

    OracleArg(Ref<oracles::OracleValueArgDecl>),
    OracleLocal(Ref<statements::AssignStatement>),
    BuiltinValue(BuiltinValue),
}

#[derive(Debug)]
pub enum DeclarationType {
    Package,
    OracleImport,
    Type,
    PureValue,
    Value,
}

impl Declaration {
    fn decl_type(&self) -> DeclarationType {
        match self {
            Declaration::Package(_) => DeclarationType::Package,
            Declaration::OracleImport(_) => DeclarationType::OracleImport,

            Declaration::TypeParam(_) => DeclarationType::Type,
            Declaration::BuiltinType(_) => DeclarationType::Type,

            Declaration::BuiltinValue(BuiltinValue::True) => DeclarationType::PureValue,
            Declaration::BuiltinValue(BuiltinValue::False) => DeclarationType::PureValue,
            Declaration::BuiltinValue(BuiltinValue::None) => DeclarationType::PureValue,
            Declaration::Const(_) => DeclarationType::PureValue,
            Declaration::State(_) => DeclarationType::Value,

            Declaration::OracleArg(_) => DeclarationType::Value,
            Declaration::OracleLocal(_) => DeclarationType::Value,

            // TODO: Actually, whether this is pure or not depends on whether the inner expression
            //       is pure, but we can't tell that at this point, so we are conservative.
            Declaration::BuiltinValue(BuiltinValue::Some) => DeclarationType::Value,
        }
    }
}

impl core::fmt::Display for DeclarationType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DeclarationType::Package => f.write_str("package"),
            DeclarationType::OracleImport => f.write_str("oracle"),
            DeclarationType::Type => f.write_str("type"),
            DeclarationType::PureValue => f.write_str("pure value"),
            DeclarationType::Value => f.write_str("value"),
        }
    }
}
