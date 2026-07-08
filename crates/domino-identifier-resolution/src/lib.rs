pub mod diag;
mod scope;

mod resolve_package;

pub use resolve_package::{PackageInfo, PackageVisitor};

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

pub trait Declaration: From<BuiltinType> + From<BuiltinValue> {
    fn decl_type(&self) -> DeclarationType;
}

#[derive(Debug, Clone, Copy)]
pub enum DeclarationType {
    Package,
    OracleImport,
    Type,
    PureValue,
    Value,
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
