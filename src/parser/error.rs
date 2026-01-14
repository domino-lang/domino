// SPDX-License-Identifier: MIT OR Apache-2.0

use std::fmt::{Debug, Display};

use miette::{Diagnostic, SourceSpan};
use pest::error::ErrorVariant;
use thiserror::Error;

use crate::types::Type;

use super::ast::Identifier as _;

pub enum NewError {}

#[derive(Error, Diagnostic, Debug)]
#[error("syntax error: {variant}")]
#[diagnostic(code(domino::syntax))]
pub struct PestParseError {
    #[label("here")]
    pub at: SourceSpan,

    variant: PestErrorVariantPrinter,
}

#[derive(Debug)]
pub struct PestErrorVariantPrinter(ErrorVariant<super::Rule>);

impl Display for PestErrorVariantPrinter {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.0 {
            ErrorVariant::ParsingError {
                positives,
                negatives,
            } => {
                writeln!(f, "(pos {positives:?}) (neg {negatives:?}) ")?;
            }
            ErrorVariant::CustomError { message } => write!(f, "{message}")?,
        }

        Ok(())
    }
}

#[derive(Error, Diagnostic, Debug)]
#[error("undefined type '{text}'")]
#[diagnostic(code(domino::code::undefined_type))]
pub struct UndefinedTypeError {
    #[label("this type is not defined")]
    pub at: SourceSpan,

    pub text: String,
}

#[derive(Error, Diagnostic, Debug)]
#[error("undefined identifier '{ident_name}'")]
#[diagnostic(code(domino::code::undefined_identifier))]
pub struct UndefinedIdentifierError {
    #[source_code]
    pub source_code: miette::NamedSource<String>,

    #[label("this identifier is not defined")]
    pub at: SourceSpan,

    pub ident_name: String,
}

#[derive(Debug, Diagnostic, Error)]
#[error("identifier '{ident_name}' has already been declared")]
#[diagnostic(code(domino::code::identifier_already_declared))]
pub struct IdentifierAlreadyDeclaredError {
    #[source_code]
    pub source_code: miette::NamedSource<String>,

    #[label("this identifier here")]
    pub at: SourceSpan,

    // TODO: would be nice to be also have a span for the original definition
    //       this requires keeping definition location info in the scope
    pub ident_name: String,
}

#[derive(Debug, Diagnostic, Error)]
#[error("oracle '{oracle_name}' has already been declared")]
#[diagnostic(code(domino::code::oracle_already_declared))]
pub struct OracleAlreadyImportedError {
    #[source_code]
    pub source_code: miette::NamedSource<String>,

    #[label("this oracle here")]
    pub at: SourceSpan,

    pub oracle_name: String,
}

#[derive(Error, Diagnostic, Debug)]
#[error("type mismatch: got {got}, expected {expected}")]
#[diagnostic(code(domino::code::type_mismatch))]
pub struct TypeMismatchError {
    #[label("this expression has the wrong type")]
    pub at: SourceSpan,

    pub expected: Type,

    pub got: Type,

    #[source_code]
    pub source_code: miette::NamedSource<String>,
}

#[derive(Error, Diagnostic, Debug)]
#[error("argument count mismatch: got {got}, expected {expected}")]
#[diagnostic(code(domino::code::type_mismatch))]
pub struct ArgumentCountMismatchError {
    #[label("this expression has the wrong number of arguments")]
    pub at: SourceSpan,

    pub expected: usize,

    pub got: usize,

    #[source_code]
    pub source_code: miette::NamedSource<String>,
}

#[derive(Error, Diagnostic, Debug)]
#[error("package instance '{pkg_inst_name}' is not defined in game {in_game}")]
#[diagnostic(code(domino::code::undefined_package_instance))]
pub struct UndefinedPackageInstanceError {
    #[source_code]
    pub source_code: miette::NamedSource<String>,

    #[label("this package instance is not defined")]
    pub at: SourceSpan,

    pub pkg_inst_name: String,
    pub in_game: String,
}

#[derive(Error, Diagnostic, Debug)]
#[error("undefined game instance '{game_inst_name}'")]
#[diagnostic(code(domino::code::undefined_game_instance))]
pub struct UndefinedGameInstanceError {
    #[source_code]
    pub source_code: miette::NamedSource<String>,

    #[label("this game instance is not defined")]
    pub at: SourceSpan,

    pub game_inst_name: String,
}

#[derive(Error, Diagnostic, Debug)]
#[error("undefined package '{pkg_name}'")]
#[diagnostic(code(domino::code::undefined_package))]
pub struct UndefinedPackageError {
    #[source_code]
    pub source_code: miette::NamedSource<String>,

    #[label("this package is not defined")]
    pub at: SourceSpan,

    pub pkg_name: String,
}

#[derive(Error, Diagnostic, Debug)]
#[error("undefined oracle '{oracle_name}'")]
#[diagnostic(code(domino::code::undefined_package))]
pub struct UndefinedOracleError {
    #[source_code]
    pub source_code: miette::NamedSource<String>,

    #[label("this oracle is not defined")]
    pub at: SourceSpan,

    pub oracle_name: String,
}

#[derive(Error, Diagnostic, Debug)]
#[error("undefined game '{game_name}'")]
#[diagnostic(code(domino::code::undefined_game))]
pub struct UndefinedGameError {
    #[source_code]
    pub source_code: miette::NamedSource<String>,

    #[label("this game is not defined")]
    pub at: SourceSpan,

    pub game_name: String,
}

#[derive(Debug, Diagnostic, Error)]
#[error("parameter '{param_name}' does not exist on package {pkg_name}")]
#[diagnostic(code(domino::code::pkg::no_such_parameter))]
pub struct NoSuchPackageParameterError {
    #[source_code]
    pub source_code: miette::NamedSource<String>,

    #[label("this identifier here")]
    pub at: SourceSpan,

    pub param_name: String,
    pub pkg_name: String,
}

#[derive(Debug, Diagnostic, Error)]
#[error("parameter '{param_name}' does not exist on game {game_name}")]
#[diagnostic(code(domino::code::game::no_such_parameter))]
pub struct NoSuchGameParameterError {
    #[source_code]
    pub source_code: miette::NamedSource<String>,

    #[label("this identifier here")]
    pub at: SourceSpan,

    pub param_name: String,
    pub game_name: String,
}

#[derive(Debug, Diagnostic, Error)]
#[error("type '{type_name}' does not exist ")]
#[diagnostic(code(domino::code::no_such_type))]
pub struct NoSuchTypeError {
    #[source_code]
    pub source_code: miette::NamedSource<String>,

    #[label("this type here")]
    pub at: SourceSpan,

    pub type_name: String,
}

#[derive(Debug, Diagnostic, Error)]
#[error("oracle '{oracle_name}' does not exist ")]
#[diagnostic(code(domino::code::no_such_oracle))]
pub struct NoSuchOracleError {
    #[source_code]
    pub source_code: miette::NamedSource<String>,

    #[label("this oracle here")]
    pub at: SourceSpan,

    pub oracle_name: String,
}

#[derive(Debug, Diagnostic, Error)]
#[error("identifiers in for loop spec don't match: {fst:?} != {snd:?}")]
#[diagnostic(code(domino::code::no_such_oracle))]
pub struct ForLoopIdentifersDontMatchError {
    #[source_code]
    pub source_code: miette::NamedSource<String>,

    #[label("this identifer...")]
    pub at_fst: SourceSpan,

    #[label("...should be the same as this")]
    pub at_snd: SourceSpan,

    pub fst: String,
    pub snd: String,
}

#[derive(Debug, Diagnostic, Error)]
#[error(
    "package parameter '{param_name}' has been defined twice in package instance {pkg_inst_name}"
)]
#[diagnostic(code(domino::code::pkg_inst::duplicate_parameter_definition))]
pub struct DuplicatePackageParameterDefinitionError {
    #[source_code]
    pub source_code: miette::NamedSource<String>,

    #[label("this identifier here")]
    pub at: SourceSpan,

    #[label("has previously been defined here")]
    pub other: SourceSpan,

    pub param_name: String,
    pub pkg_inst_name: String,
}

#[derive(Debug, Diagnostic, Error)]
#[error("game parameter '{param_name}' has been defined twice in game instance {game_inst_name}")]
#[diagnostic(code(domino::code::game_inst::duplicate_parameter_definition))]
pub struct DuplicateGameParameterDefinitionError {
    #[source_code]
    pub source_code: miette::NamedSource<String>,

    #[label("this identifier here")]
    pub at: SourceSpan,

    #[label("has previously been defined here")]
    pub other: SourceSpan,

    pub param_name: String,
    pub game_inst_name: String,
}

#[derive(Debug, Diagnostic, Error)]
#[error("package {pkg_name} declares parameters that are not defined in package instance {pkg_inst_name}: {missing_params}")]
#[diagnostic(code(domino::code::pkg::missing_parameter_definition))]
pub struct MissingPackageParameterDefinitionError {
    #[source_code]
    pub source_code: miette::NamedSource<String>,

    #[label("this parameter definition block")]
    pub at: SourceSpan,

    pub pkg_name: String,
    pub pkg_inst_name: String,

    pub missing_params_vec: Vec<String>,
    pub missing_params: String,
}

#[derive(Debug, Diagnostic, Error)]
#[error("game {game_name} declares parameters that are not defined in game instance {game_inst_name}: {missing_params}")]
#[diagnostic(code(domino::code::game::missing_parameter_definition))]
pub struct MissingGameParameterDefinitionError {
    #[source_code]
    pub source_code: miette::NamedSource<String>,

    #[label("this parameter definition block")]
    pub at: SourceSpan,

    pub game_name: String,
    pub game_inst_name: String,

    pub missing_params_vec: Vec<String>,
    pub missing_params: String,
}

#[derive(Debug, Diagnostic, Error)]
#[error("theorem does not follow from the game hops")]
#[diagnostic(code(ssbee::code::unproven_theorem))]
pub struct UnprovenTheoremError {
    #[source_code]
    pub source_code: miette::NamedSource<String>,

    #[label("this theorem here")]
    pub at: SourceSpan,

    pub theorem_name: String,
}

#[derive(Debug, Diagnostic, Error)]
#[error("use of undefined assumption {assumption_name}")]
#[diagnostic(code(domino::code::undefined_assumption))]
pub struct UndefinedAssumptionError {
    #[source_code]
    pub source_code: miette::NamedSource<String>,

    #[label("this assumption here")]
    pub at: SourceSpan,

    pub assumption_name: String,
}

#[derive(Debug, Diagnostic, Error)]
#[error("the first package instance name in an assumption package mapping block header must be from the assumption, but isn't")]
#[diagnostic(code(
    domino::code::theorem::reduction::assumption_mapping::no_assumption_game_instance
))]
#[help("the mapping maps the package instances of the assumption game and the model game. Therefore the first needs to be an assumption game instance, while the other needs to be a model game instance. Game instance names from the assumption are {assumption_left_game_instance_name} and {assumption_right_game_instance_name}.")]
pub struct AssumptionMappingLeftGameInstanceIsNotFromAssumption {
    #[source_code]
    pub source_code: miette::NamedSource<String>,

    #[label("this game instance name")]
    pub at: SourceSpan,

    pub game_instance_name: String,

    pub assumption_left_game_instance_name: String,
    pub assumption_right_game_instance_name: String,
}

#[derive(Debug, Diagnostic, Error)]
#[error("the second package instance name in an assumption package mapping block header must be from the model (i.e. not from the assumption), but isn't")]
#[diagnostic(code(
    domino::code::theorem::reduction::assumption_mapping::no_assumption_game_instance
))]
pub struct AssumptionMappingRightGameInstanceIsFromAssumption {
    #[source_code]
    pub source_code: miette::NamedSource<String>,

    #[label("this game instance name")]
    pub at: SourceSpan,

    pub game_instance_name: String,

    pub model_left_game_instance_name: String,
    pub model_right_game_instance_name: String,
}

#[derive(Debug, Diagnostic, Error)]
#[error("Can't infer type of `None`. Use `None as <type>` to construct a `None` of type `Maybe(<type>)`")]
#[diagnostic(code(domino::code::untyped_none_type_inference))]
pub struct UntypedNoneTypeInferenceError {
    #[source_code]
    pub source_code: miette::NamedSource<String>,

    #[label("this None")]
    pub at: SourceSpan,
}

#[derive(Debug, Diagnostic, Error)]
#[error("Expected an expression identifier, got oracle identifier {oracle_name}`")]
#[diagnostic(code(domino::code::expected_expression_identifier))]
pub struct ExpectedExpressionIdentifierError {
    #[source_code]
    pub source_code: miette::NamedSource<String>,

    #[label("this identifier is an oracle, not an expression")]
    pub at: SourceSpan,

    pub oracle_name: String,
}

#[derive(Debug, Diagnostic, Error)]
#[error("The package instances {assumption_pkg_inst_name} and {construction_pkg_inst_name} in a reduction mapping have different package types")]
#[diagnostic(code(domino::code::theorem::reduction::mapping::package_mismatch))]
pub struct AssumptionMappingContainsDifferentPackagesError {
    #[source_code]
    pub source_code: miette::NamedSource<String>,

    #[label("this package instance is a {assumption_pkg_name}")]
    pub at_assumption: SourceSpan,
    #[label("this package instance is a {construction_pkg_name}")]
    pub at_construction: SourceSpan,

    pub assumption_pkg_inst_name: String,
    pub construction_pkg_inst_name: String,
    pub assumption_pkg_name: String,
    pub construction_pkg_name: String,
}

#[derive(Debug, Diagnostic, Error)]
#[error("The package instances {assumption_pkg_inst_name} and {construction_pkg_inst_name} in a reduction mapping have different parameter assignments for {param_names}")]
#[diagnostic(code(domino::code::theorem::reduction::mapping::package_mismatch))]
pub struct AssumptionMappingParameterMismatchError {
    #[source_code]
    pub source_code: miette::NamedSource<String>,

    #[label("this package instance")]
    pub at_assumption: SourceSpan,
    #[label("and that package instance")]
    pub at_construction: SourceSpan,

    pub assumption_pkg_inst_name: String,
    pub construction_pkg_inst_name: String,

    pub param_names: String,
}

#[derive(Debug, Diagnostic, Error)]
#[error("The package instances {left_pkg_inst_name} and {right_pkg_inst_name} in a reduction have different package types: {left_pkg_name} != {right_pkg_name}")]
#[diagnostic(code(domino::code::theorem::reduction::mapping::reduction_package_mismatch))]
pub struct ReductionContainsDifferentPackagesError {
    #[source_code]
    pub source_code: miette::NamedSource<String>,

    #[label("in this reduction")]
    pub at_reduction: SourceSpan,

    pub left_pkg_inst_name: String,
    pub right_pkg_inst_name: String,
    pub left_pkg_name: String,
    pub right_pkg_name: String,
}

#[derive(Debug, Diagnostic, Error)]
#[error("The package instances {left_pkg_inst_name} and {right_pkg_inst_name} in a reduction have different parameter assignments for {param_names}")]
#[diagnostic(code(domino::code::theorem::reduction::mapping::reduction_package_mismatch))]
pub struct ReductionPackageInstanceParameterMismatchError {
    #[source_code]
    pub source_code: miette::NamedSource<String>,

    #[label("in this reduction")]
    pub at_reduction: SourceSpan,

    pub left_pkg_inst_name: String,
    pub right_pkg_inst_name: String,

    pub param_names: String,
}

#[derive(Debug, Diagnostic, Error)]
#[error("The package instances {pkg_inst_name_1} and {pkg_inst_name_2} should be the same, but {pkg_inst_name_1} is in the assumption part of {game_name_1}, whereas {pkg_inst_name_2} is in the reduction part of {game_name_2}")]
#[diagnostic(code(
    domino::code::theorem::reduction::mapping::reduction_inconsistent_assumption_boundary
))]
pub struct ReductionInconsistentAssumptionBoundaryError {
    #[source_code]
    pub source_code: miette::NamedSource<String>,

    #[label("in this reduction")]
    pub at_reduction: SourceSpan,

    #[label("mapped here")]
    pub at_mapping_entry: SourceSpan,

    pub pkg_inst_name_1: String,
    pub pkg_inst_name_2: String,

    pub game_name_1: String,
    pub game_name_2: String,
}

#[derive(Debug, Diagnostic, Error)]
#[error("The package instance {pkg_inst_name} was mapped twice")]
#[diagnostic(code(domino::code::theorem::reduction::mapping::duplicate_package_instance))]
pub struct AssumptionMappingDuplicatePackageInstanceError {
    #[source_code]
    pub source_code: miette::NamedSource<String>,

    #[label("now here")]
    pub at_this: SourceSpan,
    #[label("and before here")]
    pub at_prev: SourceSpan,

    pub pkg_inst_name: String,
}

#[derive(Debug, Diagnostic, Error)]
#[error("The package instance {pkg_inst_name} of the assumption game has not been mapped")]
#[diagnostic(code(domino::code::theorem::reduction::mapping::duplicate_package_instance))]
pub struct AssumptionMappingMissesPackageInstanceError {
    #[source_code]
    pub source_code: miette::NamedSource<String>,

    #[label("in this mapping")]
    pub at: SourceSpan,

    pub pkg_inst_name: String,
}

#[derive(Debug, Diagnostic, Error)]
#[error("The edge {pkg_inst_name} exists in game X but not in game Y, yielding an inconsistent reduction")]
#[diagnostic(code(domino::code::theorem::reduction::mapping::duplicate_package_instance))]
pub struct InconsistentReductions {
    #[source_code]
    pub source_code: miette::NamedSource<String>,

    #[label("in this mapping")]
    pub at: SourceSpan,

    pub pkg_inst_name: String,
}

#[derive(Debug, Diagnostic, Error, Clone)]
#[error("The construction package instance `{construction_pkg_inst_name}` has an incoming edge with oracle `{oracle_name}`, but the mapped assumption package instance `{assumption_pkg_inst_name}` doesn't")]
#[diagnostic(code(domino::code::theorem::reduction::mapping::assumption_exports_insufficient))]
pub struct AssumptionExportsNotSufficientError {
    #[source_code]
    pub source_code: miette::NamedSource<String>,

    #[label(
        "in the assumption game, access to the `{oracle_name}` is not exported for this package instance"
    )]
    pub assumption_at: SourceSpan,

    #[label(
        "but in the construction game, oracle `{oracle_name}` can be called on this package instance"
    )]
    pub construction_at: SourceSpan,

    pub assumption_pkg_inst_name: String,
    pub construction_pkg_inst_name: String,

    pub oracle_name: String,
}

#[derive(Error, Diagnostic, Debug)]
#[error("package instance {pkg_inst_name} of package type {pkg_name} imports oracle {oracle_name}, but no such edge exists in composition")]
#[diagnostic(code(domino::code::game::missing_edge))]
pub struct MissingEdgeForImportedOracleError {
    #[source_code]
    pub source_code: miette::NamedSource<String>,

    // this should be the package instance definition
    #[label("missing edge to oracle {oracle_name} for package instance {pkg_inst_name}")]
    pub at: SourceSpan,

    pub pkg_inst_name: String,
    pub pkg_name: String,
    pub oracle_name: String,
}

#[derive(Error, Diagnostic, Debug)]
#[error("game {game_name} assigns an edge from package instance {pkg_inst_name} of package type {pkg_name} for oracle {oracle_name}, but that package doesn't import that oracle")]
#[diagnostic(code(domino::code::game::unused_edge))]
pub struct UnusedEdgeError {
    #[source_code]
    pub source_code: miette::NamedSource<String>,

    // this should be the package instance definition
    #[label("oracle {oracle_name} not imported by package instance {pkg_inst_name}")]
    pub at: SourceSpan,

    pub pkg_inst_name: String,
    pub pkg_name: String,
    pub oracle_name: String,
    pub game_name: String,
}

#[derive(Error, Diagnostic, Debug)]
#[error("game {game_name} exports oracle {oracle_name} multiple times")]
#[diagnostic(code(domino::code::game::unused_edge))]
pub struct DuplicateExportError {
    #[source_code]
    pub source_code: miette::NamedSource<String>,

    // this should be the package instance definition
    #[label("oracle {oracle_name} re-exported here")]
    pub at: SourceSpan,

    pub oracle_name: String,
    pub game_name: String,
}

#[derive(Error, Diagnostic, Debug)]
#[error("oracle {oracle_name} wired to incompatible oracle signature")]
#[diagnostic(code(domino::code::game::unused_edge))]
pub struct OracleSigMismatchError {
    #[source_code]
    pub source_code: miette::NamedSource<String>,

    // this should be the package instance definition
    #[label("signature of oracle {oracle_name} imported by {src_pkg_inst_name} does not match the one exposed by {dst_pkg_inst_name}")]
    pub at: SourceSpan,

    pub oracle_name: String,
    pub src_pkg_inst_name: String,
    pub dst_pkg_inst_name: String,
}

#[derive(Error, Diagnostic, Debug)]
#[error("game {game_name} assigns an edge from package instance {pkg_inst_name} for oracle {oracle_name} twice")]
#[diagnostic(code(domino::code::game::unused_edge))]
pub struct DuplicateEdgeDefinitionError {
    #[source_code]
    pub source_code: miette::NamedSource<String>,

    // this should be the package instance definition
    #[label("this edge has been defined before")]
    pub at: SourceSpan,

    pub pkg_inst_name: String,
    pub oracle_name: String,
    pub game_name: String,
}

#[derive(Error, Debug, miette::Diagnostic)]
#[error("Error parsing '{num_str}' as a number: {source}")]
#[diagnostic(code(domino::code::number_parse))]
pub struct ParseNumberError {
    #[source_code]
    pub source_code: miette::NamedSource<String>,

    #[label("this number could not be parsed")]
    pub at: SourceSpan,

    pub num_str: String,

    #[source]
    pub source: <u64 as std::str::FromStr>::Err,
}

#[derive(miette::Diagnostic, Debug, thiserror::Error)]
#[error("Reduction references construction game instance {name}, but that is not in the header")]
pub struct InvalidGameInstanceInReductionError {
    #[source_code]
    pub source_code: miette::NamedSource<String>,

    #[label("this is not in the header of the reduction")]
    pub span: miette::SourceSpan,

    #[label("this is not in the header of the reduction")]
    pub header_span: miette::SourceSpan,

    pub name: String,
}

impl InvalidGameInstanceInReductionError {
    pub(crate) fn new(
        source: miette::NamedSource<String>,
        name: &crate::parser::ast::GameInstanceName,
        header_span: impl Into<miette::SourceSpan>,
    ) -> Self {
        let name_start = name.as_span().start();
        let name_end = name.as_span().end();
        let span = (name_start..name_end).into();

        Self {
            source_code: source,
            span,
            header_span: header_span.into(),
            name: name.as_str().to_string(),
        }
    }
}

#[derive(miette::Diagnostic, Debug, thiserror::Error)]
#[error("Wrong number of argument when invoking {oracle_name}, oracle has {expected_num} arguments, but invocation has {got_num}")]
pub struct WrongArgumentCountInInvocationError {
    #[source_code]
    pub source_code: miette::NamedSource<String>,

    #[label("this invocation has the wrong number of arguments")]
    pub span: miette::SourceSpan,

    pub oracle_name: String,

    pub expected_num: usize,

    pub got_num: usize,
}
