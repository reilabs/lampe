//! Errors from the emit phase of the library.

use thiserror::Error;

/// The result type for dealing with emit-related errors.
pub type Result<T> = std::result::Result<T, Error>;

/// Errors during the emission of Lean from Noir source code.
#[derive(Debug, Error, PartialEq)]
pub enum Error {
    #[error("Could not extract identifier from {_0}")]
    MissingIdentifier(String),

    #[error("Indentation level cannot be decreased below zero")]
    CannotDecreaseIndentLevel,

    #[error("Global is not extracted as a let statement")]
    GlobalStatementNotLet,

    #[error("Unsupported feature {_0}")]
    UnsupportedFeature(String),

    #[error("Unexpected type: type of {_0} must be {_1}")]
    UnexpectedType(String, String),

    // NOTE: This error should not occur, as cycle detection is performed by Noir. We include it
    // anyway just in case.
    #[error("Found cycle in type declarations {_0}")]
    CycleDetected(String),
}
