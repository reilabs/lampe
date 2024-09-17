//! Errors to do with compilation of Noir.

use noirc_driver::ErrorsAndWarnings;
use thiserror::Error;

/// The result type for dealing with compilation-related errors.
pub type Result<T> = std::result::Result<T, Error>;

/// Errors for compilation of Noir source code.
#[derive(Debug, Error)]
pub enum Error {
    #[error("Could not successfully check crate:\n{diagnostics:?}")]
    CheckFailure { diagnostics: ErrorsAndWarnings },

    #[error("Noir Error: {_0}")]
    Other(String),
}

impl From<ErrorsAndWarnings> for Error {
    fn from(diagnostics: ErrorsAndWarnings) -> Self {
        Error::CheckFailure { diagnostics }
    }
}
