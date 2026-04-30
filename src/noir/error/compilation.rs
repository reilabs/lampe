//! Errors to do with compilation of Noir.

use noirc_driver::ErrorsAndWarnings;
use noirc_errors::reporter::ReportedErrors;
use thiserror::Error;

/// The result type for dealing with compilation-related errors.
pub type Result<T> = std::result::Result<T, Error>;

/// Errors for compilation of Noir source code.
#[derive(Debug, Error)]
pub enum Error {
    #[error("Could not successfully check crate:\n{diagnostics:?}")]
    CheckFailure { diagnostics: ErrorsAndWarnings },

    #[error("Could not successfully compile crate; reported {} errors", _0.error_count)]
    Reported(ReportedErrors),

    #[error("Noir Error: {_0}")]
    Other(String),
}

impl From<ErrorsAndWarnings> for Error {
    fn from(diagnostics: ErrorsAndWarnings) -> Self {
        Error::CheckFailure { diagnostics }
    }
}
