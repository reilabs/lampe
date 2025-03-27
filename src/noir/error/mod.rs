//! The error types for use at the boundary of the library.

pub mod compilation;
pub mod emit;
pub mod file;

use thiserror::Error;

/// The result type for use at the boundary of the library.
pub type Result<T> = std::result::Result<T, Error>;

/// The top-level error type for use at the boundary of the library.
///
/// It provides conversions from the more-specific internal error types to ease
/// usage, while also ensuring a strongly-typed error boundary to enable proper
/// handling.
#[derive(Debug, Error)]
pub enum Error {
    /// Errors in compilation.
    #[error(transparent)]
    Compile(#[from] compilation::Error),

    /// Errors in emission of Lean code.
    #[error(transparent)]
    Emit(#[from] emit::Error),

    /// Errors in file handling.
    #[error(transparent)]
    File(#[from] file::Error),
}
