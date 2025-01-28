//! Errors to do with handling files.

use std::path::PathBuf;

use thiserror::Error;

/// The result type for dealing with file-related errors.
pub type Result<T> = std::result::Result<T, Error>;

/// Errors for handling files when interacting with the Noir compiler driver.
#[derive(Debug, Error)]
pub enum Error {
    #[error("Could not read file at {_0:?}")]
    MissingFile(PathBuf),

    #[error("Could not write to file at {_0:?}")]
    WritingError(PathBuf),

    #[error("File at {_0:?} already exists in the project")]
    DuplicateFile(PathBuf),

    #[error("Noir Error: {_0}")]
    Other(String),
}
