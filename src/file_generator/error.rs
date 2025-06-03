use std::{fmt, io};

use thiserror::Error;

use crate::{file_generator::lean, noir};

/// The result type for dealing with file generation related errors.
pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, Error)]
pub enum Error {
    #[error("IO Error: {_0}")]
    IOError(#[from] io::Error),

    #[error("Formatting Error: {_0}")]
    FmtError(#[from] fmt::Error),

    #[error("Noir Error: {_0}")]
    Noir(#[from] noir::error::Error),

    #[error("Error generating require block for Lake: {_0}")]
    LakeRequireGeneration(String),

    #[error("Error deserializing toml file: {_0}")]
    TomlDeserializationError(#[from] toml::de::Error),

    #[error(transparent)]
    LeanError(#[from] lean::error::Error),
}
