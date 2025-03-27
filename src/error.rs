use crate::Error::{FileError, FileGenerationError, NoirProjectError};
use crate::error::Error::{CompilationError, EmitError};
use crate::{file_generator, noir};
use std::fmt::Display;

pub enum Error {
    CompilationError(noir::error::compilation::Error),
    EmitError(noir::error::emit::Error),
    FileError(noir::error::file::Error),
    FileGenerationError(file_generator::error::Error),
    NoirProjectError(nargo_toml::ManifestError),
}

impl From<noir::error::compilation::Error> for Error {
    fn from(error: noir::error::compilation::Error) -> Self {
        CompilationError(error)
    }
}

impl From<noir::error::emit::Error> for Error {
    fn from(error: noir::error::emit::Error) -> Self {
        EmitError(error)
    }
}

impl From<noir::error::file::Error> for Error {
    fn from(error: crate::noir_error::file::Error) -> Self {
        FileError(error)
    }
}

impl From<file_generator::error::Error> for Error {
    fn from(error: file_generator::error::Error) -> Self {
        FileGenerationError(error)
    }
}

impl From<nargo_toml::ManifestError> for Error {
    fn from(error: nargo_toml::ManifestError) -> Self {
        NoirProjectError(error)
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CompilationError(e) => e.fmt(f),
            EmitError(e) => e.fmt(f),
            FileError(e) => e.fmt(f),
            FileGenerationError(e) => e.fmt(f),
            NoirProjectError(e) => e.fmt(f),
        }
    }
}
