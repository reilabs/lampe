use crate::noir;
use std::{fmt, io};
use thiserror::Error;

/// The result type for dealing with file generation related errors.
pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, Error)]
pub enum Error {
    #[error("IO Error: {_0}")]
    IOError(io::Error),

    #[error("Formatting Error: {_0}")]
    FmtError(fmt::Error),

    #[error("Noir Error: {_0}")]
    Noir(noir::error::Error),
}

impl From<io::Error> for Error {
    fn from(err: io::Error) -> Error {
        Error::IOError(err)
    }
}

impl From<fmt::Error> for Error {
    fn from(err: fmt::Error) -> Error {
        Error::FmtError(err)
    }
}

impl From<noir::error::Error> for Error {
    fn from(err: noir::error::Error) -> Error {
        Error::Noir(err)
    }
}
