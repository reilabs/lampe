//! A representation of an unparsed Noir source.

use std::{fs::File, io::Read, path::PathBuf};

use crate::noir::error::file::{Error, Result};

/// An unparsed Noir source file.
#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub struct Source {
    /// The name of the source file.
    pub name: PathBuf,

    /// The contents of the source file.
    pub contents: String,
}

impl Source {
    /// Create a new source from a file path and contents.
    pub fn new(path: impl Into<PathBuf>, contents: impl Into<String>) -> Self {
        let name = path.into();
        let contents = contents.into();

        Self { name, contents }
    }

    /// Creates a new source file by reading the file at the specified path to
    /// get the contents of the file.
    ///
    /// # Errors
    ///
    /// - [`Error::MissingFile`] if the provided file cannot be read.
    pub fn read(root: impl Into<PathBuf>, relative_path: impl Into<PathBuf>) -> Result<Self> {
        let relative_path = relative_path.into();
        let name = root.into().join(relative_path.clone());
        let mut file = File::open(&name).map_err(|_| Error::MissingFile(name.clone()))?;
        let mut contents = String::new();
        file.read_to_string(&mut contents)
            .map_err(|_| Error::MissingFile(name.clone()))?;

        Ok(Self {
            name: relative_path,
            contents,
        })
    }
}
