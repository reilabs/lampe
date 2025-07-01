use std::path::{Path, PathBuf};

use convert_case::{Case, Casing};
use itertools::Itertools;

use crate::file_generator::lean::error::{Error::DuplicateWithGeneratedFile, Result};

/// This structure represents relative path of project's file to easily generate
/// imports and file paths.
#[derive(Debug, Eq, Hash, PartialEq)]
pub struct LeanFilePath {
    segments: Vec<String>,
}

impl LeanFilePath {
    #[must_use]
    fn from_noir_path(path: &Path) -> Self {
        let components = path.components().map(|c| c.as_os_str().to_string_lossy().to_string());
        let mut segments: Vec<String> = components
            .skip_while(|c| c != "src")
            .skip(1) // Skip the "src" part itself
            .collect();

        if let Some(last) = segments.last_mut() {
            *last = last.trim_end_matches(".nr").to_owned();
        }

        Self { segments }
    }

    #[must_use]
    fn from_segments<I: IntoIterator<Item = T>, T: Into<String>>(segments: I) -> Self {
        Self {
            segments: segments.into_iter().map(T::into).collect(),
        }
    }

    #[must_use]
    pub fn to_lean_path(&self) -> PathBuf {
        self.segments
            .iter()
            .map(|segment| segment.to_case(Case::Pascal))
            .collect::<PathBuf>()
            .with_extension("lean")
    }

    #[must_use]
    pub fn to_lean_import(&self) -> String {
        self.segments
            .iter()
            .map(|segment| segment.to_case(Case::Pascal))
            .join(".")
    }
}

/// This structure represents lean file content.
type LeanFileContent = String;

/// This structure represents lean file = lean file path + line file content.
#[derive(Debug)]
pub struct LeanFile {
    pub file_path: LeanFilePath,
    pub content:   LeanFileContent,
}

impl LeanFile {
    /// Generates a lean file corresponding to the user's Noir file.
    ///
    /// # Errors
    ///
    /// - If the file cannot be loaded.
    /// - If the file is a duplicate.
    pub fn from_user_noir_file(path: &Path, content: LeanFileContent) -> Result<Self> {
        let file_path = LeanFilePath::from_noir_path(path);

        if file_path == Self::generated_types_file_path() {
            return Err(DuplicateWithGeneratedFile(path.to_path_buf()));
        }

        Ok(LeanFile {
            file_path: LeanFilePath::from_noir_path(path),
            content,
        })
    }

    #[must_use]
    pub fn from_generated_types(content: LeanFileContent) -> Self {
        LeanFile {
            file_path: Self::generated_types_file_path(),
            content,
        }
    }

    #[must_use]
    pub fn is_generated_types(&self) -> bool {
        self.file_path == Self::generated_types_file_path()
    }

    #[must_use]
    fn generated_types_file_path() -> LeanFilePath {
        LeanFilePath::from_segments(["generated_types"])
    }
}

#[must_use]
pub fn to_import_from_noir_path(path: &Path) -> String {
    LeanFilePath::from_noir_path(path).to_lean_import()
}
