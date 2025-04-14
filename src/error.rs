use crate::{file_generator, noir};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum Error {
    #[error(transparent)]
    CompilationError(#[from] noir::error::compilation::Error),
    #[error(transparent)]
    EmitError(#[from] noir::error::emit::Error),
    #[error(transparent)]
    FileError(#[from] noir::error::file::Error),
    #[error(transparent)]
    FileGenerationError(#[from] file_generator::error::Error),
    #[error(transparent)]
    NoirProjectError(#[from] nargo_toml::ManifestError),
    #[error("Package {package_name}:{} is missing dependency {dependency_name} in configuration", .package_version.as_ref().unwrap_or(&"missing".to_string()))]
    MissingDependencyError {
        package_name: String,
        package_version: Option<String>,
        dependency_name: String,
    },
    #[error("Package {package_name}:{} , dependency {dependency_name} - url parsing error {err}", .package_version.as_ref().unwrap_or(&"missing".to_string()))]
    URLParsingError {
        package_name: String,
        package_version: Option<String>,
        dependency_name: String,
        err: String,
    },
}
