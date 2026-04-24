//! This module contains lean's dependencies' structs and logic.

use std::fmt;

mod git;
mod path;
mod reservoir;
mod reservoir_git;

#[allow(unused_imports)]
pub use git::LeanDependencyGit;
#[allow(unused_imports)]
pub use path::LeanDependencyPath;
#[allow(unused_imports)]
pub use reservoir::LeanDependencyReservoir;
#[allow(unused_imports)]
pub use reservoir_git::LeanDependencyReservoirGit;

use crate::file_generator::{self, NoirPackageIdentifier};

pub trait LeanDependency {
    /// Generates the lean dependency.
    ///
    /// # Errors
    ///
    /// - If the dependency cannot be generated.
    fn generate(&self) -> Result<String, fmt::Error>;

    /// Returns the versioned name of the dependency in the form
    /// `<name>-<version>`.
    fn name(&self) -> &str;

    /// This is the best effort way to generate a `NoirPackageIdentifier` from a
    /// name assuming everything is extracted as expected by Lampe
    ///
    /// # Errors
    ///
    /// - [`file_generator::Error::LakeRequireGeneration`], if the dependency is
    ///   in an unexpected form.
    fn noir_package_identifier(&self) -> Result<NoirPackageIdentifier, file_generator::Error> {
        let (name, version) =
            self.name()
                .split_once('-')
                .ok_or(file_generator::Error::LakeRequireGeneration(
                    "Lean dependency was in an unexpected form".to_string(),
                ))?;

        Ok(NoirPackageIdentifier {
            name:    name.to_string(),
            version: version.to_string(),
        })
    }
}
