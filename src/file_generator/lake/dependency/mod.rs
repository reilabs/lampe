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

use crate::{
    file_generator::{self, NoirPackageIdentifier},
    lean::{LEAN_QUOTE_END, LEAN_QUOTE_START},
};

pub trait LeanDependency {
    /// Generates the lean dependency.
    ///
    /// # Errors
    ///
    /// - If the dependency cannot be generated.
    fn generate(&self) -> Result<String, fmt::Error>;

    fn name(&self) -> &str;

    /// This is the best effort way to generate a NoirPackageIdentifier from a
    /// name assuming everything is extracted as expected by Lampe
    fn noir_package_identifier(&self) -> Result<NoirPackageIdentifier, file_generator::Error> {
        // let stripped_name = self.name().strip_prefix(LEAN_QUOTE_START).ok_or(
        //     file_generator::Error::LakeRequireGeneration(
        //         "Lean dependency was in an unexpected form".to_string(),
        //     ),
        // )?;
        // let stripped_name = stripped_name.strip_suffix(LEAN_QUOTE_END).ok_or(
        //     file_generator::Error::LakeRequireGeneration(
        //         "Lean dependency was in an unexpected form".to_string(),
        //     ),
        // )?;

        let (name, version) =
            self.name()
                .split_once("-")
                .ok_or(file_generator::Error::LakeRequireGeneration(
                    "Lean dependency was in an unexpected form".to_string(),
                ))?;

        Ok(NoirPackageIdentifier {
            name:    name.to_string(),
            version: version.to_string(),
        })
    }
}
