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

pub trait LeanDependency {
    /// Generates the lean dependency.
    ///
    /// # Errors
    ///
    /// - If the dependency cannot be generated.
    fn generate(&self) -> Result<String, fmt::Error>;
}
