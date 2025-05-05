use std::fmt;

mod git;
mod path;
mod reservoir;
mod reservoir_git;

pub use path::LeanDependencyPath;

pub trait LeanDependency {
    fn generate(&self) -> Result<String, fmt::Error>;
}
