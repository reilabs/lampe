use std::{fmt, fmt::Write};

use crate::file_generator::{lake::dependency::LeanDependency};

/// This is Lean's local dependency.
#[derive(Debug, Clone)]
pub struct LeanDependencyPath {
    name: String,
    path: Option<String>,
}

pub struct LeanDependencyPathBuilder {
    dependency: LeanDependencyPath,
}

#[allow(dead_code)]
impl LeanDependencyPathBuilder {
    #[must_use]
    fn new(name: &str) -> Self {
        Self {
            dependency: LeanDependencyPath {
                name: name.to_string(),
                path: None,
            },
        }
    }

    #[must_use]
    pub fn path(mut self, path: &str) -> Self {
        self.dependency.path = Some(path.to_string());
        self
    }

    #[must_use]
    pub fn build(self) -> LeanDependencyPath {
        self.dependency
    }
}

#[allow(dead_code)]
impl LeanDependencyPath {
    #[must_use]
    pub fn builder(name: &str) -> LeanDependencyPathBuilder {
        LeanDependencyPathBuilder::new(name)
    }
}

impl LeanDependency for LeanDependencyPath {
    /// Generates the Lean dependency.
    ///
    /// # Errors
    ///
    /// - If the dependency cannot be generated.
    fn generate(&self) -> Result<String, fmt::Error> {
        let mut result = String::new();
        result.push_str("[[require]]\n");
        let name = &self.name;
        writeln!(result, "name = \"{name}\"")?;
        if let Some(path) = &self.path {
            writeln!(result, "path = \"{path}\"")?;
        }

        Ok(result)
    }

    fn name(&self) -> &str {
        &self.name
    }
}
