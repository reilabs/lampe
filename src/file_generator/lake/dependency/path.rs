use crate::file_generator::lake::dependency::LeanDependency;
use std::fmt;
use std::fmt::Write;

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
    fn new(name: &str) -> Self {
        Self {
            dependency: LeanDependencyPath {
                name: name.to_string(),
                path: None,
            },
        }
    }

    pub fn path(mut self, path: &str) -> Self {
        self.dependency.path = Some(path.to_string());
        self
    }

    pub fn build(self) -> LeanDependencyPath {
        self.dependency
    }
}

#[allow(dead_code)]
impl LeanDependencyPath {
    pub fn builder(name: &str) -> LeanDependencyPathBuilder {
        LeanDependencyPathBuilder::new(name)
    }
}

impl LeanDependency for LeanDependencyPath {
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
}
