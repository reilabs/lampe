use std::{fmt, fmt::Write};

use crate::file_generator::lake::dependency::LeanDependency;

/// This is Lean's dependency from Reservoir (Lean's package manager) with git
/// rev.
#[derive(Debug, Clone)]
pub struct LeanDependencyReservoirGit {
    name:  String,
    scope: Option<String>,
    rev:   Option<String>,
}

pub struct LeanDependencyReservoirGitBuilder {
    dependency: LeanDependencyReservoirGit,
}

#[allow(dead_code)]
impl LeanDependencyReservoirGitBuilder {
    #[must_use]
    fn new(name: &str) -> Self {
        Self {
            dependency: LeanDependencyReservoirGit {
                name:  name.to_string(),
                scope: None,
                rev:   None,
            },
        }
    }

    #[must_use]
    pub fn scope(mut self, scope: &str) -> Self {
        self.dependency.scope = Some(scope.to_string());
        self
    }

    #[must_use]
    pub fn rev(mut self, rev: &str) -> Self {
        self.dependency.rev = Some(rev.to_string());
        self
    }

    #[must_use]
    pub fn build(self) -> LeanDependencyReservoirGit {
        self.dependency
    }
}

#[allow(dead_code)]
impl LeanDependencyReservoirGit {
    #[must_use]
    pub fn builder(name: &str) -> LeanDependencyReservoirGitBuilder {
        LeanDependencyReservoirGitBuilder::new(name)
    }
}

impl LeanDependency for LeanDependencyReservoirGit {
    /// Generates the lean dependency.
    ///
    /// # Errors
    ///
    /// - If the dependency cannot be generated.
    fn generate(&self) -> Result<String, fmt::Error> {
        let mut result = String::new();
        result.push_str("[[require]]\n");
        let name = &self.name;
        writeln!(result, "name = \"{name}\"")?;
        if let Some(scope) = &self.scope {
            writeln!(result, "scope = \"{scope}\"")?;
        }
        if let Some(rev) = &self.rev {
            writeln!(result, "rev = \"{rev}\"")?;
        }

        Ok(result)
    }

    fn name(&self) -> &str {
        &self.name
    }
}
