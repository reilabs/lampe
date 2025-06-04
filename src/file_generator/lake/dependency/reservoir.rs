use std::{collections::HashMap, fmt, fmt::Write};

use crate::file_generator::lake::dependency::LeanDependency;

/// This is Lean's dependency from Reservoir (Lean's package manager).
#[derive(Debug, Clone)]
pub struct LeanDependencyReservoir {
    name:    String,
    scope:   Option<String>,
    version: Option<String>,
    options: Option<HashMap<String, String>>,
}

pub struct LeanDependencyReservoirBuilder {
    dependency: LeanDependencyReservoir,
}

#[allow(dead_code)]
impl LeanDependencyReservoirBuilder {
    fn new(name: &str) -> Self {
        Self {
            dependency: LeanDependencyReservoir {
                name:    name.to_string(),
                scope:   None,
                version: None,
                options: None,
            },
        }
    }

    pub fn scope(mut self, scope: &str) -> Self {
        self.dependency.scope = Some(scope.to_string());
        self
    }

    pub fn version(mut self, version: &str) -> Self {
        self.dependency.version = Some(version.to_string());
        self
    }

    pub fn options(mut self, options: HashMap<String, String>) -> Self {
        self.dependency.options = Some(options);
        self
    }

    pub fn build(self) -> LeanDependencyReservoir {
        self.dependency
    }
}

#[allow(dead_code)]
impl LeanDependencyReservoir {
    pub fn builder(name: &str) -> LeanDependencyReservoirBuilder {
        LeanDependencyReservoirBuilder::new(name)
    }
}

impl LeanDependency for LeanDependencyReservoir {
    fn generate(&self) -> Result<String, fmt::Error> {
        let mut result = String::new();
        result.push_str("[[require]]\n");
        let name = &self.name;
        writeln!(result, "name = \"{name}\"")?;
        if let Some(scope) = &self.scope {
            writeln!(result, "scope = \"{scope}\"")?;
        }
        if let Some(version) = &self.version {
            writeln!(result, "version = \"{version}\"")?;
        }
        if let Some(options) = &self.options {
            result.push_str("options = {");
            let mut first = true;
            for (k, v) in options {
                if first {
                    first = false;
                } else {
                    result.push_str(", ");
                }
                write!(result, "{k} = \"{v}\"")?;
            }
            result.push_str("}\n");
        }

        Ok(result)
    }
}
