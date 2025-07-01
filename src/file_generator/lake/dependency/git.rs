use std::{fmt, fmt::Write};

use crate::file_generator::lake::dependency::LeanDependency;

/// This is Lean's git dependency.
#[derive(Debug, Clone)]
pub struct LeanDependencyGit {
    name:    String,
    git:     Option<String>,
    rev:     Option<String>,
    sub_dir: Option<String>,
}

pub struct LeanDependencyGitBuilder {
    dependency: LeanDependencyGit,
}

#[allow(dead_code)]
impl LeanDependencyGitBuilder {
    #[must_use]
    fn new(name: &str) -> Self {
        Self {
            dependency: LeanDependencyGit {
                name:    name.to_string(),
                git:     None,
                rev:     None,
                sub_dir: None,
            },
        }
    }

    #[must_use]
    pub fn git(mut self, git: &str) -> Self {
        self.dependency.git = Some(git.to_string());
        self
    }

    #[must_use]
    pub fn rev(mut self, rev: &str) -> Self {
        self.dependency.rev = Some(rev.to_string());
        self
    }

    #[must_use]
    pub fn subdir(mut self, subdir: &str) -> Self {
        self.dependency.sub_dir = Some(subdir.to_string());
        self
    }

    #[must_use]
    pub fn build(self) -> LeanDependencyGit {
        self.dependency
    }
}

#[allow(dead_code)]
impl LeanDependencyGit {
    #[must_use]
    pub fn builder(name: &str) -> LeanDependencyGitBuilder {
        LeanDependencyGitBuilder::new(name)
    }
}

impl LeanDependency for LeanDependencyGit {
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
        if let Some(git) = &self.git {
            writeln!(result, "git = \"{git}\"")?;
        }
        if let Some(rev) = &self.rev {
            writeln!(result, "rev = \"{rev}\"")?;
        }
        if let Some(sub_dir) = &self.sub_dir {
            writeln!(result, "subDir = \"{sub_dir}\"")?;
        }

        Ok(result)
    }
}
