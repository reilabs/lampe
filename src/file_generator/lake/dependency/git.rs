use crate::file_generator::lake::dependency::LeanDependency;
use std::fmt;
use std::fmt::Write;

#[derive(Debug, Clone)]
pub struct LeanDependencyGit {
    name: String,
    git: Option<String>,
    rev: Option<String>,
    sub_dir: Option<String>,
}

pub struct LeanDependencyGitBuilder {
    dependency: LeanDependencyGit,
}

#[allow(dead_code)]
impl LeanDependencyGitBuilder {
    fn new(name: &str) -> Self {
        Self {
            dependency: LeanDependencyGit {
                name: name.to_string(),
                git: None,
                rev: None,
                sub_dir: None,
            },
        }
    }

    pub fn git(mut self, git: &str) -> Self {
        self.dependency.git = Some(git.to_string());
        self
    }

    pub fn rev(mut self, rev: &str) -> Self {
        self.dependency.rev = Some(rev.to_string());
        self
    }

    pub fn subdir(mut self, subdir: &str) -> Self {
        self.dependency.sub_dir = Some(subdir.to_string());
        self
    }

    pub fn build(self) -> LeanDependencyGit {
        self.dependency
    }
}

#[allow(dead_code)]
impl LeanDependencyGit {
    pub fn builder(name: &str) -> LeanDependencyGitBuilder {
        LeanDependencyGitBuilder::new(name)
    }
}

impl LeanDependency for LeanDependencyGit {
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
        if let Some(subdir) = &self.sub_dir {
            writeln!(result, "subDir = \"{subdir}\"")?;
        }

        Ok(result)
    }
}
