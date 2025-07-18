//! This module contains functionality for generating lake's (lean's project
//! manager).

use std::{fmt::Write, fs, path::Path};

use serde::Deserialize;

use crate::file_generator::{
    lake::dependency::{LeanDependency, LeanDependencyGit},
    Error,
    NoirPackageIdentifier,
    LAMPE_GENERATED_COMMENT,
};

pub mod dependency;

/// This is list of dependencies added by default to all Lampe's projects.
fn default_lean_dependencies() -> Vec<Box<dyn LeanDependency>> {
    vec![Box::new(
        LeanDependencyGit::builder("Lampe")
            .git("https://github.com/reilabs/lampe")
            .rev("main")
            .subdir("Lampe")
            .build(),
    )]
}

/// Generates main lake file.
/// Path: $(project)/lampe/lakefile.toml
pub fn generate_lakefile_toml(
    lampe_root_dir: &Path,
    noir_package_identifier: &NoirPackageIdentifier,
    additional_dependencies: &[Box<dyn LeanDependency>],
    overwrite: bool,
) -> Result<(), Error> {
    let output_file = lampe_root_dir.join("lakefile.toml");
    if output_file.exists() && !overwrite {
        return Ok(());
    }

    let mut result = String::new();
    writeln!(result, "# {LAMPE_GENERATED_COMMENT}")?;
    writeln!(
        result,
        "name = \"{}-{}\"",
        noir_package_identifier.name, noir_package_identifier.version
    )?;
    writeln!(result, "version = \"{}\"", noir_package_identifier.version)?;
    writeln!(
        result,
        "defaultTargets = [\"{}-{}\"]",
        noir_package_identifier.name, noir_package_identifier.version
    )?;
    result.push('\n');
    result.push_str("[[lean_lib]]\n");
    writeln!(
        result,
        "name = \"«{}-{}»\"",
        noir_package_identifier.name, noir_package_identifier.version
    )?;
    result.push('\n');

    for dependency in default_lean_dependencies() {
        result.push_str(&dependency.generate()?);
        result.push('\n');
    }

    for dependency in additional_dependencies {
        result.push_str(&dependency.generate()?);
        result.push('\n');
    }

    fs::write(output_file, result)?;

    Ok(())
}

/// This struct is used to read lakefile.toml file.
#[derive(Deserialize, Debug)]
struct LakefileConfig {
    name: String,
}

/// Returns name extracted out of Lampe's project's lakefile.toml.
pub fn read_package_name(lampe_root_dir: &Path) -> Result<String, Error> {
    let lakefile_path = lampe_root_dir.join("lakefile.toml");
    let content = fs::read_to_string(lakefile_path)?;

    let config: LakefileConfig = toml::from_str(&content)?;

    Ok(config.name)
}
