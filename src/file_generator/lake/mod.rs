//! This module contains functionality for generating lake's (lean's project
//! manager).

use std::{fmt::Write, fs, path::Path};

use itertools::Itertools;
use serde::Deserialize;

use crate::{
    file_generator::{
        lake::dependency::{LeanDependency, LeanDependencyGit},
        Error,
        NoirPackageIdentifier,
        LAMPE_GENERATED_COMMENT,
    },
    lean::{LEAN_QUOTE_END, LEAN_QUOTE_START},
};

pub mod constants;
pub mod dependency;

/// This is list of dependencies added by default to all Lampe's projects.
///
/// If `stdlib_info` is provided the project is assumed not to be the standard
/// library, and the bundled standard library is added.
fn default_lean_dependencies(
    stdlib_info: Option<NoirPackageIdentifier>,
) -> Vec<Box<dyn LeanDependency>> {
    let mut deps: Vec<Box<dyn LeanDependency>> = vec![Box::new(
        LeanDependencyGit::builder("Lampe")
            .git("https://github.com/reilabs/lampe")
            .rev("main")
            .subdir("Lampe")
            .build(),
    )];

    // We include the standard library for any project that is _not_ the standard
    // library.
    if let Some(info) = stdlib_info {
        let dep_name = format!("{}-{}", info.name, info.version);
        deps.push(Box::new(
            LeanDependencyGit::builder(&dep_name)
                .git("https://github.com/reilabs/lampe")
                .rev("main")
                .subdir("stdlib/lampe")
                .build(),
        ));
    }

    deps
}

/// Generates main lake file.
/// Path: $(project)/lampe/lakefile.toml
///
/// # Errors
///
/// - If the lakefile cannot be generated properly.
pub fn generate_lakefile_toml(
    lampe_root_dir: &Path,
    stdlib_info: Option<NoirPackageIdentifier>,
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
        "name = \"{}{}-{}{}\"",
        LEAN_QUOTE_START,
        noir_package_identifier.name,
        noir_package_identifier.version,
        LEAN_QUOTE_END,
    )?;
    result.push('\n');

    for dependency in default_lean_dependencies(stdlib_info) {
        result.push_str(&dependency.generate()?);
        result.push('\n');
    }

    additional_dependencies
        .into_iter()
        .sorted_by_key(|d| d.name())
        .try_for_each(|dependency| -> Result<(), Error> {
            result.push_str(&dependency.generate()?);
            result.push('\n');
            Ok(())
        })?;

    fs::write(output_file, result)?;

    Ok(())
}

/// This struct is used to read lakefile.toml file.
#[derive(Deserialize, Debug)]
struct LakefileConfig {
    name: String,
}

/// Returns name extracted out of Lampe's project's lakefile.toml.
///
/// # Errors
///
/// - If the package name does not point to a valid file.
pub fn read_package_name(lampe_root_dir: &Path) -> Result<String, Error> {
    let lakefile_path = lampe_root_dir.join("lakefile.toml");
    let content = fs::read_to_string(lakefile_path)?;

    let config: LakefileConfig = toml::from_str(&content)?;

    Ok(config.name)
}
