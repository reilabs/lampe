use crate::file_generator::lake::dependency::{
    LeanDependency, LeanDependencyPath,
};
use crate::file_generator::{EXTRACTED_MODULE_NAME, Error, LAMPE_GENERATED_COMMENT, NoirPackageIdentifier};
use std::fmt::Write;
use std::fs;
use std::path::Path;
use std::string::ToString;
use serde::Deserialize;

pub mod dependency;

fn default_lean_dependencies() -> Vec<Box<dyn LeanDependency>> {
    vec![
        Box::new(LeanDependencyPath::builder("Lampe").path("./../../../Lampe").build()),
        // TODO: In a real setup, require Lample like this:
        // Box::new(LeanDependencyGit::builder("Lampe")
        //     .git("https://github.com/reilabs/lampe")
        //     .rev("main")
        //     .subdir("Lampe")
        //     .build()),
    ]
}

pub fn generate_lakefile_toml(
    lampe_root_dir: &Path,
    noir_package_identifier: &NoirPackageIdentifier,
    additional_dependencies: &Vec<Box<dyn LeanDependency>>,
    overwrite: bool,
) -> Result<(), Error> {
    let output_file = lampe_root_dir.join("lakefile.toml");
    if output_file.exists() && !overwrite {
        return Ok(());
    }

    let mut result = String::new();
    writeln!(result, "# {LAMPE_GENERATED_COMMENT}")?;
    writeln!(result, "name = \"{}-{}\"", noir_package_identifier.name, noir_package_identifier.version)?;
    writeln!(result, "version = \"{}\"", noir_package_identifier.version)?;
    writeln!(result, "defaultTargets = [\"{}\"]", noir_package_identifier.name)?;
    result.push('\n');
    result.push_str("[[lean_lib]]\n");
    writeln!(result, "name = \"{}\"", noir_package_identifier.name)?;
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


#[derive(Deserialize)]
struct LakefileConfig {
    name: String,
}

pub fn read_package_name(
    lampe_root_dir: &Path,
) -> Result<String, Error> {
    let lakefile_path = lampe_root_dir.join("lakefile.toml");
    let content = fs::read_to_string(lakefile_path)?;

    let config: LakefileConfig = toml::from_str(&content)?;

    Ok(config.name)
}
