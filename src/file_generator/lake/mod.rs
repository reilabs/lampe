use crate::file_generator::lake::dependency::{LeanDependency, LeanDependencyPath};
use crate::file_generator::{Error, LAMPE_GENERATED_COMMENT};
use nargo::package::Package;
use std::fmt::Write;
use std::fs;
use std::path::Path;
use std::string::ToString;

mod dependency;

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
    package: &Package,
    overwrite: bool,
) -> Result<(), Error> {
    let output_file = lampe_root_dir.join("lakefile.toml");
    if output_file.exists() && !overwrite {
        return Ok(());
    }

    let name = &package.name.to_string();
    let version = &package.version.clone().unwrap_or("0.0.0".to_string());

    let mut result = String::new();
    writeln!(result, "# {LAMPE_GENERATED_COMMENT}")?;
    writeln!(result, "name = \"{name}\"")?;
    writeln!(result, "version = \"{version}\"")?;
    writeln!(result, "defaultTargets = [\"{name}\"]")?;
    result.push('\n');
    result.push_str("[[lean_lib]]\n");
    writeln!(result, "name = \"{name}\"")?;
    result.push('\n');

    for dependency in default_lean_dependencies() {
        result.push_str(&dependency.generate()?);
        result.push('\n');
    }

    fs::write(output_file, result)?;

    Ok(())
}
