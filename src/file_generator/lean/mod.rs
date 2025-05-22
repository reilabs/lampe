//! This module contains functionality for generating lean files with specified configuration, like:
//! imports, namespaces, etc.

use crate::file_generator::{
    DEPENDENCIES_MODULE_NAME, EXTRACTED_MODULE_NAME, Error, LAMPE_GENERATED_COMMENT, LeanFile,
    NoirPackageIdentifier,
};
use itertools::Itertools;
use std::collections::HashMap;
use std::fmt::Write;
use std::fs;
use std::path::Path;

pub mod error;
pub mod file;

/// Generates all lean files from passed extracted code with project configuration.
/// Current lean files structure is (in pseudo description):
/// |--Main package
/// |  |--Extracted
/// |  |  |--Dependencies
/// |  |  |  |-- Each dependency in own module
/// |  |  |--Noir extracted code matching file paths as created by user in Noir project
pub fn generate_lean_files(
    lampe_root_dir: &Path,
    noir_package_identifier: &NoirPackageIdentifier,
    extracted_code: &[LeanFile],
    extracted_dependencies: HashMap<NoirPackageIdentifier, Vec<LeanFile>>,
) -> Result<(), Error> {
    generate_lib_file(lampe_root_dir, noir_package_identifier, false)?;

    let lib_dir = lampe_root_dir.join(format!(
        "{}-{}",
        &noir_package_identifier.name, &noir_package_identifier.version
    ));
    if !lib_dir.exists() {
        fs::create_dir(&lib_dir)?;
    }

    generate_extracted_file(
        &lib_dir,
        noir_package_identifier,
        &extracted_dependencies
            .keys()
            .cloned()
            .collect::<Vec<NoirPackageIdentifier>>(),
        true,
    )?;

    let extracted_lib_dir = lib_dir.join(EXTRACTED_MODULE_NAME);
    if !extracted_lib_dir.exists() {
        fs::create_dir(&extracted_lib_dir)?;
    }

    generate_extracted_module_version_file(
        &extracted_lib_dir,
        noir_package_identifier,
        extracted_code,
        true,
    )?;

    generate_extracted_module_version_extracted_files(
        &extracted_lib_dir,
        noir_package_identifier,
        extracted_code,
        true,
    )?;

    if !extracted_dependencies.is_empty() {
        let extracted_dep_lib_dir = extracted_lib_dir.join(DEPENDENCIES_MODULE_NAME);
        if !extracted_dep_lib_dir.exists() {
            fs::create_dir(&extracted_dep_lib_dir)?;
        }

        for (extracted_dependency, lean_files) in extracted_dependencies {
            generate_extracted_dep_module_version_file(
                &extracted_dep_lib_dir,
                noir_package_identifier,
                &extracted_dependency,
                &lean_files,
                true,
            )?;

            generate_extracted_dep_module_version_extracted_files(
                &extracted_dep_lib_dir,
                noir_package_identifier,
                &extracted_dependency,
                &lean_files,
                true,
            )?;
        }
    }

    Ok(())
}

/// Generates Lean's entrypoint file ready for user's code.
fn generate_lib_file(
    lampe_root_dir: &Path,
    noir_package_identifier: &NoirPackageIdentifier,
    overwrite: bool,
) -> Result<(), Error> {
    let output_file = lampe_root_dir.join(format!(
        "{}-{}.lean",
        &noir_package_identifier.name, &noir_package_identifier.version
    ));
    if output_file.exists() && !overwrite {
        return Ok(());
    }

    let mut result = String::new();

    writeln!(result, "-- {LAMPE_GENERATED_COMMENT}")?;
    writeln!(result)?;
    writeln!(
        result,
        "import «{}-{}».{}",
        &noir_package_identifier.name, &noir_package_identifier.version, EXTRACTED_MODULE_NAME
    )?;
    writeln!(result)?;
    writeln!(
        result,
        "namespace «{}-{}»",
        &noir_package_identifier.name, &noir_package_identifier.version
    )?;
    writeln!(result)?;
    writeln!(result, "open Lampe")?;

    fs::write(output_file, result)?;

    Ok(())
}

/// Generates extracted module file that groups all imports of extracted and generated code
/// for simple usage.
fn generate_extracted_file(
    lib_dir: &Path,
    noir_package_identifier: &NoirPackageIdentifier,
    extracted_modules: &[NoirPackageIdentifier],
    overwrite: bool,
) -> Result<(), Error> {
    let output_file = lib_dir.join(format!("{EXTRACTED_MODULE_NAME}.lean"));
    if output_file.exists() && !overwrite {
        return Ok(());
    }

    if let Some(parent_dir) = output_file.parent() {
        fs::create_dir_all(parent_dir)?;
    }

    let mut result = String::new();

    writeln!(result, "-- {LAMPE_GENERATED_COMMENT}")?;
    writeln!(result)?;
    writeln!(
        result,
        "import «{}-{}».{}.«{}-{}»",
        &noir_package_identifier.name,
        &noir_package_identifier.version,
        EXTRACTED_MODULE_NAME,
        &noir_package_identifier.name,
        &noir_package_identifier.version,
    )?;
    for extracted_module in extracted_modules.iter().sorted() {
        writeln!(
            result,
            "import «{}-{}».{}.{}.«{}-{}»",
            &noir_package_identifier.name,
            &noir_package_identifier.version,
            EXTRACTED_MODULE_NAME,
            DEPENDENCIES_MODULE_NAME,
            &extracted_module.name,
            &extracted_module.version,
        )?;
    }

    fs::write(output_file, result)?;

    Ok(())
}

/// Generates main extracted project Lean's module file that is used later to import everything
/// easily.
fn generate_extracted_module_version_file(
    extracted_lib_dir: &Path,
    noir_package_identifier: &NoirPackageIdentifier,
    extracted_code: &[LeanFile],
    overwrite: bool,
) -> Result<(), Error> {
    let output_file = extracted_lib_dir.join(format!(
        "{}-{}.lean",
        &noir_package_identifier.name, &noir_package_identifier.version
    ));
    if output_file.exists() && !overwrite {
        return Ok(());
    }

    let mut result = String::new();

    writeln!(result, "-- {LAMPE_GENERATED_COMMENT}")?;
    writeln!(result)?;
    for import in extracted_code
        .iter()
        .map(|file| file.file_path.to_lean_import())
        .sorted()
    {
        writeln!(
            result,
            "import «{}-{}».{}.{}",
            &noir_package_identifier.name,
            &noir_package_identifier.version,
            EXTRACTED_MODULE_NAME,
            import
        )?;
    }
    writeln!(result)?;
    writeln!(
        result,
        "namespace «{}-{}»",
        &noir_package_identifier.name, &noir_package_identifier.version
    )?;
    writeln!(result, "namespace {EXTRACTED_MODULE_NAME}")?;
    writeln!(result)?;

    if !extracted_code.is_empty() {
        write!(result, "def env := ")?;
        let env = extracted_code
            .iter()
            .filter(|file| !file.is_generated_types())
            .map(|file| file.file_path.to_lean_import())
            .sorted()
            .map(|import| {
                format!(
                    "«{}-{}».{}.{}.env",
                    &noir_package_identifier.name,
                    &noir_package_identifier.version,
                    EXTRACTED_MODULE_NAME,
                    import,
                )
            })
            .join("\n  ++ ");
        result.push_str(&env);
    }
    writeln!(result)?;

    fs::write(output_file, result)?;

    Ok(())
}

/// Generates main extracted project's lean files using code generated by Lampe based on Noir's project. It keeps original
/// names and relative path from Noir's project changing naming to CamelCase.
fn generate_extracted_module_version_extracted_files(
    extracted_module_dir: &Path,
    noir_package_identifier: &NoirPackageIdentifier,
    extracted_code: &[LeanFile],
    overwrite: bool,
) -> Result<(), Error> {
    for lean_file in extracted_code {
        generate_extracted_module_version_extracted_file(
            extracted_module_dir,
            noir_package_identifier,
            lean_file,
            overwrite,
        )?;
    }

    Ok(())
}

/// Generates single main extracted project Lean's file out from passed generated code.
fn generate_extracted_module_version_extracted_file(
    extracted_module_dir: &Path,
    noir_package_identifier: &NoirPackageIdentifier,
    extracted_code: &LeanFile,
    overwrite: bool,
) -> Result<(), Error> {
    let output_file = extracted_module_dir.join(extracted_code.file_path.to_lean_path());
    if output_file.exists() && !overwrite {
        return Ok(());
    }

    if let Some(output_file_dir) = output_file.parent() {
        fs::create_dir_all(output_file_dir)?;
    }

    let mut result = String::new();

    writeln!(result, "-- {LAMPE_GENERATED_COMMENT}")?;
    writeln!(result)?;

    if !extracted_code.is_generated_types() {
        writeln!(
            result,
            "import «{}-{}».{}.GeneratedTypes",
            &noir_package_identifier.name, &noir_package_identifier.version, EXTRACTED_MODULE_NAME,
        )?;
    }

    writeln!(result, "import Lampe")?;
    writeln!(result)?;
    writeln!(result, "open Lampe")?;
    writeln!(result)?;
    writeln!(
        result,
        "namespace «{}-{}»",
        &noir_package_identifier.name, &noir_package_identifier.version
    )?;
    writeln!(result, "namespace {EXTRACTED_MODULE_NAME}")?;
    writeln!(result)?;
    result.push_str(&extracted_code.content);

    fs::write(output_file, result)?;

    Ok(())
}

/// Generates extracted dependency's Lean's module file that is used later to import everything
/// easily.
fn generate_extracted_dep_module_version_file(
    extracted_dep_module_dir: &Path,
    noir_package_identifier: &NoirPackageIdentifier,
    extracted_module: &NoirPackageIdentifier,
    extracted_code: &[LeanFile],
    overwrite: bool,
) -> Result<(), Error> {
    let output_file = extracted_dep_module_dir.join(format!(
        "{}-{}.lean",
        &extracted_module.name, &extracted_module.version
    ));
    if output_file.exists() && !overwrite {
        return Ok(());
    }

    let mut result = String::new();

    writeln!(result, "-- {LAMPE_GENERATED_COMMENT}")?;
    writeln!(result)?;
    for import in extracted_code
        .iter()
        .map(|file| file.file_path.to_lean_import())
        .sorted()
    {
        writeln!(
            result,
            "import «{}-{}».{}.{}.«{}-{}».{}",
            &noir_package_identifier.name,
            &noir_package_identifier.version,
            EXTRACTED_MODULE_NAME,
            DEPENDENCIES_MODULE_NAME,
            &extracted_module.name,
            &extracted_module.version,
            import
        )?;
    }
    writeln!(result)?;
    writeln!(
        result,
        "namespace «{}-{}»",
        &noir_package_identifier.name, &noir_package_identifier.version
    )?;
    writeln!(result, "namespace {EXTRACTED_MODULE_NAME}")?;
    writeln!(result, "namespace {DEPENDENCIES_MODULE_NAME}")?;
    writeln!(
        result,
        "namespace «{}-{}»",
        &extracted_module.name, &extracted_module.version
    )?;
    writeln!(result)?;

    if !extracted_code.is_empty() {
        write!(result, "def env := ")?;
        let env = extracted_code
            .iter()
            .filter(|file| !file.is_generated_types())
            .map(|file| file.file_path.to_lean_import())
            .sorted()
            .map(|import| {
                format!(
                    "«{}-{}».{}.{}.«{}-{}».{}.env",
                    &noir_package_identifier.name,
                    &noir_package_identifier.version,
                    EXTRACTED_MODULE_NAME,
                    DEPENDENCIES_MODULE_NAME,
                    &extracted_module.name,
                    &extracted_module.version,
                    import,
                )
            })
            .join("\n  ++ ");
        result.push_str(&env);
    }
    writeln!(result)?;

    fs::write(output_file, result)?;

    Ok(())
}

/// Generates extracted dependency's lean files using code generated by Lampe based on Noir's project. It keeps original
/// names and relative path from Noir's project changing naming to CamelCase.
fn generate_extracted_dep_module_version_extracted_files(
    extracted_dep_module_dir: &Path,
    noir_package_identifier: &NoirPackageIdentifier,
    extracted_module: &NoirPackageIdentifier,
    extracted_code: &Vec<LeanFile>,
    overwrite: bool,
) -> Result<(), Error> {
    let extracted_dep_module_dir = extracted_dep_module_dir.join(format!(
        "{}-{}",
        &extracted_module.name, &extracted_module.version
    ));
    if !extracted_dep_module_dir.exists() {
        fs::create_dir(&extracted_dep_module_dir)?;
    }

    for lean_file in extracted_code {
        generate_extracted_dep_module_version_extracted_file(
            &extracted_dep_module_dir,
            noir_package_identifier,
            extracted_module,
            lean_file,
            overwrite,
        )?;
    }

    Ok(())
}

/// Generates single extracted dependency's lean file out from passed generated code.
fn generate_extracted_dep_module_version_extracted_file(
    extracted_dep_module_dir: &Path,
    noir_package_identifier: &NoirPackageIdentifier,
    extracted_module: &NoirPackageIdentifier,
    extracted_code: &LeanFile,
    overwrite: bool,
) -> Result<(), Error> {
    let output_file = extracted_dep_module_dir.join(extracted_code.file_path.to_lean_path());
    if output_file.exists() && !overwrite {
        return Ok(());
    }

    if let Some(output_file_dir) = output_file.parent() {
        fs::create_dir_all(output_file_dir)?;
    }

    let mut result = String::new();

    writeln!(result, "-- {LAMPE_GENERATED_COMMENT}")?;
    writeln!(result)?;

    if !extracted_code.is_generated_types() {
        writeln!(
            result,
            "import «{}-{}».{}.{}.«{}-{}».GeneratedTypes",
            &noir_package_identifier.name,
            &noir_package_identifier.version,
            EXTRACTED_MODULE_NAME,
            DEPENDENCIES_MODULE_NAME,
            &extracted_module.name,
            &extracted_module.version,
        )?;
    }

    writeln!(result, "import Lampe")?;
    writeln!(result)?;
    writeln!(result, "open Lampe")?;
    writeln!(result)?;
    writeln!(
        result,
        "namespace «{}-{}»",
        &noir_package_identifier.name, &noir_package_identifier.version
    )?;
    writeln!(result, "namespace {EXTRACTED_MODULE_NAME}")?;
    writeln!(result, "namespace {DEPENDENCIES_MODULE_NAME}")?;
    writeln!(
        result,
        "namespace «{}-{}»",
        &extracted_module.name, &extracted_module.version
    )?;
    writeln!(result)?;
    result.push_str(&extracted_code.content);

    fs::write(output_file, result)?;

    Ok(())
}
