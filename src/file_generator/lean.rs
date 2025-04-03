use crate::file_generator::{EXTRACTED_MODULE_NAME, Error, LAMPE_GENERATED_COMMENT, NoirPackageIdentifier, LeanFile};
use std::collections::HashMap;
use std::fmt::Write;
use std::fs;
use std::path::Path;
use itertools::Itertools;

pub fn generate_lean_files(
    lampe_root_dir: &Path,
    noir_package_identifier: &NoirPackageIdentifier,
    extracted_code: &LeanFile,
    extracted_dependencies: &HashMap<NoirPackageIdentifier, LeanFile>,
) -> Result<(), Error> {
    let lib_dir = lampe_root_dir.join(&noir_package_identifier.name);
    if !lib_dir.exists() {
        fs::create_dir(&lib_dir)?;
    }

    generate_lib_file(lampe_root_dir, noir_package_identifier, false)?;

    let extracted_lib_dir = lib_dir.join(EXTRACTED_MODULE_NAME);
    if !extracted_lib_dir.exists() {
        fs::create_dir(&extracted_lib_dir)?;
    }

    let mut grouped = HashMap::new();
    let grouped_by_name= grouped.entry(noir_package_identifier.name.clone()).or_insert(HashMap::new());
    grouped_by_name.entry(noir_package_identifier.version.clone()).or_insert(extracted_code);
    for (dependency_identifier, lean_file) in extracted_dependencies {
        let grouped_by_name= grouped.entry(dependency_identifier.name.clone()).or_insert(HashMap::new());
        grouped_by_name.entry(dependency_identifier.version.clone()).or_insert(lean_file);
    }

    generate_extracted_file(&lib_dir, &noir_package_identifier, &grouped.keys().map(|v| v.clone()).collect(), true)?;

    for (dependency_name, grouped_by_version) in grouped {
        let extracted_module_dir = extracted_lib_dir.join(&dependency_name);
        if !extracted_module_dir.exists() {
            fs::create_dir(&extracted_module_dir)?;
        }

        generate_extracted_module_file(&extracted_lib_dir, &noir_package_identifier, &dependency_name, &grouped_by_version.keys().map(|v| v.clone()).collect(), true)?;

        for (dependency_version, lean_file) in grouped_by_version {
            generate_extracted_module_version_file(&extracted_module_dir, &noir_package_identifier, &dependency_name, &dependency_version, lean_file, true)?;
        }
    }

    Ok(())
}

fn generate_lib_file(
    lampe_root_dir: &Path,
    noir_package_identifier: &NoirPackageIdentifier,
    overwrite: bool,
) -> Result<(), Error> {
    let output_file = lampe_root_dir.join(format!("{}.lean", &noir_package_identifier.name));
    if output_file.exists() && !overwrite {
        return Ok(());
    }

    let mut result = String::new();

    writeln!(result, "-- {LAMPE_GENERATED_COMMENT}")?;
    writeln!(result, "")?;
    writeln!(result, "import {}.{}", &noir_package_identifier.name, EXTRACTED_MODULE_NAME)?;
    writeln!(result, "")?;
    writeln!(result, "namespace {}", &noir_package_identifier.name)?;
    writeln!(result, "namespace «{}»", &noir_package_identifier.version)?;
    writeln!(result, "")?;
    writeln!(result, "open Lampe")?;

    fs::write(output_file, result)?;

    Ok(())
}

fn generate_extracted_lib_file(
    lib_name: &String,
    lib_dir: &Path,
    imports: &Vec<&String>,
    overwrite: bool,
) -> Result<(), Error> {
    let output_file = lib_dir.join(format!("{EXTRACTED_MODULE_NAME}.lean"));
    if output_file.exists() && !overwrite {
        return Ok(());
    }

    let mut result = String::new();

    write!(result, "-- {LAMPE_GENERATED_COMMENT}\n\n")?;
    for file_name in imports.iter().sorted() {
        writeln!(result, "import {lib_name}.{EXTRACTED_MODULE_NAME}.{file_name}")?;
    }

    fs::write(output_file, result)?;

    Ok(())
}

fn generate_extracted_file(
    lib_dir: &Path,
    noir_package_identifier: &NoirPackageIdentifier,
    extracted_modules: &Vec<String>,
    overwrite: bool,
) -> Result<(), Error> {
    let output_file = lib_dir.join(format!("{}.lean", EXTRACTED_MODULE_NAME));
    if output_file.exists() && !overwrite {
        return Ok(());
    }

    let mut result = String::new();

    writeln!(result, "-- {LAMPE_GENERATED_COMMENT}")?;
    writeln!(result, "")?;
    for extracted_module in extracted_modules.iter().sorted() {
        writeln!(result, "import {}.{}.{}", &noir_package_identifier.name, EXTRACTED_MODULE_NAME, extracted_module)?;
    }

    fs::write(output_file, result)?;

    Ok(())
}

fn generate_extracted_module_file(
    extracted_lib_dir: &Path,
    noir_package_identifier: &NoirPackageIdentifier,
    extracted_module: &String,
    extracted_versions: &Vec<String>,
    overwrite: bool,
) -> Result<(), Error> {
    let output_file = extracted_lib_dir.join(format!("{}.lean", extracted_module));
    if output_file.exists() && !overwrite {
        return Ok(());
    }

    let mut result = String::new();

    writeln!(result, "-- {LAMPE_GENERATED_COMMENT}")?;
    writeln!(result, "")?;
    for extracted_version in extracted_versions.iter().sorted() {
        writeln!(result, "import {}.{}.{}.«{}»", &noir_package_identifier.name, EXTRACTED_MODULE_NAME, extracted_module, extracted_version)?;
    }

    fs::write(output_file, result)?;

    Ok(())
}

fn generate_extracted_module_version_file(
    extracted_module_dir: &Path,
    noir_package_identifier: &NoirPackageIdentifier,
    extracted_module: &String,
    extracted_version: &String,
    extracted_code: &LeanFile,
    overwrite: bool,
) -> Result<(), Error> {
    let output_file = extracted_module_dir.join(format!("{}.lean", extracted_version));
    if output_file.exists() && !overwrite {
        return Ok(());
    }

    let mut result = String::new();

    writeln!(result, "-- {LAMPE_GENERATED_COMMENT}")?;
    writeln!(result, "")?;
    writeln!(result, "import Lampe")?;
    writeln!(result, "")?;
    writeln!(result, "open Lampe")?;
    writeln!(result, "")?;
    writeln!(result, "namespace {}", &noir_package_identifier.name)?;
    writeln!(result, "namespace «{}»", &noir_package_identifier.version)?;
    writeln!(result, "namespace {}", EXTRACTED_MODULE_NAME)?;
    writeln!(result, "namespace {}", extracted_module)?;
    writeln!(result, "namespace «{}»", extracted_version)?;
    writeln!(result, "")?;
    result.push_str(&extracted_code.content);

    fs::write(output_file, result)?;

    Ok(())
}
