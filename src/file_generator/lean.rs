use crate::file_generator::{
    EXTRACTED_LIB_NAME, Error, LAMPE_GENERATED_COMMENT, LeanFileContent, LeanFilePath,
};
use itertools::Itertools;
use nargo::package::Package;
use std::collections::{HashMap, HashSet};
use std::fmt::Write;
use std::fs;
use std::path::Path;

pub fn generate_lean_files(
    lampe_root_dir: &Path,
    package: &Package,
    extracted_files: &HashMap<LeanFilePath, LeanFileContent>,
) -> Result<(), Error> {
    let lib_name = &package.name.to_string();

    let lib_dir = lampe_root_dir.join(lib_name);
    if !lib_dir.exists() {
        fs::create_dir(&lib_dir)?;
    }

    generate_lib_file(lampe_root_dir, lib_name, false)?;

    let extracted_lib_dir = lib_dir.join(EXTRACTED_LIB_NAME);
    if !extracted_lib_dir.exists() {
        fs::create_dir(&extracted_lib_dir)?;
    }

    for (file_path, extracted_lean) in extracted_files {
        let lib_name = if file_path.is_type_path() {
            None
        } else {
            Some(lib_name.as_str())
        };

        generate_extracted_file(
            lib_name,
            &extracted_lib_dir,
            file_path,
            extracted_lean,
            true,
        )?;
    }
    generate_extracted_lib_file(
        lib_name,
        &lib_dir,
        &extracted_files.keys().map(LeanFilePath::to_lean_import).collect(),
        true,
    )?;

    Ok(())
}

fn generate_lib_file(
    lampe_root_dir: &Path,
    lib_name: &String,
    overwrite: bool,
) -> Result<(), Error> {
    let output_file = lampe_root_dir.join(format!("{lib_name}.lean"));
    if output_file.exists() && !overwrite {
        return Ok(());
    }

    let mut result = String::new();

    write!(result, "-- {LAMPE_GENERATED_COMMENT}\n\n")?;
    writeln!(result, "import {lib_name}.{EXTRACTED_LIB_NAME}")?;

    fs::write(output_file, result)?;

    Ok(())
}

fn generate_extracted_lib_file(
    lib_name: &String,
    lib_dir: &Path,
    file_names: &HashSet<String>,
    overwrite: bool,
) -> Result<(), Error> {
    let output_file = lib_dir.join(format!("{EXTRACTED_LIB_NAME}.lean"));
    if output_file.exists() && !overwrite {
        return Ok(());
    }

    let mut result = String::new();

    write!(result, "-- {LAMPE_GENERATED_COMMENT}\n\n")?;
    for file_name in file_names {
        writeln!(result, "import {lib_name}.{EXTRACTED_LIB_NAME}.{file_name}")?;
    }

    result.push('\n');

    let environment_string = file_names
        .iter()
        .filter(|name| *name != "Types")
        .map(|name| format!("{EXTRACTED_LIB_NAME}.") + name + ".env")
        .join(" ++ ");

    write!(result, "def Extracted.env := {environment_string}")?;

    fs::write(output_file, result)?;

    Ok(())
}

fn generate_extracted_file(
    lib_name: Option<&str>,
    extracted_lib_dir: &Path,
    file_path: &LeanFilePath,
    extracted_lean: &LeanFileContent,
    overwrite: bool,
) -> Result<(), Error> {
    let output_file = extracted_lib_dir.join(file_path.to_lean_path());
    if output_file.exists() && !overwrite {
        return Ok(());
    }

    if let Some(parent_dir) = output_file.parent() {
        fs::create_dir_all(parent_dir)?;
    }

    let mut result = String::new();

    write!(result, "-- {LAMPE_GENERATED_COMMENT}\n\n")?;

    if let Some(lib_name) = lib_name {
        writeln!(result, "import {lib_name}.{EXTRACTED_LIB_NAME}.Types")?;
    }

    result.push_str("import Lampe\n\n");
    result.push_str("open Lampe\n\n");
    write!(result, "namespace {EXTRACTED_LIB_NAME}\n\n")?;
    result.push_str(extracted_lean);

    fs::write(output_file, result)?;

    Ok(())
}
