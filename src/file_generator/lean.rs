use crate::file_generator::{
    EXTRACTED_LIB_NAME, Error, LAMPE_GENERATED_COMMENT, LeanFileContent, LeanFileName,
};
use nargo::package::Package;
use std::collections::{HashMap, HashSet};
use std::fmt::Write;
use std::fs;
use std::path::Path;

pub fn generate_lean_files(
    lampe_root_dir: &Path,
    package: &Package,
    extracted_files: &HashMap<LeanFileName, LeanFileContent>,
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

    for (file_name, extracted_lean) in extracted_files {
        generate_extracted_file(&extracted_lib_dir, file_name, extracted_lean, true)?;
    }
    generate_extracted_lib_file(lib_name, &lib_dir, &extracted_files.keys().collect(), true)?;

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
    file_names: &HashSet<&String>,
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

    fs::write(output_file, result)?;

    Ok(())
}

fn generate_extracted_file(
    extracted_lib_dir: &Path,
    file_name: &LeanFileName,
    extracted_lean: &LeanFileContent,
    overwrite: bool,
) -> Result<(), Error> {
    let output_file = extracted_lib_dir.join(format!("{file_name}.lean"));
    if output_file.exists() && !overwrite {
        return Ok(());
    }

    let mut result = String::new();

    write!(result, "-- {LAMPE_GENERATED_COMMENT}\n\n")?;
    result.push_str("import Lampe\n\n");
    result.push_str("open Lampe\n\n");
    write!(result, "namespace {EXTRACTED_LIB_NAME}\n\n")?;
    result.push_str(extracted_lean);

    fs::write(output_file, result)?;

    Ok(())
}
