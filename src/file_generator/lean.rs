use crate::file_generator::{
    EXTRACTED_DIR_NAME, Error, LAMPE_GENERATED_COMMENT, LeanFileContent, LeanFileName,
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
    let name = &package.name.to_string();

    let lib_dir = lampe_root_dir.join(name);
    if !lib_dir.exists() {
        fs::create_dir(&lib_dir)?;
    }
    generate_lib_lean(lampe_root_dir, package)?;

    let extracted_dir = lib_dir.join(EXTRACTED_DIR_NAME);
    if !extracted_dir.exists() {
        fs::create_dir(&extracted_dir)?;
    }

    for (file_name, extracted_lean) in extracted_files {
        write_extracted_file(&lib_dir, file_name, extracted_lean)?;
    }
    generate_extracted(&lib_dir, package, &extracted_files.keys().collect())?;

    Ok(())
}

fn generate_lib_lean(lib_dir: &Path, package: &Package) -> Result<(), Error> {
    let name = &package.name.to_string();

    let mut result = String::new();
    writeln!(result, "import {name}.{EXTRACTED_DIR_NAME}")?;

    fs::write(lib_dir.join(format!("{name}.lean")), result)?;

    Ok(())
}

fn generate_extracted(
    lib_dir: &Path,
    package: &Package,
    file_names: &HashSet<&String>,
) -> Result<(), Error> {
    let name = &package.name.to_string();

    let mut result = String::new();

    write!(result, "-- {LAMPE_GENERATED_COMMENT}\n\n")?;
    for file_name in file_names {
        writeln!(result, "import {name}.{EXTRACTED_DIR_NAME}.{file_name}")?;
    }

    fs::write(lib_dir.join(format!("{EXTRACTED_DIR_NAME}.lean")), result)?;

    Ok(())
}

fn write_extracted_file(
    lib_dir: &Path,
    file_name: &LeanFileName,
    extracted_lean: &LeanFileContent,
) -> Result<(), Error> {
    let mut result = String::new();

    write!(result, "-- {LAMPE_GENERATED_COMMENT}\n\n")?;
    result.push_str("import Lampe\n\n");
    result.push_str("open Lampe\n\n");
    result.push_str(&format!("namespace {EXTRACTED_DIR_NAME}\n\n"));

    result.push_str(extracted_lean);

    fs::write(
        lib_dir.join(EXTRACTED_DIR_NAME).join(format!("{file_name}.lean")),
        result,
    )?;

    Ok(())
}
