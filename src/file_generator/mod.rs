//! This module contains functionality for interacting with the Lampe output.

use crate::file_generator::error::{Error, Result};
use nargo::package::{Dependency, Package};
use std::collections::HashMap;
use std::{fmt, fs};
use std::path::{Path, PathBuf};
use nargo_toml::DependencyConfig;
use crate::file_generator::lake::dependency::{LeanDependency, LeanDependencyGit, LeanDependencyPath};
use crate::file_generator_error::Error::LakeRequireGeneration;

pub mod error;
pub mod lake;
mod lean;
mod lean_toolchain;

const LAMPE_DIR_NAME: &str = "lampe";
const EXTRACTED_MODULE_NAME: &str = "Extracted";
const LAMPE_GENERATED_COMMENT: &str = "Generated by lampe";

#[derive(Debug)]
pub struct LeanFile {
    pub content: String,
}

#[derive(Hash, Eq, PartialEq, Clone, Debug)]
pub struct NoirPackageIdentifier {
    pub name: String,
    pub version: String,
}

pub fn lampe_project(
    noir_root_dir: &Path,
    noir_package_identifier: &NoirPackageIdentifier,
    additional_dependencies: &Vec<Box<dyn LeanDependency>>,
    extracted_code: &LeanFile,
    extracted_dependencies: &HashMap<NoirPackageIdentifier, LeanFile>,
) -> Result<()> {
    let lampe_root_dir = noir_root_dir.join(LAMPE_DIR_NAME);

    if !lampe_root_dir.exists() {
        fs::create_dir(&lampe_root_dir)?;
    }

    generate_package_structure(&lampe_root_dir, &noir_package_identifier, additional_dependencies, extracted_code, extracted_dependencies)?;

    Ok(())
}

fn generate_package_structure(
    lampe_root_dir: &Path,
    noir_package_identifier: &NoirPackageIdentifier,
    additional_dependencies: &Vec<Box<dyn LeanDependency>>,
    extracted_code: &LeanFile,
    extracted_dependencies: &HashMap<NoirPackageIdentifier, LeanFile>,
) -> Result<()> {
    lake::generate_lakefile_toml(lampe_root_dir, noir_package_identifier, additional_dependencies, false)?;
    lean_toolchain::generate_lean_toolchain(lampe_root_dir, false)?;
    lean::generate_lean_files(lampe_root_dir, noir_package_identifier, extracted_code, extracted_dependencies)?;

    Ok(())
}

pub fn get_lean_dependency(dependency_name: &String, dependency_config: &DependencyConfig) -> Result<Box<dyn LeanDependency>> {
    match dependency_config {
        DependencyConfig::Github { git, tag, directory } => {
            let directory = directory.clone().unwrap_or("".to_string());
            let path = Path::new(&directory).join(LAMPE_DIR_NAME);
            let subdir = path.to_str().ok_or(LakeRequireGeneration(format!("Error preparing subdir: {:?}", path)))?;

            Ok(Box::new(LeanDependencyGit::builder(dependency_name)
                .git(git)
                .rev(tag)
                .subdir(subdir)
                .build()))
        }
        DependencyConfig::Path { path } => {
            let path = Path::new(path);
            let path = if path.is_relative() {
                // If the path is relative we need to get parent dir as Nargo.toml is there
                Path::new("..").join(path)
            } else {
                path.into()
            };
            let path = path.join(LAMPE_DIR_NAME);
            let path = path.to_str().ok_or(LakeRequireGeneration(format!("Error preparing path: {:?}", path)))?;

            Ok(Box::new(LeanDependencyPath::builder(dependency_name)
                .path(path)
                .build()))
        }
    }
}

pub fn has_lampe(package: &Package) -> bool {
    let package_lampe_dir = package.root_dir.join(LAMPE_DIR_NAME);
    package_lampe_dir.exists() && package_lampe_dir.is_dir()
}

pub fn read_lampe_package_name(package: &Package) -> Result<String> {
    let package_lampe_dir = package.root_dir.join(LAMPE_DIR_NAME);
    Ok(lake::read_package_name(&package_lampe_dir)?)
}
