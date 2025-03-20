use crate::file_generator::Error;
use std::fs;
use std::path::PathBuf;

pub fn generate_lean_toolchain(lampe_root_dir: &PathBuf) -> Result<(), Error> {
    let mut result = String::new();
    result.push_str("leanprover/lean4:v4.15.0\n");

    fs::write(lampe_root_dir.join("lean-toolchain"), result)?;

    Ok(())
}
