use crate::file_generator::Error;
use std::fs;
use std::path::Path;

pub fn generate_lean_toolchain(lampe_root_dir: &Path, overwrite: bool) -> Result<(), Error> {
    let output_file = lampe_root_dir.join("lean-toolchain");
    if output_file.exists() && !overwrite {
        return Ok(());
    }

    let mut result = String::new();
    result.push_str("leanprover/lean4:v4.15.0\n");

    fs::write(output_file, result)?;

    Ok(())
}
