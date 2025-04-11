//! A library for extracting [Noir](https://noir-lang.org) programs to
//! equivalent definitions in the [Lean](https://lean-lang.org) theorem prover
//! and programming language.
//!
//! It provides functionality for ingesting a Noir project, compiling it from
//! source, and then generating definitions in a Lean DSL that provides the
//! proof assistant with all the information necessary to formally verify the
//! program.

#![warn(clippy::all, clippy::cargo, clippy::pedantic)]
// Allows for better API naming
#![allow(clippy::module_name_repetitions)]
// These occur in our Noir dependencies and cannot be avoided.
#![allow(clippy::multiple_crate_versions)]
// This only occurs for keys of type `Type`. It may be worth checking if this is actually an issue
// we should worry about
#![allow(clippy::mutable_key_type)]

mod lean;
mod noir;

pub mod error;
mod file_generator;
pub mod project;

pub use error::Error;
pub use project::Project;

pub use file_generator::error as file_generator_error;
pub use noir::error as noir_error;

#[cfg(test)]
mod tests {
    use std::fs;
    use tempfile::tempdir;

    use crate::Project;

    fn test_extractor_on(main_source: &str) -> std::io::Result<(Vec<String>, String)> {
        let temp_dir = tempdir().expect("creating temp_dir");

        let nargo_toml = r#"
[package]
name = "MockProject"
type = "lib"
authors = [""]

[dependencies]
"#;

        fs::write(temp_dir.path().join("Nargo.toml"), nargo_toml)?;
        fs::create_dir(temp_dir.path().join("src"))?;
        fs::write(temp_dir.path().join("src").join("lib.nr"), main_source)?;

        let mock_project =
            Project::new(temp_dir.path().to_path_buf()).expect("creating mock project");
        let warnings = mock_project
            .extract()
            .expect("getting warnings")
            .warnings
            .iter()
            .map(|warning| format!("{warning:?}"))
            .collect();

        let extracted_file = fs::read_to_string(
            temp_dir
                .path()
                .join("lampe")
                .join("MockProject")
                .join("Extracted")
                .join("Main")
                .with_extension("lean"),
        )
        .expect("reading file");

        Ok((warnings, extracted_file))
    }

    #[test]
    fn test_unbound() {
        let type_source = r#"
struct Bad<T> {
    x: Field,
}

fn mkBad<T>() -> Bad<T> {
    Bad { x: 3 }
}

fn main() -> pub Field {
    let f = mkBad();
    f.x
}
"#;
        assert!(test_extractor_on(type_source).is_ok());
    }
}
