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
    use walkdir::WalkDir;

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

        let mut extracted_files = String::new();

        for entry_result in WalkDir::new(temp_dir.path()) {
            let entry = match entry_result {
                Ok(entry) => entry,
                Err(err) => panic!("unable to acecss entry: {}", err),
            };

            if entry.file_type().is_file() {
                extracted_files.push_str("----------------------\n");
                extracted_files.push_str(&format!("{entry:?}\n"));
                extracted_files.push_str("----------------------\n");
                extracted_files.push_str(&fs::read_to_string(&entry.path()).unwrap());
                extracted_files.push('\n');
            }
        }

        Ok((warnings, extracted_files))
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

    #[test]
    fn test_order() {
        let type_source = r#"
struct FooStruct2 {
    x: FooStruct
}

struct FooStruct {
    x: FooType,
}

type FooType = Field;

struct BarStruct {
    y: Field
}

type BarType = BarStruct;
"#;
        let result = test_extractor_on(type_source);
        assert!(result.is_ok());
    }

    #[test]
    fn test_func_order() {
        let type_source = r#"// mod test;
trait BinaryHasher<F> {
    fn hash(a: F, b: F) -> F;
}

global RC: [Field; 8] = [0,0,0,0,0,0,0,0];

global SIGMA: Field = 0;

fn rl(u: u8) -> u8 {
    0
}

fn rotate_left(u: u8, N: u8) -> u8 {
    0
}

fn sbox(v: u8) -> u8 {
    0
}

fn from_le_bytes(bytes: [u8; 32]) -> Field {
    0
}

pub fn sgn0(self: Field) -> u1 {
    self as u1
}

// NOTE: hacky workaround
fn to_le_bits(self: Field) -> [u1; 256] {
    [0; 256]
}

fn to_le_bytes(self: Field) -> [u8; 32] {
    [0; 32]
}

fn as_array(self: [u8]) -> [u8; 32] {
    [0; 32]
}

fn bar(a: Field) -> Field {
    a
}

fn square(a: Field) -> Field {
    a * a * SIGMA
}

fn permute(s: [Field; 2]) -> [Field; 2] {
    [0,0]
}

pub struct Skyscraper {}

impl BinaryHasher<Field> for Skyscraper {
    fn hash(a: Field, b: Field) -> Field {
        let x = permute([a, b]);
        x[0] + a
    }
}

pub fn mtree_recover<H, let N: u32>(idx: [bool; N], p: [Field; N], item: Field) -> Field
where
    H: BinaryHasher<Field>,
{
    0
}

unconstrained fn weird_eq_witness(a : Field, b : Field) -> Field {
    a
}

// This is pointless, but demonstrated how we can use unconstrained functions
fn weird_assert_eq(a : Field, b : Field) {
    assert(a == b);
}

fn main(root: pub Field, proof: pub [Field; 32], item: pub Field, idx: [bool; 32]) -> pub Field {
    0
}"#;

        let result = test_extractor_on(type_source);

        assert!(result.is_ok());

        println!("{}", result.unwrap().1);
    }
}
