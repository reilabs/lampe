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

pub mod lean;
pub mod noir;

pub mod error;
pub mod file_generator;
pub mod project;

pub use error::Error;
pub use file_generator::error as file_generator_error;
pub use noir::error as noir_error;
pub use project::Project;

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
            Project::new(temp_dir.path().to_path_buf(), temp_dir.path().to_path_buf())
                .expect("creating mock project");
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
                Err(err) => panic!("unable to acecss entry: {err}"),
            };

            if entry.file_type().is_file() {
                extracted_files.push_str("----------------------\n");
                extracted_files.push_str(&format!("{entry:?}\n"));
                extracted_files.push_str("----------------------\n");
                extracted_files.push_str(&fs::read_to_string(entry.path()).unwrap());
                extracted_files.push('\n');
            }
        }

        Ok((warnings, extracted_files))
    }

    #[test]
    fn test_order() {
        let type_source = r"
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
";
        let result = test_extractor_on(type_source);
        assert!(result.is_ok());
    }

    // TODO: Delete
    #[test]
    fn test_lambda() {
        let lambda_function_source = r"
fn simple_lambda(x : Field, y : Field) -> Field {
    let add = |a, b| a + b;
    add(x, y)
}
";
        let result = test_extractor_on(lambda_function_source);

        assert!(result.is_ok());

        print!("{}", result.unwrap().1);
    }

    // TODO: Delete
    #[test]
    fn test_traits() {
        let trait_source = r"
trait FooTrait<I> {
    fn foo(self) -> I;
}

struct FooStruct;

impl FooTrait<Field> for FooStruct {
    fn foo(self) -> Field {
        42
    }
}
";
        let result = test_extractor_on(trait_source);

        assert!(result.is_ok());

        print!("{}", result.unwrap().1);
    }

    #[test]
    fn test_structs() {
        let struct_source = r"
struct FooStruct {
    x: Field,
    y: Field
}

struct GenericFoo<I> {
    x: I,
    y: I
}

fn create_generic_foo<I>(x: I, y: I) -> GenericFoo<I> {
    GenericFoo { x, y }
}
";
        let result = test_extractor_on(struct_source);
        assert!(result.is_ok());

        print!("{}", result.unwrap().1);
    }

    #[test]
    fn test_generics() {
        let generic_function_source = r"
fn generic_func<I>(a: I) -> I {
    a
}

fn call_generic_func(a : Field) -> Field {
    let x = generic_func(a);
    x
}
";
        let result = test_extractor_on(generic_function_source);
        assert!(result.is_ok());

        print!("{}", result.unwrap().1);
    }

    #[test]
    fn test_globals() {
        let global_source = r"
global FOO : Field = 42;
global FOOS : [Field; 2] = [FOO, FOO + 1];

fn use_globals() -> [Field; 2] {
    let y = FOO;
    let x = FOOS;
    [y, x[1]]
}
    ";

        let result = test_extractor_on(global_source);
        assert!(result.is_ok());

        print!("{}", result.unwrap().1);
    }

    #[test]
    fn test_slices() {
        let slice_source = r"
fn use_slice() -> Field {
    let s = [1,2,3];
    let t = s.as_slice();
    t[0]
}
";
        let result = test_extractor_on(slice_source);
        assert!(result.is_ok());

        print!("{}", result.unwrap().1);
    }

    // TODO: Note that in this test we can see all of the weird cases with numeric
    // generics not being displayed correctly. Once with too many annotations
    // (ini the #arrayIndex call with (0 : u32) as u32) And again with not
    // enough (in the `Array<Field, 4>` annotations)
    #[test]
    fn test_arrays() {
        let array_source = r"
fn use_array() -> Field {
    let a = [1; 4];
    a[0]
}
";
        let result = test_extractor_on(array_source);
        assert!(result.is_ok());

        print!("{}", result.unwrap().1);
    }

    #[test]
    fn test_rep_slice() {
        let repslice_source = r"
fn repeated_slice() -> Field {
    let a = &[1; 4];
    a[0]
}
";
        let result = test_extractor_on(repslice_source);
        assert!(result.is_ok());

        print!("{}", result.unwrap().1);
    }

    #[test]
    fn test_unbound() {
        let unbound_source = r"
struct MyStruct {
    x : Field
}

trait WeirdAdd {
    fn weird_add(self, other: Self) -> Self;
}

impl WeirdAdd for MyStruct {
    fn weird_add(self, other: Self) -> Self {
        MyStruct { x: self.x + other.x }
    }
}

fn call_trait2<T, U> (x : T, y : U) -> Field where T : WeirdAdd, U : WeirdAdd {
    let x = x.weird_add(x);
    let y = y.weird_add(y);
    3
}

fn call_trait2_unbound<T>(x : T, y : T) -> Field where T : WeirdAdd {
    let z = call_trait2::<T, T>(x, y);
    3
}
";
        let result = test_extractor_on(unbound_source);
        assert!(result.is_ok());

        print!("{}", result.unwrap().1);
    }

    #[test]
    fn test_unbound2() {
        let unbound_source = r"
use std::ops::arith::Add;

fn call_trait2<T, U> (x: T, y: U) -> Field where T: Add, U: Add {
    let x = x.add(x);
    let y = y.add(y);
    3
}

fn call_trait2_unbound(x: u64, y: u64) -> Field {
    let z = call_trait2(x, y);
    3
}
";
        let result = test_extractor_on(unbound_source);
        assert!(result.is_ok());

        print!("{}", result.unwrap().1);
    }

    #[test]
    fn test_const_generic() {
        let const_generic_source = r"
    fn creat_arr<let N : u32>() -> [Field; N] {
        [1; N]
    }

    fn create_arr() -> [Field; 3] {
        [1; 3]
    }
";
        let result = test_extractor_on(const_generic_source);
        assert!(result.is_ok());

        print!("{}", result.unwrap().1);
    }

    #[test]
    fn test_const_generic2() {
        let const_generic_source = r"
    fn const_test<let N : u32>(x : Field) -> Field {
        let mut res = x;

        for _ in 0 .. N {
            res = res * 2;
        }
        res
    }
    ";
        let result = test_extractor_on(const_generic_source);
        assert!(result.is_ok());

        print!("{}", result.unwrap().1);
    }

    #[test]
    fn bounded_vec() {
        let const_generic_source = r"
pub struct BVec<T, let MaxLen: u32> {
    storage: [T; MaxLen],
    len: u32,
}
    ";
        let result = test_extractor_on(const_generic_source);
        assert!(result.is_ok());

        print!("{}", result.unwrap().1);
    }

    #[test]
    fn impl_block() {
        let const_generic_source = r"
pub struct Option2 {
    _is_some: bool
}

impl Option2 {
    pub fn none() -> Option2 {
        Self { _is_some: false }
    }
}
    ";
        let result = test_extractor_on(const_generic_source);
        assert!(result.is_ok());

        print!("{}", result.unwrap().1);
    }

    #[test]
    fn colon_test() {
        let colon_source = r"
mod asdf {
    fn colon_test() -> Field {
        let a: Field = 5;
        let b: Field = 10;
        a + b
    }

    pub type FField = Field;

    struct Other {
        field: FField
    }

    mod inner {
        use super::{FField, Other};

        fn colon_test_inner() -> FField {
            let a: FField = 5;
            let b: FField = 10;
            let c = Other { field: a + b };
            c.field
        }
    }
}

";
        let result = test_extractor_on(colon_source);
        assert!(result.is_ok());

        print!("{}", result.unwrap().1);
    }

    #[test]
    fn const_generic_arithmetic() {
        let colon_source = r"
fn replicate<T, let L: u32, let N: u32>(arr: [T; L]) -> [T; L * N] {
    let mut result = [arr[0]; L * N];

    for i in 0 .. (L*N) {
        result[i] = arr[i % L];
    }

    result
}

fn call_replicate<T, let L: u32>(arr: [T; L]) -> [T; 3 * L] {
    replicate::<T, L, 3>(arr)
}
";
        let result = test_extractor_on(colon_source);
        assert!(result.is_ok());

        print!("{}", result.unwrap().1);
    }

    #[test]
    fn eq_test() {
        let eq_source = r"
struct MyStruct {
    x : Field
}

trait MEq {
    fn meq(self, other: Self) -> bool;
}

impl Eq for MyStruct {
    fn eq(self, other: Self) -> bool {
        self.x == other.x
    }
}

impl MEq for MyStruct {
    fn meq(self, other: Self) -> bool {
        self.x == other.x
    }
}

fn using_eq(a: MyStruct, b: MyStruct) -> bool {
    let meq = a.meq(b);
    let beq = a.eq(b);
    let beq2 = a == b;
    meq & beq & beq2
}
";

        let result = test_extractor_on(eq_source);
        assert!(result.is_ok());

        print!("{}", result.unwrap().1);
    }

    #[test]
    fn trait_method_call_extraction_with_generics() {
        let eq_source = r"
trait BinaryHasherIsh<F> {
    fn hash(l: F, r: F) -> F;
}

fn call_binary_hasher<H>() -> Field where H: BinaryHasherIsh<Field> {
    H::hash(0, 1)
}
";

        let result = test_extractor_on(eq_source);
        assert!(result.is_ok());

        print!("{}", result.unwrap().1);
    }

    #[test]
    fn trait_method_call_extraction_with_assoc_types() {
        let eq_source = r"
trait BinaryHasherIsh2 {
    type F;

    fn hash(l: Self::F, r: Self::F) -> Self::F;
}

fn call_binary_hasher_2<H>() -> Field where H: BinaryHasherIsh2<F = Field> {
    H::hash(0, 1)
}
";

        let result = test_extractor_on(eq_source);
        assert!(result.is_ok());

        print!("{}", result.unwrap().1);
    }
}
