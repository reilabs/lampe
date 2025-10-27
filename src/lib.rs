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

pub mod constants;
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

    use tempfile::{tempdir, TempDir};
    use walkdir::WalkDir;

    use crate::{
        lean::{ast::Crate, LEAN_KEYWORDS, LEAN_QUOTE_END, LEAN_QUOTE_START},
        Project,
    };

    /// Set up a mock Noir project for extraction
    fn set_up_project(main_source: &str) -> std::io::Result<(TempDir, Project)> {
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

        let temp_path = temp_dir.path().to_path_buf();

        Ok((
            temp_dir,
            Project::new(temp_path.clone(), temp_path).expect("creating mock project"),
        ))
    }

    /// Returns a tuple of warnings and a string representation of the extracted
    /// files
    #[expect(clippy::format_push_string)]
    fn display_extraction_results(main_source: &str) -> std::io::Result<(Vec<String>, String)> {
        let (temp_dir, mock_project) = set_up_project(main_source)?;

        let warnings = mock_project
            .extract(true)
            .expect("getting warnings")
            .warnings
            .iter()
            .map(|warning| format!("{warning:?}"))
            .collect();

        let mut extracted_files = String::new();

        for entry_result in WalkDir::new(temp_dir.path()) {
            let entry = match entry_result {
                Ok(entry) => entry,
                Err(err) => panic!("unable to access entry: {err}"),
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

    /// Returns the generated crate data for testing the generator instead of
    /// the writer.
    fn get_crate_data(main_source: &str) -> Result<Crate, crate::Error> {
        let (temp_dir, mock_project) = set_up_project(main_source).unwrap();

        // Prevent the temp directory from being deleted so that we can read the
        // Nargo.toml file for names
        let _temp_dir_path = temp_dir.keep();

        let package = &mock_project.nargo_workspace.members[0];
        let noir_project = crate::noir::Project::new(
            &mock_project.nargo_file_manager,
            &mock_project.nargo_parsed_files,
        );
        let generator = noir_project
            .compile_package(package, &mock_project.nargo_workspace)?
            .take();

        Ok(generator.generate())
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
        let result = display_extraction_results(type_source);
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
        let result = display_extraction_results(lambda_function_source);

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
        let result = display_extraction_results(trait_source);

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
        let result = display_extraction_results(struct_source);
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
        let result = display_extraction_results(generic_function_source);
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

        let result = display_extraction_results(global_source);
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
        let result = display_extraction_results(slice_source);
        assert!(result.is_ok());

        print!("{}", result.unwrap().1);
    }

    #[test]
    fn test_arrays() {
        let array_source = r"
fn use_array() -> Field {
    let a = [1; 4];
    a[0]
}
";
        let result = display_extraction_results(array_source);
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
        let result = display_extraction_results(repslice_source);
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
        let result = display_extraction_results(unbound_source);
        assert!(result.is_ok());

        print!("{}", result.unwrap().1);
    }

    #[test]
    fn test_unbound2() {
        let unbound_source = r"
trait Add2 {
    fn add(self, other: Self) -> Self;
}

impl Add2 for u64 {
    fn add(self, other: Self) -> Self {
        self + other
    }
}

fn call_trait2<T, U> (x: T, y: U) -> Field where T: Add2, U: Add2 {
    let x = x.add(x);
    let y = y.add(y);
    3
}

fn call_trait2_unbound(x: u64, y: u64) -> Field {
    let z = call_trait2(x, y);
    3
}
";
        let result = display_extraction_results(unbound_source);
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
        let result = display_extraction_results(const_generic_source);
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
        let result = display_extraction_results(const_generic_source);
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
        let result = display_extraction_results(const_generic_source);
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
        let result = display_extraction_results(const_generic_source);
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
        let result = display_extraction_results(colon_source);
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
        let result = display_extraction_results(colon_source);
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

        let result = display_extraction_results(eq_source);
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

        let result = display_extraction_results(eq_source);
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

        let result = display_extraction_results(eq_source);
        assert!(result.is_ok());

        print!("{}", result.unwrap().1);
    }

    #[test]
    fn keyword_conflicts() {
        use crate::lean::ast::*;

        let keyword_source = r"
mod has {
    pub mod meta {
        pub mod from {
            pub struct name;
        }
    }
}

    fn from() ->  Field {
        3
    }
";
        let crate_data = get_crate_data(keyword_source).unwrap();

        let assert_good_name = |name: &str| {
            println!("name: {name}");
            assert!(name.split("::").all(|part| {
                let quoted = part.starts_with(LEAN_QUOTE_START) && part.ends_with(LEAN_QUOTE_END);
                if quoted {
                    // Ensure quoted parts are lean keywords or contain special characters
                    let inner = &part[LEAN_QUOTE_START.len()..part.len() - LEAN_QUOTE_END.len()];
                    LEAN_KEYWORDS.contains(&inner) || inner.chars().any(|c| c == '-' || c == '.')
                } else {
                    // Ensure unquoted parts are not lean keywords
                    !LEAN_KEYWORDS.contains(&part)
                }
            }));
        };

        for module in crate_data.modules {
            for item in module.entries {
                match item {
                    ModuleDefinition::Global(global_definition) => {
                        assert_good_name(&global_definition.name);
                    }
                    ModuleDefinition::Function(function_definition) => {
                        assert_good_name(&function_definition.name);
                    }
                    ModuleDefinition::TraitImpl(trait_implementation) => {
                        assert_good_name(&trait_implementation.name);
                        for method in trait_implementation.methods {
                            assert_good_name(&method.name);
                        }
                    }
                }
            }
        }

        for type_data in crate_data.types {
            assert_good_name(type_data.name());
        }
    }

    #[test]
    fn not_eq() {
        let neq_source = r"
fn not_eq<A: Eq>(a: A, b: A) -> bool {
    a != b
}
";

        let result = display_extraction_results(neq_source);
        assert!(result.is_ok());

        print!("{}", result.unwrap().1);
    }

    #[test]
    fn generic_ord() {
        let ord_source = r"
fn leq<A: Ord>(a: A, b: A) -> bool {
    a <= b
}
";

        let result = display_extraction_results(ord_source);
        assert!(result.is_ok());

        print!("{}", result.unwrap().1);
    }

    #[test]
    fn trait_where_bounds() {
        let source = r"
trait MyFrom<T> {
    fn from(input: T) -> Self;
}

trait MyInto<T> {
    fn into(self) -> T;
}

impl<T> MyFrom<T> for T {
    fn from(input: T) -> Self {
        input
    }
}

impl<T, U> MyInto<T> for U where T: From<U> {
    fn into(self) -> T {
        T::from(self)
    }
}
";

        let result = display_extraction_results(source);
        assert!(result.is_ok());

        print!("{}", result.unwrap().1);
    }
}
