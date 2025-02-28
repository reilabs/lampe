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

pub mod error;
pub mod lean;
pub mod noir;

/// The result type for use with the library, exported here for easy access.
pub use crate::error::Result;
/// The project type for use with the library, exported here for easy access.
pub use crate::noir::project::Project;
/// The source type for use with the library, exported here for easy access.
pub use crate::noir::source::Source;

/// Takes the definition of a Noir project and converts it into equivalent
/// definitions in the Lean theorem prover and programming language.
///
/// # Errors
///
/// If the extraction process fails for any reason.
pub fn noir_to_lean(project: Project) -> Result<noir::WithWarnings<String>> {
    let lean_emitter = project.compile()?;
    let source = lean_emitter.emit()?;
    Ok(noir::WithWarnings::new(source, lean_emitter.warnings))
}

#[cfg(test)]
mod test {
    use std::path::Path;

    use crate::{
        noir::{project::Project, source::Source},
        noir_to_lean,
    };

    fn extract_str(source: &str) -> anyhow::Result<String> {
        // Set up our source code
        let file_name = Path::new("main.nr");
        let source = Source::new(file_name, source);
        // Create our project
        let project = Project::new(Path::new(""), source);
        // Execute the compilation step on our project.
        let output = noir_to_lean(project)?.take();
        Ok(output)
    }

    /// Runs the extraction on `source` and prints the result to the std output.
    fn print_result(source: &str) -> anyhow::Result<()> {
        let output = extract_str(source)?;
        println!("{output}");
        Ok(())
    }

    /// This test is a bit of a mess and exists purely for experimentation.
    #[test]
    fn runs() -> anyhow::Result<()> {
        print_result(
            r#"
            use std::default::Default;

            fn my_func3(a: u8) -> u8 {
                my_func(a)
            }

            fn my_func(a: u8) -> u8 {
                a + 1
            }

            fn my_func2(arr: [u8; 8], b: u8) -> u8 {
                arr[b]
            }

            fn get_unchecked<T>(a: Option2<T>) -> T {
                a._value
            }

            fn my_fn() -> u8 {
              1 + 1
            }

            fn cast_test(a: u8) -> u64 {
                if a == 0 {
                    0
                } else {
                    a as u64
                }
            }

            fn tuple_test(a: u8) -> (u8, u8) {
                let b = | c | c + a + 10;
                (a, a)
            }

            fn literal_test() -> () {
                let a = 1;
                let b = true;
                let c = false;
                let d = [1; 5];
                let e = &[1; 5];
                let f = [1, 2, 3];
                let g = &[];
                // let h = "asdf";
                // let i = f"${g}";
            }

            fn assigns(x: u8) {
                let mut y = 3;
                y += x;

                let mut foo = Option2::none();
                foo._is_some = false;

                let mut arr = [1, 2];
                arr[0] = 10;
            }

            // unconstrained fn loop(x: u8) {
            //     for i in 0 .. x {
            //         if i == 2 {
            //             continue;
            //         }
            //
            //         if i == 5 {
            //             break;
            //         }
            //     }
            // }

            fn check(x: u8) {
                assert(x == 5);
            }

            struct Option2<T> {
                _is_some: bool,
                _value: T,
            }

            impl<T> Default for Option2<T> {
                fn default() -> Self {
                    Option2::none()
                }
            }

            impl <T> Option2<T> {
                /// Constructs a None value
                pub fn none() -> Self {
                    Self { _is_some: false, _value: std::mem::zeroed() }
                }

                /// Constructs a Some wrapper around the given value
                pub fn some(_value: T) -> Self {
                   Self { _is_some: true, _value }
                }

                /// True if this Option is None
                pub fn is_none(self) -> bool {
                    !self.is_some()
                }

                /// True if this Option is Some
                pub fn is_some(self) -> bool {
                    self._is_some
                }
            }

            trait MyTrait {
                fn foo(self) -> Self {
                    self
                }
            }

            impl<T> MyTrait for Option2<T> {
                fn foo(self) -> Self {
                    self
                }
            }

            impl<T> MyTrait for (T, bool) where T : MyTrait {
                fn foo(self) -> Self {
                    self
                }
            }

            fn string_test() -> str<5> {
                let x : str<5> = "Hello";
                x
            }

            fn fmtstr_test(x: Field, y: Field) -> Field {
                assert(x != y);
                let _a: fmtstr<37, (Field, Field)> = f"this is first:{x}  this is second:{y}";
                x + y
            }

            fn impl_test(x: impl MyTrait, y: impl Default) -> impl Default {
                false
            }

            type AliasedOpt<T> = Option2<T>;

            fn is_alias_some<T>(x: AliasedOpt<T>) -> bool {
                x.is_some()
            }

            fn main() {
                let mut op1 = Option2::some(5);
                let op2 = Option2::default();
                let op3 = if true { op1 } else { op2 }.foo();
                op1.is_some();
                let mut l = [1, 2, 3];
                l[0];
                let t = (1, true, 3);
                t.2;
                l[1] = 4;
                op1._is_some = false;
                let mut tpl = (1, true);
                tpl.0 = 2;
                let impl_res = impl_test(op1, 0);
                let aliased_opt = AliasedOpt::none();
                is_alias_some(aliased_opt);
            }
        "#,
        )
    }

    #[test]
    fn patterns() -> anyhow::Result<()> {
        print_result(
            r#"
            struct Option2<T> {
                _is_some: bool,
                _value: T,
            }

            impl <T> Option2<T> {
                /// Constructs a Some wrapper around the given value
                pub fn some(_value: T) -> Self {
                   Self { _is_some: true, _value }
                }
            }

            fn pattern_test() {
                let opt = Option2::some(true);
                let t = (1, opt, 3);
                let (x, mut Option2 { _is_some, _value }, mut z) = t;
                let lam = |(x, mut y, z) : (bool, bool, bool), k : Field| -> bool {
                    x
                };
            }
        "#,
        )
    }

    #[test]
    fn const_generics() -> anyhow::Result<()> {
        print_result(
            r#"
            fn nat_generic_test<let N: u32>() -> [Field; N] {
                for i in 0..N {
                    i;
                }
                [1; N]
            }

            fn nat_generic_test_2<let N: u8>(x: Field) -> Field {
                let mut res = x;
                for _ in 0..N {
                    res = res * 2;
                }
                res
            }
        "#,
        )
    }

    #[test]
    fn globals() -> anyhow::Result<()> {
        print_result(
            r#"
            global FOOS: [Field; 2] = [FOO, FOO + 1];

            global FOO: Field  = 42;

            fn main() -> pub Field {
                FOOS[1]
            }
        "#,
        )
    }
}
