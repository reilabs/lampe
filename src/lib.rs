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

    /// This test is a bit of a mess and exists purely for experimentation.
    #[test]
    fn runs() -> anyhow::Result<()> {
        // Set up our source code
        let file_name = Path::new("main.nr");
        let source = r#"
            use std::hash::{Hash, Hasher};
            use std::cmp::{Ordering, Ord, Eq};
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

            // fn literal_test() -> () {
            //     let a = 1;
            //     let b = true;
            //     let c = false;
            //     let d = [1; 5];
            //     let e = [1, 2, 3];
            //     let f = &[];
            //     let g = "asdf";
            //     let h = f"${g}";
            // }

            // fn assigns(x: u8) {
            //     let mut y = 3;
            //     y += x;
           
            //     let mut foo = Option2::none();
            //     foo._is_some = false;
           
            //     let mut arr = [1, 2];
            //     arr[0] = 10;
            // }

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

            // fn check(x: u8) {
            //     assert(x == 5);
            // }

            // global TEST = 1 + 7 + 3;
            //
            // fn use_global() -> Field {
            //     TEST
            // }

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
                    Self { _is_some: false, _value: std::unsafe::zeroed() }
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
            }
        "#;

        let source = Source::new(file_name, source);

        // Create our project
        let project = Project::new(Path::new(""), source);

        // Execute the compilation step on our project.
        let source = noir_to_lean(project)?.take();

        println!("{source}");

        Ok(())
    }
}
