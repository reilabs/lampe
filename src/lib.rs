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
