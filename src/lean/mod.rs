//! Functionality for emitting Lean definitions from Noir source.
//!
//! Note that there are a bunch of clippy allows. This file is going away, I
//! just want to make CI not yell at me.
pub mod ast;
pub mod builtin;
pub mod emit;
pub mod generator;
