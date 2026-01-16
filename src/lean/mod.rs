//! Functionality for emitting Lean definitions from Noir source.
//!
//! Note that there are a bunch of clippy allows. This file is going away, I
//! just want to make CI not yell at me.
pub mod ast;
pub mod builtin;
pub mod emit;
pub mod generator;

/// The opening quote for use in the Lean source.
pub const LEAN_QUOTE_START: &str = "«";

/// The closing quote for use in the Lean source.
pub const LEAN_QUOTE_END: &str = "»";

/// Keywords that are built into Lean's syntax, so we need to quote them
pub const LEAN_KEYWORDS: &[&str] = &["all", "from", "meta"];

fn conflicts_with_lean_keyword(text: &str) -> bool {
    LEAN_KEYWORDS.contains(&text)
}
