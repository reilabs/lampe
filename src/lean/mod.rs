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

/// Keywords that are built into Lean's syntax, so we need to quote them.
///
/// This list covers Lean 4 reserved words and tokens that the lexer does not
/// recognise as `ident`. Variable names, type-path segments, and any other
/// user-facing identifiers that collide with these must be wrapped in `«»`.
pub const LEAN_KEYWORDS: &[&str] = &[
    // Lean 4 command / declaration keywords
    "abbrev",
    "axiom",
    "class",
    "constant",
    "def",
    "deriving",
    "do",
    "else",
    "end",
    "example",
    "extends",
    "for",
    "fun",
    "if",
    "import",
    "in",
    "inductive",
    "instance",
    "let",
    "macro",
    "match",
    "meta",
    "module",
    "mutual",
    "namespace",
    "noncomputable",
    "notation",
    "opaque",
    "open",
    "partial",
    "private",
    "protected",
    "return",
    "section",
    "set_option",
    "structure",
    "syntax",
    "tactic",
    "theorem",
    "then",
    "try",
    "universe",
    "unsafe",
    "variable",
    "where",
    // Additional identifiers that Lean treats specially
    "all",
    "from",
    "have",
    "show",
    "suffices",
    "assume",
    "by",
    "at",
    "catch",
    "finally",
    "unless",
    "with",
    "Type",
    "Prop",
    "Sort",
    "true",
    "false",
];

fn conflicts_with_lean_keyword(text: &str) -> bool {
    LEAN_KEYWORDS.contains(&text)
}
