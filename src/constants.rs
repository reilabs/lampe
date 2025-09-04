/// The contents of the included standard-library's TOML file.
pub const STDLIB_TOML: &str = include_str!("../stdlib/Nargo.toml");

/// The version used when a Nargo package does not specify a version string.
pub const NONE_DEPENDENCY_VERSION: &str = "0.0.0";

/// The path separator used by the Noir compiler when printing path-separated
/// internal names.
pub const NOIR_PATH_SEPARATOR: &str = "::";

/// The path separator we want to use for namespaced names generated in the Lean
/// DSL.
pub const LAMPE_PATH_SEPARATOR: &str = ".";

/// The key needed to access the root namespace in Lean, allowing unambiguous
/// use of namespace-qualified names.
pub const LEAN_ROOT_NAMESPACE_KEY: &str = "_root_";

/// Separates the name of the self type and the method defined on it.
pub const LAMPE_STRUCT_METHOD_SEPARATOR: &str = "::";
