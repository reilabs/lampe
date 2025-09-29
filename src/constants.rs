/// The contents of the included standard-library's TOML file.
pub const STDLIB_TOML: &str = include_str!("../stdlib/Nargo.toml");

/// The version used when a Nargo package does not specify a version string.
pub const NONE_DEPENDENCY_VERSION: &str = "0.0.0";

/// The path separator used by the Noir compiler when printing path-separated
/// internal names.
pub const NOIR_PATH_SEPARATOR: &str = "::";

/// Separates the name of the self type and the method defined on it.
pub const LAMPE_STRUCT_METHOD_SEPARATOR: &str = "::";

/// The name of the noir standard library Nargo package, as set in `Nargo.toml`.
pub const NOIR_STDLIB_PACKAGE_NAME: &str = "std";
