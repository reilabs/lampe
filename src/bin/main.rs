//! A utility for extracting [Noir](https://noir-lang.org) programs to
//! equivalent definitions in the [Lean](https://lean-lang.org) theorem prover
//! and programming language.
//!
//! # Limitations
//!
//! It currently only supports single-file programs, pending further expansion
//! to support full Noir projects. The stdlib functions properly at this stage.

#![warn(clippy::all, clippy::cargo, clippy::pedantic)]
// These occur in our Noir dependencies and cannot be avoided.
#![allow(clippy::multiple_crate_versions)]

use std::{fs, panic, path::PathBuf, process::ExitCode};

use clap::{arg, Parser};
use lampe::{noir_error, noir_error::file, Error, Project};

/// The default Noir project path for the CLI to extract from.
const DEFAULT_NOIR_PROJECT_PATH: &str = "./";

/// A utility to extract Noir code to Lean in order to enable the formal
/// verification of Noir programs.
#[derive(Clone, Debug, Parser)]
pub struct ProgramOptions {
    /// The root of the Noir project to extract.
    #[arg(long, value_name = "PATH", default_value = DEFAULT_NOIR_PROJECT_PATH, value_parser = parse_path)]
    pub root: PathBuf,

    /// The root of the Lampe project output.
    #[arg(long, value_name = "TARGET", value_parser = parse_path)]
    pub target: Option<PathBuf>,

    /// Testing mode?
    #[arg(long)]
    pub test_mode: bool,
}

/// The main function for the CLI utility, responsible for parsing program
/// options and handing them off to the actual execution of the tool.
fn main() -> ExitCode {
    // Parse args and hand-off immediately.
    let args = ProgramOptions::parse();
    if args.test_mode {
        run_test_mode(&args).unwrap_or_else(|err| {
            eprintln!("Error Encountered: {err}");
            ExitCode::FAILURE
        })
    } else {
        run(&args).unwrap_or_else(|err| {
            eprintln!("Error Encountered: {err:?}");
            ExitCode::FAILURE
        })
    }
}

/// A particular testing mode for the main function used to run through Noir
/// frontend tests
///
/// # Errors
///
/// - [`Error`] If the source directory is not readable
pub fn run_test_mode(args: &ProgramOptions) -> Result<ExitCode, Error> {
    let list = fs::read_dir(&args.root).map_err(|_| {
        file::Error::Other(format!(
            "Unable to read directory {:?}",
            args.root.as_os_str()
        ))
    })?;

    for entry in list {
        let entry =
            entry.map_err(|err| file::Error::Other(format!("Unable to read entry: {err:?}")))?;
        if !entry
            .metadata()
            .map_err(|_| {
                file::Error::Other(format!(
                    "Unable to read metadata of {:?}",
                    entry.file_name()
                ))
            })?
            .is_dir()
        {
            continue;
        }

        let result = panic::catch_unwind(|| Project::new(entry.path(), entry.path())?.extract());

        match result {
            Err(panic) => {
                println!(
                    "🔴 Panic                 {}\t{}",
                    entry.path().to_str().unwrap_or(""),
                    panic
                        .downcast::<String>()
                        .unwrap_or(Box::new("<no info>".to_string()))
                );
            }
            Ok(Err(Error::EmitError(noir_error::emit::Error::UnsupportedFeature(feature)))) => {
                println!(
                    "🟡 Unsupported           {}\t{}",
                    entry.path().to_str().unwrap_or(""),
                    feature
                );
            }
            Ok(Err(Error::EmitError(err))) => {
                println!(
                    "🔴 Emit Error            {}\t{:?}",
                    entry.path().to_str().unwrap_or(""),
                    err
                );
            }
            Ok(Err(Error::CompilationError(_))) => {
                println!(
                    "🟡 Compile Error         {}",
                    entry.path().to_str().unwrap_or("")
                );
            }
            Ok(Err(Error::FileError(err))) => {
                println!(
                    "🟡 IO Error              {}\t{:?}",
                    entry.path().to_str().unwrap_or(""),
                    err
                );
            }
            Ok(Err(Error::FileGenerationError(err))) => {
                println!(
                    "🟡 File generating error {}\t{:?}",
                    entry.path().to_str().unwrap_or(""),
                    err
                );
            }
            Ok(Err(Error::NoirProjectError(err))) => {
                println!(
                    "🟡 Noir project error    {}\t{:?}",
                    entry.path().to_str().unwrap_or(""),
                    err
                );
            }
            Ok(Err(err)) => {
                println!("🟡 Error                 {err:?}");
            }
            Ok(Ok(_)) => {
                println!(
                    "🟢 Pass                  {}",
                    entry.path().to_str().unwrap_or("")
                );
            }
        }
    }
    Ok(ExitCode::SUCCESS)
}

/// The main execution of the CLI utility. Should be called directly from the
/// `main` function of the application.
///
/// # Errors
///
/// - [`Error`] if the extraction process fails for any reason.
pub fn run(args: &ProgramOptions) -> Result<ExitCode, Error> {
    let noir_root_path = args.root.clone();
    let target_path = args.target.clone().unwrap_or(noir_root_path.clone());
    let project = Project::new(noir_root_path, target_path)?;

    let result = project.extract()?;

    if result.has_warnings() {
        for warning in &result.warnings {
            eprintln!("{warning:?}");
        }
    }

    Ok(ExitCode::SUCCESS)
}

// Copied from: https://github.com/noir-lang/noir/blob/5071093f9b51e111a49a5f78d827774ef8e80c74/tooling/nargo_cli/src/cli/mod.rs#L301
/// Parses a path and turns it into an absolute one by joining to the current
/// directory.
fn parse_path(path: &str) -> Result<PathBuf, String> {
    use fm::NormalizePath;
    let mut path: PathBuf = path.parse().map_err(|e| format!("failed to parse path: {e}"))?;
    if !path.is_absolute() {
        path = std::env::current_dir().unwrap().join(path).normalize();
    }
    Ok(path)
}
