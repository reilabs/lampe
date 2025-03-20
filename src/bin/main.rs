//! A utility for extracting [Noir](https://noir-lang.org) programs to
//! equivalent definitions in the [Lean](https://lean-lang.org) theorem prover
//! and programming language.
//!
//! # Limitations
//!
//! It currently only supports single-file programs, pending further expansion
//! to support full Noir projects. The stdlib functions properly at this stage.

#![warn(clippy::all, clippy::cargo, clippy::pedantic)]

use std::{fs, panic, path::PathBuf, process::ExitCode};

use clap::{Parser, arg};
use lampe::{noir_error, Error, Project};
use lampe::noir_error::file;

/// The default Noir project path for the CLI to extract from.
const DEFAULT_NOIR_PROJECT_PATH: &str = "./";

/// A utility to extract Noir code to Lean in order to enable the formal
/// verification of Noir programs.
#[derive(Clone, Debug, Parser)]
pub struct ProgramOptions {
    /// The root of the Noir project to extract.
    #[arg(long, value_name = "PATH", default_value = DEFAULT_NOIR_PROJECT_PATH)]
    pub root: PathBuf,

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
            eprintln!("Error Encountered: {err}");
            ExitCode::FAILURE
        })
    }
}

/// A particular testing mode for the main function used to run through Noir frontend tests
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

        let project = Project::new(entry.path());
        let result = panic::catch_unwind(|| project.extract());

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
                println!("🟡 Compile Error         {}", entry.path().to_str().unwrap_or(""));
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
            Ok(Ok(_)) => {
                println!("🟢 Pass                  {}", entry.path().to_str().unwrap_or(""));
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
    let project = Project::new(args.root.clone());

    let result = project.extract()?;

    if result.has_warnings() {
        for warning in &result.warnings {
            eprintln!("{warning:?}");
        }
    }

    Ok(ExitCode::SUCCESS)
}
