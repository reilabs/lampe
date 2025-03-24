//! A utility for extracting [Noir](https://noir-lang.org) programs to
//! equivalent definitions in the [Lean](https://lean-lang.org) theorem prover
//! and programming language.
//!
//! # Limitations
//!
//! It currently only supports single-file programs, pending further expansion
//! to support full Noir projects. The stdlib functions properly at this stage.

#![warn(clippy::all, clippy::cargo, clippy::pedantic)]

use std::{fs, fs::OpenOptions, io::Write, panic, path::PathBuf, process::ExitCode};

use clap::{arg, Parser};
use lampe::{
    error::{emit, file, Error},
    noir::source::Source,
    noir_to_lean, Project, Result,
};

/// The default Noir project path for the CLI to extract from.
const DEFAULT_NOIR_PROJECT_PATH: &str = "";

/// The default Noir filename for the CLI to extract from.
const DEFAULT_NOIR_FILE_NAME: &str = "main.nr";

/// The default output file for the generated definitions.
const DEFAULT_OUT_FILE_NAME: &str = "Main.lean";

/// The
const LEAN_HEADER: &str = "import Lampe\n\nopen Lampe\n\nnamespace Extracted\n\n";

/// A utility to extract Noir code to Lean in order to enable the formal
/// verification of Noir programs.
#[derive(Clone, Debug, Parser)]
pub struct ProgramOptions {
    /// The root of the Noir project to extract.
    #[arg(long, value_name = "PATH", default_value = DEFAULT_NOIR_PROJECT_PATH)]
    pub root: PathBuf,

    /// The specific file in the Noir project to extract.
    #[arg(long, value_name = "FILE", default_value = DEFAULT_NOIR_FILE_NAME)]
    pub file: PathBuf,

    /// The file to output the generated Lean sources to.
    #[arg(long, value_name = "FILE", default_value = DEFAULT_OUT_FILE_NAME)]
    pub out_file: PathBuf,

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
pub fn run_test_mode(args: &ProgramOptions) -> Result<ExitCode> {
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

        let source = Source::read(entry.path(), "src/main.nr")?;
        let project = Project::new(entry.path(), source);
        let emit_result = panic::catch_unwind(|| noir_to_lean(project));

        match emit_result {
            Err(panic) => {
                println!(
                    "🔴 Panic         {}\t{}",
                    entry.path().to_str().unwrap_or(""),
                    panic
                        .downcast::<String>()
                        .unwrap_or(Box::new("<no info>".to_string()))
                );
            }
            Ok(Err(Error::Emit(emit::Error::UnsupportedFeature(feature)))) => {
                println!(
                    "🟡 Unsupported   {}\t{}",
                    entry.path().to_str().unwrap_or(""),
                    feature
                );
            }
            Ok(Err(Error::Emit(err))) => {
                println!(
                    "🔴 Emit Error    {}\t{:?}",
                    entry.path().to_str().unwrap_or(""),
                    err
                );
            }
            Ok(Err(Error::Compile(_))) => {
                println!("🟡 Compile Error {}", entry.path().to_str().unwrap_or(""));
            }
            Ok(Err(Error::File(e))) => {
                println!(
                    "🟡 IO Error      {}\t{:?}",
                    entry.path().to_str().unwrap_or(""),
                    e
                );
            }
            Ok(Ok(_)) => {
                println!("🟢 Pass          {}", entry.path().to_str().unwrap_or(""));
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
pub fn run(args: &ProgramOptions) -> Result<ExitCode> {
    let source = Source::read(&args.root, &args.file)?;
    let project = Project::new(&args.root, source);

    let emit_result = noir_to_lean(project)?;
    if emit_result.has_warnings() {
        for warning in &emit_result.warnings {
            println!("{warning:?}");
        }
    }

    let mut lean_source = LEAN_HEADER.to_owned();
    lean_source.push_str(&emit_result.take());

    let mut out_file = OpenOptions::new()
        .write(true)
        .create(true)
        .truncate(true)
        .open(&args.out_file)
        .map_err(|_| lampe::error::file::Error::MissingFile(args.out_file.clone()))?;

    out_file
        .write(lean_source.as_bytes())
        .map_err(|_| lampe::error::file::Error::WritingError(args.out_file.clone()))?;

    Ok(ExitCode::SUCCESS)
}
