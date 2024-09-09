//! A utility for extracting [Noir](https://noir-lang.org) programs to
//! equivalent definitions in the [Lean](https://lean-lang.org) theorem prover
//! and programming language.
//!
//! # Limitations
//!
//! It currently only supports single-file programs, pending further expansion
//! to support full Noir projects. The stdlib functions properly at this stage.

#![warn(clippy::all, clippy::cargo, clippy::pedantic)]

use std::{fs::File, io::Write, path::PathBuf, process::ExitCode};

use clap::{arg, Parser};
use lampe::{noir::source::Source, noir_to_lean, Project, Result};

/// The default Noir project path for the CLI to extract from.
const DEFAULT_NOIR_PROJECT_PATH: &str = "";

/// The default Noir filename for the CLI to extract from.
const DEFAULT_NOIR_FILE_NAME: &str = "main.nr";

/// The default output file for the generated definitions.
const DEFAULT_OUT_FILE_NAME: &str = "Main.lean";

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
}

/// The main function for the CLI utility, responsible for parsing program
/// options and handing them off to the actual execution of the tool.
fn main() -> ExitCode {
    // Parse args and hand-off immediately.
    let args = ProgramOptions::parse();
    run(&args).unwrap_or_else(|err| {
        eprintln!("Error Encountered: {err}");
        ExitCode::FAILURE
    })
}

/// The main execution of the CLI utility. Should be called directly from the
/// `main` function of the application.
///
/// # Errors
///
/// - [`Error`] if the extraction process fails for any reason.
pub fn run(args: &ProgramOptions) -> Result<ExitCode> {
    let source = Source::read(&args.file)?;
    let project = Project::new(&args.root, source);

    let emit_result = noir_to_lean(project)?;
    if emit_result.has_warnings() {
        for warning in &emit_result.warnings {
            println!("{warning:?}");
        }
    }

    let lean_source = emit_result.take();
    let mut out_file = File::open(&args.out_file)
        .map_err(|_| lampe::error::file::Error::MissingFile(args.out_file.clone()))?;
    out_file
        .write(lean_source.as_bytes())
        .map_err(|_| lampe::error::file::Error::MissingFile(args.out_file.clone()))?;

    Ok(ExitCode::SUCCESS)
}
