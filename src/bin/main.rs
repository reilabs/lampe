//! A utility for extracting [Noir](https://noir-lang.org) programs to
//! equivalent definitions in the [Lean](https://lean-lang.org) theorem prover
//! and programming language.
//!
//! # Limitations
//!
//! It currently only supports single-file programs, pending further expansion
//! to support full Noir projects. The stdlib functions properly at this stage.

#![warn(clippy::all, clippy::cargo, clippy::pedantic)]

use std::{fs::OpenOptions, io::Write, path::PathBuf, process::ExitCode};

use clap::{Parser, arg};
use lampe::{Project, Result, error::file, lean::EmitResult, noir::source::Source, noir_to_lean};
use walkdir::WalkDir;

/// The default Noir project path for the CLI to extract from.
const DEFAULT_NOIR_PROJECT_PATH: &str = "";

/// The default Noir filename for the CLI to extract from.
const DEFAULT_NOIR_FILE_NAME: &str = "main.nr";

/// The default output file for the generated definitions.
const DEFAULT_OUT_MODULE_NAME: &str = "Extracted";

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
    #[arg(long, value_name = "FILE", default_value = DEFAULT_OUT_MODULE_NAME)]
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

fn add_all_files(project: &mut Project) -> file::Result<()> {
    let root_path = project.project_root().to_path_buf();
    let root_file = project.root_file().to_path_buf();

    for entry in WalkDir::new(&root_path)
        .into_iter()
        .filter(|e| e.is_ok())
        .map(|e| e.unwrap())
        .filter(|e| e.file_type().is_file())
    {
        let path = entry.path();

        if let Some(extension) = path.extension() {
            if extension == "nr" {
                if let Ok(rel_path) = path.strip_prefix(&root_path) {
                    if rel_path != root_file.as_path() {
                        if let Ok(source) = Source::read(&root_path, rel_path) {
                            project.add_source(source)?;
                        }
                    }
                }
            }
        }
    }

    Ok(())
}

fn emit_file(result: &EmitResult) -> Result<()> {
    let out_path = result.file_path.clone();
    let mut out_file = OpenOptions::new()
        .write(true)
        .create(true)
        .truncate(true)
        .open(&out_path)
        .map_err(|_| lampe::error::file::Error::MissingFile(out_path.clone()))?;

    out_file
        .write(result.output.as_bytes())
        .map_err(|_| lampe::error::file::Error::WritingError(out_path))?;

    Ok(())
}

/// The main execution of the CLI utility. Should be called directly from the
/// `main` function of the application.
///
/// # Errors
///
/// - [`Error`] if the extraction process fails for any reason.
pub fn run(args: &ProgramOptions) -> Result<ExitCode> {
    let root_source = Source::read(&args.root, &args.file)?;
    let mut project = Project::new(&args.root, root_source);

    add_all_files(&mut project)?;

    let emit_result = noir_to_lean(project)?;
    if emit_result.has_warnings() {
        for warning in &emit_result.warnings {
            println!("{warning:?}");
        }
    }

    emit_result.data.iter().for_each(|result| {
        emit_file(result).unwrap(); // TODO: Handle errors properly.
    });

    // let mut lean_source = LEAN_HEADER.to_owned();
    // lean_source.push_str(&emit_result.take());

    // let mut out_file = OpenOptions::new()
    //     .write(true)
    //     .create(true)
    //     .truncate(true)
    //     .open(&args.out_file)
    //     .map_err(|_| lampe::error::file::Error::MissingFile(args.out_file.clone()))?;

    // out_file
    //     .write(lean_source.as_bytes())
    //     .map_err(|_| lampe::error::file::Error::WritingError(args.out_file.clone()))?;

    Ok(ExitCode::SUCCESS)
}
