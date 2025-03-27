//! Functionality for working with projects of Noir sources.

use fm::FileManager;
use nargo::package::Package;
use nargo::workspace::Workspace;
use nargo::{insert_all_files_for_workspace_into_file_manager, parse_all, prepare_package};
use noirc_driver::{CompileOptions, check_crate};
use noirc_frontend::hir::ParsedFiles;

use crate::{
    lean::LeanEmitter,
    noir::WithWarnings,
    noir::error::compilation::{Error as CompileError, Result as CompileResult},
};

/// A manager for source files for the Noir project that we intend to extract.
#[derive(Clone)]
pub struct Project<'file_manager, 'parsed_files> {
    /// Nargo object keeping loaded files
    nargo_file_manager: &'file_manager FileManager,

    /// Nargo object keeping parsed files
    nargo_parsed_files: &'parsed_files ParsedFiles,
}

impl<'file_manager, 'parsed_files> Project<'file_manager, 'parsed_files> {
    /// Creates a new project with the provided root.
    #[allow(clippy::missing_panics_doc)]
    pub fn new(
        nargo_file_manager: &'file_manager FileManager,
        nargo_parsed_files: &'parsed_files ParsedFiles,
    ) -> Self {
        Self {
            nargo_file_manager,
            nargo_parsed_files,
        }
    }

    /// Takes the project definition and performs compilation of that project to
    /// the Noir intermediate representation for further analysis and the
    /// emission of Lean code.
    ///
    /// If the compilation process generates non-fatal warnings, these are
    /// attached to the return value.
    ///
    /// # Errors
    ///
    /// - [`CompileError`] if the compilation process fails.
    pub fn compile_package(&self, package: &Package) -> CompileResult<WithWarnings<LeanEmitter>> {
        let (mut context, crate_id) =
            prepare_package(self.nargo_file_manager, self.nargo_parsed_files, package);
        // Enables reference tracking in the internal context.
        context.activate_lsp_mode(); //

        // Perform compilation to check the code within it.
        let ((), warnings) = check_crate(
            &mut context,
            crate_id,
            &CompileOptions {
                deny_warnings: false,
                disable_macros: false,
                debug_comptime_in_file: None,
                ..Default::default()
            },
        )
        .map_err(|diagnostics| CompileError::CheckFailure { diagnostics })?;

        Ok(WithWarnings::new(
            LeanEmitter::new(context, crate_id),
            warnings,
        ))
    }
}

// Copied from: https://github.com/noir-lang/noir/blob/e93f44cd41bbc570096e6d12c652aa4c4abc5839/tooling/nargo_cli/src/cli/compile_cmd.rs#L108
/// Parse all files in the workspace.
pub fn parse_workspace(workspace: &Workspace) -> (FileManager, ParsedFiles) {
    let mut file_manager = workspace.new_file_manager();
    insert_all_files_for_workspace_into_file_manager(workspace, &mut file_manager);
    let parsed_files = parse_all(&file_manager);
    (file_manager, parsed_files)
}
