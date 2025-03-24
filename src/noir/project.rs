//! Functionality for working with projects of Noir sources.

use std::{
    collections::HashSet,
    path::{Path, PathBuf},
};

use fm::{FileId, FileManager};
use nargo::parse_all;
use noirc_driver::{check_crate, file_manager_with_stdlib, prepare_crate, CompileOptions};
use noirc_frontend::hir::Context;

use crate::{
    error::{
        compilation::{Error as CompileError, Result as CompileResult},
        file::{Error as FileError, Result as FileResult},
    },
    lean::LeanEmitter,
    noir::{source::Source, WithWarnings},
};

/// A type for file identifiers that are known to the extraction process.
pub type KnownFiles = HashSet<FileId>;

/// A manager for source files for the Noir project that we intend to extract.
#[derive(Clone, Debug)]
pub struct Project {
    /// The internal file manager for the Noir project.
    manager: FileManager,

    /// The root directory of the project
    project_root: PathBuf,

    /// The root file name for the project.
    root_file_name: PathBuf,

    /// The files that were explicitly added to the compilation project.
    ///
    /// Namely, this will contain the file IDs for files added manually during
    /// extraction tool execution, and not identifiers for files in the standard
    /// library and other implicit libraries.
    known_files: KnownFiles,
}

impl Project {
    /// Creates a new project with the provided root.
    #[allow(clippy::missing_panics_doc)]
    pub fn new(root: impl Into<PathBuf>, root_file: Source) -> Self {
        let project_root = root.into();
        let manager = file_manager_with_stdlib(&project_root);
        let root_file_name = root_file.name.clone();
        let file_ids = KnownFiles::new();

        let mut project = Self {
            manager,
            project_root,
            root_file_name,
            known_files: file_ids,
        };

        // The panic should be impossible.
        project
            .add_source(root_file)
            .expect("The project has been newly created, so we can always add the root file.");

        project
    }

    /// Adds the provided `source` to the Noir project.
    ///
    /// # Errors
    ///
    /// - [`FileError::DuplicateFile`] if the provided file already exists in
    ///   the project.
    pub fn add_source(&mut self, source: Source) -> FileResult<()> {
        let file_id = self
            .manager
            .add_file_with_source(source.name.as_path(), source.contents)
            .ok_or(FileError::DuplicateFile(source.name))?;

        self.known_files.insert(file_id);

        Ok(())
    }

    /// Adds the provided `sources` to the Noir project.
    ///
    /// # Errors
    ///
    /// - [`FileError::DuplicateFile`] if any of the provided sources already
    ///   exists in the project.
    pub fn add_sources(&mut self, sources: impl Iterator<Item = Source>) -> FileResult<()> {
        for source in sources {
            self.add_source(source)?;
        }

        Ok(())
    }

    /// Gets the root file of the project as a Path.
    #[must_use]
    pub fn root_file(&self) -> &Path {
        self.root_file_name.as_path()
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
    pub fn compile(self) -> CompileResult<WithWarnings<LeanEmitter>> {
        // Grab all required fields from `self`.
        let root_path = self.root_file_name;
        let manager = self.manager;
        let known_files = self.known_files;

        // Start by parsing the files that the file manager knows about.
        let parsed_files = parse_all(&manager);

        // Then we build our compilation context
        let mut context = Context::new(manager, parsed_files);
        context.activate_lsp_mode();
        let root_crate = prepare_crate(&mut context, self.project_root.join(root_path).as_path());

        // Perform compilation to check the code within it.
        let ((), warnings) = check_crate(
            &mut context,
            root_crate,
            &CompileOptions {
                deny_warnings: false,
                disable_macros: false,
                debug_comptime_in_file: None,
                ..Default::default()
            },
        )
        .map_err(|diagnostics| CompileError::CheckFailure { diagnostics })?;

        Ok(WithWarnings::new(
            LeanEmitter::new(context, known_files, root_crate),
            warnings,
        ))
    }
}

impl From<Project> for FileManager {
    fn from(value: Project) -> Self {
        value.manager
    }
}
