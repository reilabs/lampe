use crate::error::Error;
use crate::noir::WithWarnings;
use crate::{file_generator, noir};
use fm::FileManager;
use itertools::Itertools;
use nargo::package::{Dependency, Package};
use nargo::workspace::Workspace;
use nargo_toml::PackageSelection::All;
use noirc_frontend::hir::ParsedFiles;
use std::collections::HashMap;
use std::fmt::Debug;
use std::path::PathBuf;

pub struct Project {
    /// The root directory of the project
    project_root: PathBuf,

    /// Nargo object keeping the workspace data
    nargo_workspace: Workspace,

    /// Nargo object keeping loaded files
    nargo_file_manager: FileManager,

    /// Nargo object keeping parsed files
    nargo_parsed_files: ParsedFiles,
}

impl Project {
    /// Creates new Lampe project by reading Noir project.
    ///
    /// # Errors
    ///
    /// Will return `Error` if something goes wrong witch reading Noir project.
    pub fn new(project_root: PathBuf) -> Result<Self, Error> {
        // Workspace loading was done based on https://github.com/noir-lang/noir/blob/c3a43abf9be80c6f89560405b65f5241ed67a6b2/tooling/nargo_cli/src/cli/mod.rs#L180
        // It can be replaced when integrated into nargo tool.
        let toml_path = nargo_toml::get_package_manifest(&project_root)?;

        let nargo_workspace = nargo_toml::resolve_workspace_from_toml(&toml_path, All, None)?;

        let (nargo_file_manager, nargo_parsed_files) = noir::parse_workspace(&nargo_workspace);

        Ok(Self {
            project_root,
            nargo_workspace,
            nargo_file_manager,
            nargo_parsed_files,
        })
    }

    /// Extracts Noir code as Lean creating Lampe project structure in Noir project.
    ///
    /// # Errors
    ///
    /// Will return `Error` if something goes wrong witch compiling, extracting or generating files.
    pub fn extract(&self) -> Result<WithWarnings<()>, Error> {
        let noir_project = noir::Project::new(&self.nargo_file_manager, &self.nargo_parsed_files);

        let mut warnings = vec![];
        for package in &self.nargo_workspace.members {
            let with_warnings = self.extract_package(&noir_project, package)?;
            if with_warnings.has_warnings() {
                warnings.extend(with_warnings.warnings);
            }
        }
        Ok(WithWarnings::new((), warnings))
    }

    fn extract_package(
        &self,
        noir_project: &noir::Project,
        package: &Package,
    ) -> Result<WithWarnings<()>, Error> {
        let compile_result = noir_project.compile_package(package)?;
        let warnings = compile_result.warnings.clone();
        let lean_emitter = compile_result.take();
        let generated_source = lean_emitter.emit()?;

        () = file_generator::lampe_project(
            &self.nargo_workspace.root_dir,
            package,
            &HashMap::from([("Main".to_string(), generated_source)]),
        )?;

        Ok(WithWarnings::new((), warnings))
    }
}

impl Debug for Project {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fn package_fmt(
            f: &mut std::fmt::Formatter<'_>,
            p: &Package,
            tab: &str,
        ) -> std::fmt::Result {
            writeln!(f, "{}name:       {}", tab, p.name)?;
            writeln!(f, "{}version:    {:?}", tab, p.version)?;
            writeln!(f, "{}type:       {}", tab, p.package_type)?;
            writeln!(f, "{}root_dir:   {:?}", tab, p.root_dir)?;
            writeln!(f, "{}entry_path: {:?}", tab, p.entry_path)?;
            writeln!(f, "{tab}dependencies:")?;

            for (crate_name, dep) in &p.dependencies {
                match dep {
                    Dependency::Local { package } => {
                        writeln!(f, "{tab}  (Local)  Crate: {crate_name}")?;
                        package_fmt(f, package, &format!("  {tab}"))?;
                    }
                    Dependency::Remote { package } => {
                        writeln!(f, "{tab}  (Remote) Crate: {crate_name}")?;
                        package_fmt(f, package, &format!("  {tab}"))?;
                    }
                }
            }

            Ok(())
        }

        writeln!(f, "Project(")?;
        writeln!(f, "  project_root: {:?}", self.project_root)?;
        writeln!(f, "  members:")?;
        for p in &self.nargo_workspace.members {
            package_fmt(f, p, "    ")?;
        }
        writeln!(f, "  loaded_files:")?;
        let file_map = self.nargo_file_manager.as_file_map();
        for file_id in file_map.all_file_ids().sorted() {
            writeln!(
                f,
                "    file_id: {:?}, name: {:?}",
                file_id,
                file_map.get_name(*file_id).unwrap()
            )?;
        }
        writeln!(f, ")")?;

        Ok(())
    }
}
