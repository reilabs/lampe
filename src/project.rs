use std::{collections::HashMap, fmt::Debug, path::PathBuf};

use fm::FileManager;
use itertools::Itertools;
use nargo::{
    package::{Dependency, Package},
    workspace::Workspace,
};
use nargo_toml::{Config, PackageSelection::All};
use noirc_frontend::hir::ParsedFiles;

use crate::{
    error::Error,
    file_generator,
    file_generator::{lake::dependency::LeanDependency, LeanFile, NoirPackageIdentifier},
    noir,
    noir::WithWarnings,
};

const NONE_DEPENDENCY_VERSION: &str = "0.0.0";

pub struct Project {
    /// The root directory of the Noir project
    project_root: PathBuf,
    
    /// The directory where put the Lampe project
    target_path: PathBuf,

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
    pub fn new(project_root: PathBuf, target_path: PathBuf) -> Result<Self, Error> {
        // Workspace loading was done based on https://github.com/noir-lang/noir/blob/c3a43abf9be80c6f89560405b65f5241ed67a6b2/tooling/nargo_cli/src/cli/mod.rs#L180
        // It can be replaced when integrated into nargo tool.
        let toml_path = nargo_toml::get_package_manifest(&project_root)?;

        let nargo_workspace = nargo_toml::resolve_workspace_from_toml(&toml_path, All, None)?;

        let (nargo_file_manager, nargo_parsed_files) = noir::parse_workspace(&nargo_workspace);

        Ok(Self {
            project_root,
            target_path,
            nargo_workspace,
            nargo_file_manager,
            nargo_parsed_files,
        })
    }

    /// Extracts Noir code as Lean creating Lampe project structure in Noir
    /// project.
    ///
    /// # Errors
    ///
    /// Will return `Error` if something goes wrong witch compiling, extracting
    /// or generating files.
    pub fn extract(&self) -> Result<WithWarnings<()>, Error> {
        let noir_project = noir::Project::new(&self.nargo_file_manager, &self.nargo_parsed_files);

        let mut warnings = vec![];
        for package in &self.nargo_workspace.members {
            let with_warnings = self.extract_package(&noir_project, package)?;
            if with_warnings.has_warnings() {
                warnings.extend(with_warnings.warnings);
            }

            let with_warnings = Self::extract_dependencies_without_lampe(&noir_project, package)?;
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
        let package_name = &package.name.to_string();
        let package_version =
            &package.version.clone().unwrap_or(NONE_DEPENDENCY_VERSION.to_string());

        let mut warnings = vec![];

        let res = Self::compile_package(noir_project, package)?;
        warnings.extend(res.warnings);
        let extracted_code = res.data;

        let additional_dependencies = Self::get_dependencies_with_lampe(package)?;

        let res = Self::extract_dependencies_without_lampe(noir_project, package)?;
        warnings.extend(res.warnings);
        let extracted_dependencies = res.data;

        file_generator::lampe_project(
            &self.target_path,
            &NoirPackageIdentifier {
                name:    package_name.clone(),
                version: package_version.clone(),
            },
            &additional_dependencies,
            &extracted_code,
            extracted_dependencies,
        )?;

        Ok(WithWarnings::new((), warnings))
    }

    fn get_dependencies_with_lampe(
        package: &Package,
    ) -> Result<Vec<Box<dyn LeanDependency>>, Error> {
        let mut result = vec![];

        let toml_path = nargo_toml::get_package_manifest(&package.root_dir)?;
        let nargo_toml = nargo_toml::read_toml(&toml_path)?;
        let package_config = match nargo_toml.config {
            Config::Package { package_config } => package_config,
            Config::Workspace { .. } => Err(nargo_toml::ManifestError::UnexpectedWorkspace(
                nargo_toml.root_dir,
            ))?,
        };

        for (crate_name, dependency) in &package.dependencies {
            let dependency_name = &crate_name.to_string();
            let dependency_config = package_config.dependencies.get(dependency_name).ok_or(
                Error::MissingDependencyError {
                    package_name:    package.name.to_string().clone(),
                    package_version: package.version.clone(),
                    dependency_name: dependency_name.clone(),
                },
            )?;

            let package = match dependency {
                Dependency::Local { package } | Dependency::Remote { package } => package,
            };

            if !file_generator::has_lampe(package) {
                continue;
            }

            let lean_dependency_name = file_generator::read_lampe_package_name(package)?;

            result.push(file_generator::get_lean_dependency(
                &lean_dependency_name,
                dependency_config,
            )?);
        }

        Ok(result)
    }

    fn extract_dependencies_without_lampe(
        noir_project: &noir::Project,
        package: &Package,
    ) -> Result<WithWarnings<HashMap<NoirPackageIdentifier, Vec<LeanFile>>>, Error> {
        let mut warnings = vec![];
        let mut result = HashMap::new();

        let res = Self::do_extract_dependencies_without_lampe(noir_project, package, &mut result)?;
        warnings.extend(res.warnings);

        Ok(WithWarnings::new(result, warnings))
    }

    fn do_extract_dependencies_without_lampe(
        noir_project: &noir::Project,
        package: &Package,
        extracted_dependencies: &mut HashMap<NoirPackageIdentifier, Vec<LeanFile>>,
    ) -> Result<WithWarnings<()>, Error> {
        let mut warnings = vec![];

        for dependency in package.dependencies.values() {
            let package = match dependency {
                Dependency::Local { package } | Dependency::Remote { package } => package,
            };

            if file_generator::has_lampe(package) {
                continue;
            }

            let package_identitifer = NoirPackageIdentifier {
                name:    package.name.to_string(),
                version: package.version.clone().unwrap_or(NONE_DEPENDENCY_VERSION.to_string()),
            };

            if extracted_dependencies.contains_key(&package_identitifer) {
                continue;
            }

            let res = Self::compile_package(noir_project, package)?;
            warnings.extend(res.warnings);

            extracted_dependencies.insert(package_identitifer, res.data);

            let res = Self::do_extract_dependencies_without_lampe(
                noir_project,
                package,
                extracted_dependencies,
            )?;
            warnings.extend(res.warnings);
        }

        Ok(WithWarnings::new((), warnings))
    }

    fn compile_package(
        noir_project: &noir::Project,
        package: &Package,
    ) -> Result<WithWarnings<Vec<LeanFile>>, Error> {
        let compile_result = noir_project.compile_package(package)?;
        let warnings = compile_result.warnings.clone();
        let lean_emitter = compile_result.take();
        let generated_source = lean_emitter.emit()?;

        let mut lean_files = generated_source
            .decl_contents
            .iter()
            .map(|(id, content)| -> Result<LeanFile, Error> {
                Ok(LeanFile::from_user_noir_file(
                    noir_project.file_manager().path(*id).ok_or(
                        noir::error::file::Error::Other(format!("Unknown file ID: {id:?}")),
                    )?,
                    content.clone(),
                )
                .map_err(file_generator::error::Error::from)?)
            })
            .collect::<Result<Vec<_>, _>>()?;

        lean_files.push(LeanFile::from_generated_types(
            generated_source.type_content,
        ));

        Ok(WithWarnings::new(lean_files, warnings))
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
