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
    constants::NONE_DEPENDENCY_VERSION,
    error::Error,
    file_generator::{
        self,
        lake::dependency::{LeanDependency, LeanDependencyPath},
        DependencyInfo,
        LeanFile,
        NoirPackageIdentifier,
    },
    lean::emit::{ModuleEmitter, TypesEmitter},
    noir::{self, WithWarnings},
};

pub struct Project {
    /// The root directory of the Noir project
    project_root: PathBuf,

    /// The directory where put the Lampe project
    target_path: PathBuf,

    /// Nargo object keeping the workspace data
    pub nargo_workspace: Workspace,

    /// Nargo object keeping loaded files
    pub nargo_file_manager: FileManager,

    /// Nargo object keeping parsed files
    pub nargo_parsed_files: ParsedFiles,
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
    pub fn extract(&self, ovewrite: bool) -> Result<WithWarnings<()>, Error> {
        let noir_project = noir::Project::new(&self.nargo_file_manager, &self.nargo_parsed_files);

        let mut warnings = vec![];
        for package in &self.nargo_workspace.members {
            let with_warnings =
                self.extract_package_with_all_dependencies(&noir_project, package, ovewrite)?;
            if with_warnings.has_warnings() {
                warnings.extend(with_warnings.warnings);
            }
        }
        Ok(WithWarnings::new((), warnings))
    }

    /// Extracts a package along with all its transitive dependencies that don't
    /// have lampe directories. Dependencies are extracted to the deps/
    /// subdirectory.
    fn extract_package_with_all_dependencies(
        &self,
        noir_project: &noir::Project,
        package: &Package,
        ovewrite: bool,
    ) -> Result<WithWarnings<()>, Error> {
        let mut warnings = vec![];

        // Collect all dependencies and their relationships in one pass
        let mut all_dependencies_to_extract = HashMap::new();
        let mut direct_dependencies_to_extract = HashMap::new();
        let mut dependency_relationships = HashMap::new();

        let res = self.collect_all_dependencies_with_relationships(
            noir_project,
            package,
            &mut all_dependencies_to_extract,
            &mut direct_dependencies_to_extract,
            &mut dependency_relationships,
        )?;
        warnings.extend(res.warnings);

        // Extract the main package with all collected dependencies
        let res = self.extract_package_with_deps(
            noir_project,
            package,
            &all_dependencies_to_extract,
            &direct_dependencies_to_extract,
            &dependency_relationships,
            ovewrite,
        )?;
        warnings.extend(res.warnings);

        Ok(WithWarnings::new((), warnings))
    }

    /// Extracts a package with pre-collected dependencies
    fn extract_package_with_deps(
        &self,
        noir_project: &noir::Project,
        package: &Package,
        extracted_dependencies: &HashMap<NoirPackageIdentifier, Vec<LeanFile>>,
        direct_dependencies: &HashMap<NoirPackageIdentifier, Vec<LeanFile>>,
        dependency_relationships: &HashMap<
            NoirPackageIdentifier,
            (Vec<NoirPackageIdentifier>, Vec<NoirPackageIdentifier>),
        >,
        ovewrite: bool,
    ) -> Result<WithWarnings<()>, Error> {
        let package_name = &package.name.to_string();
        let package_version =
            &package.version.clone().unwrap_or(NONE_DEPENDENCY_VERSION.to_string());

        let mut warnings = vec![];

        let res = self.compile_package(noir_project, package)?;
        warnings.extend(res.warnings);
        let extracted_code = res.data;

        let additional_dependencies = Self::get_dependencies_with_lampe(package)?;

        // Collect direct dependencies that already have lampe
        let direct_dependencies_with_lampe = Self::collect_direct_dependencies_with_lampe(package);

        // Add path-based dependencies for the direct extracted dependencies only
        let path_dependencies =
            Self::create_path_dependencies_for_extracted_deps(direct_dependencies);
        let mut all_dependencies = additional_dependencies;
        all_dependencies.extend(path_dependencies);

        let dependency_info = DependencyInfo {
            all_dependencies,
            extracted_dependencies: extracted_dependencies.clone(),
            direct_dependencies: direct_dependencies.clone(),
            direct_dependencies_with_lampe: direct_dependencies_with_lampe.clone(),
            dependency_relationships: dependency_relationships.clone(),
        };

        file_generator::lampe_project(
            &self.target_path,
            &NoirPackageIdentifier {
                name:    package_name.clone(),
                version: package_version.clone(),
            },
            &dependency_info,
            &extracted_code,
            ovewrite,
        )?;

        Ok(WithWarnings::new((), warnings))
    }

    /// Creates path-based lean dependencies for the extracted dependencies
    fn create_path_dependencies_for_extracted_deps(
        all_dependencies: &HashMap<NoirPackageIdentifier, Vec<LeanFile>>,
    ) -> Vec<Box<dyn LeanDependency>> {
        let mut result = vec![];

        for dep_identifier in all_dependencies.keys() {
            let dep_name = format!("{}-{}", dep_identifier.name, dep_identifier.version);
            let dep_path = format!("deps/{dep_name}/lampe");

            result.push(
                Box::new(LeanDependencyPath::builder(&dep_name).path(&dep_path).build())
                    as Box<dyn LeanDependency>,
            );
        }

        result
    }

    /// Collects all dependencies and their relationships
    fn collect_all_dependencies_with_relationships(
        &self,
        noir_project: &noir::Project,
        package: &Package,
        all_dependencies: &mut HashMap<NoirPackageIdentifier, Vec<LeanFile>>,
        direct_dependencies: &mut HashMap<NoirPackageIdentifier, Vec<LeanFile>>,
        dependency_relationships: &mut HashMap<
            NoirPackageIdentifier,
            (Vec<NoirPackageIdentifier>, Vec<NoirPackageIdentifier>),
        >,
    ) -> Result<WithWarnings<()>, Error> {
        let mut warnings = vec![];

        let res = self.collect_direct_dependencies_without_lampe(
            noir_project,
            package,
            direct_dependencies,
        )?;
        warnings.extend(res.warnings);

        let res =
            self.collect_all_dependencies_without_lampe(noir_project, package, all_dependencies)?;
        warnings.extend(res.warnings);

        let res = self.collect_dependencies_relationships_recursive(
            noir_project,
            package,
            all_dependencies,
            dependency_relationships,
        )?;
        warnings.extend(res.warnings);

        Ok(WithWarnings::new((), warnings))
    }

    /// Collect dependency relationships by traversing the dependency graph
    fn collect_dependencies_relationships_recursive(
        &self,
        noir_project: &noir::Project,
        root_package: &Package,
        all_dependencies: &HashMap<NoirPackageIdentifier, Vec<LeanFile>>,
        dependency_relationships: &mut HashMap<
            NoirPackageIdentifier,
            (Vec<NoirPackageIdentifier>, Vec<NoirPackageIdentifier>),
        >,
    ) -> Result<WithWarnings<()>, Error> {
        let mut warnings = vec![];
        let mut visited = std::collections::HashSet::new();

        let res = self.collect_package_dependencies(
            noir_project,
            root_package,
            all_dependencies,
            dependency_relationships,
            &mut visited,
        )?;
        warnings.extend(res.warnings);

        Ok(WithWarnings::new((), warnings))
    }

    /// Collects dependencies for a package
    fn collect_package_dependencies(
        &self,
        noir_project: &noir::Project,
        package: &Package,
        all_dependencies: &HashMap<NoirPackageIdentifier, Vec<LeanFile>>,
        dependency_relationships: &mut HashMap<
            NoirPackageIdentifier,
            (Vec<NoirPackageIdentifier>, Vec<NoirPackageIdentifier>),
        >,
        visited: &mut std::collections::HashSet<NoirPackageIdentifier>,
    ) -> Result<WithWarnings<()>, Error> {
        let mut warnings = vec![];

        for dependency in package.dependencies.values() {
            let dep_package = match dependency {
                Dependency::Local { package } | Dependency::Remote { package } => package,
            };

            let dep_id = NoirPackageIdentifier {
                name:    dep_package.name.to_string(),
                version: dep_package
                    .version
                    .clone()
                    .unwrap_or(NONE_DEPENDENCY_VERSION.to_string()),
            };

            if all_dependencies.contains_key(&dep_id) && !visited.contains(&dep_id) {
                visited.insert(dep_id.clone());

                let mut direct_deps_without_lampe = HashMap::new();
                let res = self.collect_direct_dependencies_without_lampe(
                    noir_project,
                    dep_package,
                    &mut direct_deps_without_lampe,
                )?;
                warnings.extend(res.warnings);

                let direct_deps_with_lampe =
                    Self::collect_direct_dependencies_with_lampe(dep_package);

                let direct_deps_ids: Vec<NoirPackageIdentifier> =
                    direct_deps_without_lampe.keys().cloned().collect();

                dependency_relationships
                    .insert(dep_id.clone(), (direct_deps_ids, direct_deps_with_lampe));

                let res = self.collect_package_dependencies(
                    noir_project,
                    dep_package,
                    all_dependencies,
                    dependency_relationships,
                    visited,
                )?;
                warnings.extend(res.warnings);
            }
        }

        Ok(WithWarnings::new((), warnings))
    }

    /// Collects direct dependencies that already have lampe directories
    fn collect_direct_dependencies_with_lampe(package: &Package) -> Vec<NoirPackageIdentifier> {
        let mut result = vec![];

        for dependency in package.dependencies.values() {
            let dep_package = match dependency {
                Dependency::Local { package } | Dependency::Remote { package } => package,
            };

            if !file_generator::has_lampe(dep_package) {
                continue;
            }

            let package_identifier = NoirPackageIdentifier {
                name:    dep_package.name.to_string(),
                version: dep_package
                    .version
                    .clone()
                    .unwrap_or(NONE_DEPENDENCY_VERSION.to_string()),
            };

            result.push(package_identifier);
        }

        result
    }

    /// Collects only direct dependencies that don't have lampe directories
    fn collect_direct_dependencies_without_lampe(
        &self,
        noir_project: &noir::Project,
        package: &Package,
        direct_dependencies: &mut HashMap<NoirPackageIdentifier, Vec<LeanFile>>,
    ) -> Result<WithWarnings<()>, Error> {
        let mut warnings = vec![];

        for dependency in package.dependencies.values() {
            let dep_package = match dependency {
                Dependency::Local { package } | Dependency::Remote { package } => package,
            };

            if file_generator::has_lampe(dep_package) {
                continue;
            }

            let package_identifier = NoirPackageIdentifier {
                name:    dep_package.name.to_string(),
                version: dep_package
                    .version
                    .clone()
                    .unwrap_or(NONE_DEPENDENCY_VERSION.to_string()),
            };

            if direct_dependencies.contains_key(&package_identifier) {
                continue;
            }

            // Only compile this dependency, don't recurse into its dependencies
            let res = self.compile_package(noir_project, dep_package)?;
            warnings.extend(res.warnings);

            direct_dependencies.insert(package_identifier, res.data);
        }

        Ok(WithWarnings::new((), warnings))
    }

    /// Collects all transitive dependencies that don't have lampe directories
    fn collect_all_dependencies_without_lampe(
        &self,
        noir_project: &noir::Project,
        package: &Package,
        all_dependencies: &mut HashMap<NoirPackageIdentifier, Vec<LeanFile>>,
    ) -> Result<WithWarnings<()>, Error> {
        let mut warnings = vec![];

        for dependency in package.dependencies.values() {
            let dep_package = match dependency {
                Dependency::Local { package } | Dependency::Remote { package } => package,
            };

            if file_generator::has_lampe(dep_package) {
                continue;
            }

            let package_identifier = NoirPackageIdentifier {
                name:    dep_package.name.to_string(),
                version: dep_package
                    .version
                    .clone()
                    .unwrap_or(NONE_DEPENDENCY_VERSION.to_string()),
            };

            if all_dependencies.contains_key(&package_identifier) {
                continue;
            }

            // First recursively collect transitive dependencies
            let res = self.collect_all_dependencies_without_lampe(
                noir_project,
                dep_package,
                all_dependencies,
            )?;
            warnings.extend(res.warnings);

            // Then compile and add this dependency
            let res = self.compile_package(noir_project, dep_package)?;
            warnings.extend(res.warnings);

            all_dependencies.insert(package_identifier, res.data);
        }

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

    fn compile_package(
        &self,
        noir_project: &noir::Project,
        package: &Package,
    ) -> Result<WithWarnings<Vec<LeanFile>>, Error> {
        let compile_result = noir_project.compile_package(package, &self.nargo_workspace)?;
        let warnings = compile_result.warnings.clone();
        let lean_generator = compile_result.take();
        let generated_program = lean_generator.generate();

        let mut lean_files = generated_program
            .modules
            .iter()
            .map(|module| {
                let file_path = noir_project
                    .file_manager()
                    .path(module.id)
                    .unwrap_or_else(|| panic!("Unknown file ID: {:?}", module.id));

                let package_name = &package.name.to_string();
                let package_version =
                    &package.version.clone().unwrap_or(NONE_DEPENDENCY_VERSION.to_string());
                let package_id = NoirPackageIdentifier {
                    name:    package_name.clone(),
                    version: package_version.clone(),
                };

                let content = ModuleEmitter::new(package_id, module.clone()).emit();
                LeanFile::from_user_noir_file(file_path, content).unwrap_or_else(|_| {
                    panic!(
                        "Unable to create file at {}",
                        file_path.to_str().unwrap_or("Unknown")
                    )
                })
            })
            .collect_vec();

        lean_files.push(LeanFile::from_generated_types(
            TypesEmitter::new(generated_program.types.clone()).emit(),
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
            writeln!(f, "{}root_dir:   {}", tab, p.root_dir.display())?;
            writeln!(f, "{}entry_path: {}", tab, p.entry_path.display())?;
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
