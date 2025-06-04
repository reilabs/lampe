//! Functionality for emitting Lean definitions from Noir source.
mod builtin;
mod context;
pub mod indent;
mod pattern;
mod syntax;

use context::EmitterCtx;
use fm::FileId;
use itertools::Itertools;
use noirc_errors::Location;
use noirc_frontend::{
    Kind, ResolvedGeneric, StructField, Type, TypeBinding, TypeBindings,
    ast::{IntegerBitSize, Signedness},
    graph::CrateId,
    hir::{
        Context,
        def_map::{ModuleData, ModuleDefId, ModuleId},
        type_check::generics::TraitGenerics,
    },
    hir_def::{
        expr::{HirArrayLiteral, HirExpression, HirIdent, HirLiteral},
        function::Parameters,
        stmt::{HirLValue, HirPattern, HirStatement},
        traits::{NamedType, TraitImpl},
    },
    node_interner::{
        DefinitionKind, DependencyId, ExprId, FuncId, GlobalId, StmtId, StructId, TraitId,
        TypeAliasId,
    },
};
use std::{
    cmp::Ordering,
    collections::{HashMap, HashSet},
};

use crate::file_generator::to_import_from_noir_path;
use crate::{
    lean::{indent::Indenter, syntax::expr::format_builtin_call},
    noir::{
        self,
        error::emit::{Error, Result},
    },
};

#[derive(PartialEq, Eq, Clone, Hash)]
pub enum EmitOutput {
    Struct(String),
    Function(String),
    TraitImpl(String),
    Alias(String),
    Global(String),
}

#[derive(Debug)]
pub struct TotalEmitOutput {
    pub type_content: String,
    pub decl_contents: HashMap<FileId, String>,
}

impl EmitOutput {
    #[must_use]
    pub fn is_empty(&self) -> bool {
        match self {
            EmitOutput::Struct(s)
            | EmitOutput::Function(s)
            | EmitOutput::Global(s)
            | EmitOutput::TraitImpl(s)
            | EmitOutput::Alias(s) => s.is_empty(),
        }
    }

    pub fn push_str(&mut self, string: &str) {
        match self {
            EmitOutput::Struct(s)
            | EmitOutput::Function(s)
            | EmitOutput::Global(s)
            | EmitOutput::TraitImpl(s)
            | EmitOutput::Alias(s) => s.push_str(string),
        }
    }
}

impl std::fmt::Display for EmitOutput {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EmitOutput::Struct(s)
            | EmitOutput::Function(s)
            | EmitOutput::Global(s)
            | EmitOutput::TraitImpl(s)
            | EmitOutput::Alias(s) => write!(f, "{s}"),
        }
    }
}

/// The stringified Lean definitions corresponding to a Noir module.
pub struct ModuleEntries {
    pub impl_refs: HashSet<String>,
    pub func_refs: HashSet<String>,
    pub defs: Vec<(Option<Location>, EmitOutput)>,
}

/// An emitter for specialized Lean definitions based on the corresponding Noir
/// intermediate representation.
pub struct LeanEmitter<'file_manager, 'parsed_files> {
    /// The compilation context of the Noir project.
    pub context: Context<'file_manager, 'parsed_files>,

    /// The identifier for the root crate in the Noir compilation context.
    root_crate: CrateId,

    /// The files contained in the root crate. Used to filter `std` and other crate files from the
    /// `file_manager` during emission and generation.
    known_files: HashSet<FileId>,
}

impl<'file_manager, 'parsed_files> LeanEmitter<'file_manager, 'parsed_files> {
    /// Creates a new emitter for Lean source code.
    ///
    /// The emitter wraps the current noir compilation `context`, and also has
    /// knowledge of the `known_files` that were added explicitly to the
    /// extraction process by the user.
    pub fn new(context: Context<'file_manager, 'parsed_files>, root_crate: CrateId) -> Self {
        let known_files = context
            .def_map(&root_crate)
            .expect("Root crate was missing in compilation context")
            .modules()
            .iter()
            .map(|(_, data)| data.location.file)
            .collect::<HashSet<_>>();

        Self {
            context,
            root_crate,
            known_files,
        }
    }

    /// Gets the identifier of the root crate for this compilation context.
    pub fn root_crate(&self) -> CrateId {
        self.root_crate
    }

    /// Emits a set of Lean definitions that correspond to the Noir language
    /// definitions seen by this emitter.
    ///
    /// # Errors
    ///
    /// - [`Error`] if the extraction process fails for any reason.
    ///
    /// # Panics
    ///
    /// When encountering a situation that would occur due to a bug in the Noir
    /// compiler, or due to programmer error.
    pub fn emit(&self) -> Result<TotalEmitOutput> {
        let type_content = self.emit_types()?;

        let mut decl_contents = HashMap::new();

        self.known_files.iter().try_for_each(|file| -> Result<_> {
            let file_decls = self.emit_decls(*file)?;
            decl_contents.insert(*file, file_decls);

            Ok(())
        })?;

        Ok(TotalEmitOutput {
            type_content,
            decl_contents,
        })
    }

    pub fn emit_types(&self) -> Result<String> {
        let mut indenter = Indenter::default();
        let mut outputs = HashSet::new();

        let mut dep_graph = self.context.def_interner.dependency_graph.clone();

        // Only consider nnodes in the dependency graph that could cause issues with the extracted
        // Lean code. This will only happen with extracted structs and type aliases.
        dep_graph.retain_nodes(|g, node_idx| {
            if let Some(dep_id) = g.node_weight(node_idx) {
                matches!(dep_id, DependencyId::Struct(_) | DependencyId::Alias(_))
            } else {
                false
            }
        });

        // Allow for cases where a node may depend on itself. This occurs in cases for trait
        // implementations for structs. If the recursive definition was truly an issue, then the
        // Noir compiler would complain already by this point.
        dep_graph.retain_edges(|g, e| {
            if let Some((start, end)) = g.edge_endpoints(e) {
                start != end
            } else {
                false
            }
        });

        let sorted_dep_graph = petgraph::algo::toposort(&dep_graph, None)
            .map_err(|err| noir::error::emit::Error::CycleDetected(format!("{err:?}")))?;

        let sorted_dep_weights = sorted_dep_graph
            .iter()
            .map(|id| dep_graph.node_weight(*id).unwrap())
            .collect::<Vec<_>>();

        for module in self
            .context
            .def_map(&self.root_crate())
            .expect("Root crate was missing in compilation context")
            .modules()
        {
            let ctx = EmitterCtx::from_module(module, &self.context.def_interner);

            for module_def_id in module.type_definitions().chain(module.value_definitions()) {
                let emit_output: (Option<usize>, String, EmitOutput) = match module_def_id {
                    ModuleDefId::TypeId(id) => {
                        let def_order = sorted_dep_weights
                            .clone()
                            .into_iter()
                            .position(|item| *item == DependencyId::Struct(id));

                        let name = self
                            .context
                            .def_interner
                            .get_struct(id)
                            .borrow()
                            .name
                            .0
                            .contents
                            .clone();

                        (
                            def_order,
                            name,
                            EmitOutput::Struct(self.emit_struct_def(&mut indenter, id, &ctx)?),
                        )
                    }
                    ModuleDefId::TypeAliasId(id) => {
                        // Check if this is a dummy ID corresponding to an associated type
                        // TODO: [#112] Is this the right way to handle this?
                        if id.0 == usize::MAX {
                            continue;
                        }

                        let def_order = sorted_dep_weights
                            .clone()
                            .into_iter()
                            .position(|item| *item == DependencyId::Alias(id));

                        let name = self
                            .context
                            .def_interner
                            .get_type_alias(id)
                            .borrow()
                            .name
                            .0
                            .contents
                            .clone();

                        (
                            def_order,
                            name,
                            EmitOutput::Alias(self.emit_alias(id, &ctx)?),
                        )
                    }
                    _ => continue,
                };

                outputs.insert(emit_output);
            }
        }

        let type_defs = outputs
            .into_iter()
            .sorted_by(|(ord1, name1, _), (ord2, name2, _)| match (ord1, ord2) {
                (Some(ord1), Some(ord2)) => ord1.cmp(ord2),
                (None, Some(_)) => Ordering::Greater,
                (Some(_), None) => Ordering::Less,
                (None, None) => name2.cmp(name1),
            })
            .rev()
            .map(|(_, _, output)| output.to_string())
            .join("\n\n");

        Ok(type_defs)
    }

    pub fn emit_decls(&self, file: FileId) -> Result<String> {
        let mut indenter = Indenter::default();
        let mut output = Vec::new();
        let mut all_impl_refs = HashSet::new();
        let mut all_func_refs = HashSet::new();

        // Emit definitions for each of the modules in the context in an arbitrary
        // iteration order
        for (_, module) in self
            .context
            .def_map(&self.root_crate())
            .expect("Root crate was missing in compilation context")
            .modules()
            .iter()
            .filter(|(_, data)| data.location.file == file)
        {
            let ModuleEntries {
                impl_refs,
                func_refs,
                defs,
            } = self.emit_module_decls(&mut indenter, module)?;
            output.extend(defs);
            all_impl_refs.extend(impl_refs);
            all_func_refs.extend(func_refs);
        }

        // Remove all entries that are duplicated as we do not necessarily have the
        // means to prevent emission of duplicates in all cases
        let mut set: HashSet<_> = HashSet::new();
        set.extend(output);
        let module_defs = set
            .into_iter()
            .sorted_by(|(loc1, _), (loc2, _)| match (loc1, loc2) {
                (Some(loc1), Some(loc2)) => loc1.span.cmp(&loc2.span),
                (None, Some(_)) => Ordering::Greater,
                (Some(_), None) => Ordering::Less,
                (None, None) => Ordering::Equal,
            })
            .map(|(_, d)| d.to_string())
            .join("\n");

        let env_funcs = all_func_refs.into_iter().sorted().join(", ");
        let env_traits = all_impl_refs.into_iter().sorted().join(", ");

        let import_name = to_import_from_noir_path(
            self.context
                .file_manager
                .path(file)
                .ok_or(Error::MissingIdentifier(format!("{file:?}")))?,
        );

        let env_def = format!("def {import_name}.env := Lampe.Env.mk [{env_funcs}] [{env_traits}]");

        // Smoosh the de-duplicated entries back together to yield a file.
        Ok(format!("{module_defs}\n\n{env_def}"))
    }

    /// Emits the Lean source code corresponding to a Noir module based on the
    /// `module`'s definition.
    ///
    /// # Errors
    ///
    /// - [`Error`] if the extraction process fails for any reason.
    pub fn emit_module_decls(
        &self,
        ind: &mut Indenter,
        module: &ModuleData,
    ) -> Result<ModuleEntries> {
        let mut accumulator: Vec<(Option<Location>, EmitOutput)> = Vec::new();
        let ctx = EmitterCtx::from_module(module, &self.context.def_interner);

        // We start by emitting the trait implementations.
        let mut impl_refs = HashSet::new();
        for (id, trait_impl) in self
            .context
            .def_interner
            .trait_implementations
            .iter()
            .filter(|(_, t)| t.borrow().file == module.location.file)
        {
            let impl_id = format!("impl_{}", id.0);

            let location = trait_impl
                .borrow()
                .methods
                .first()
                .map(|t| self.context.def_interner.function_modifiers(t).name_location);

            let emitted_trait_impl =
                self.emit_trait_impl(ind, &trait_impl.borrow(), &impl_id, &ctx)?;
            accumulator.push((location, EmitOutput::TraitImpl(emitted_trait_impl)));
            impl_refs.insert(impl_id);
        }

        let mut func_refs = HashSet::new();
        // We then emit all definitions that correspond to the given module.
        for typedef in module.type_definitions().chain(module.value_definitions()) {
            let emit_output = match typedef {
                ModuleDefId::FunctionId(id) => {
                    // Skip the trait methods, as these are already handled by `emit_trait_impl`.
                    if self.context.function_meta(&id).trait_impl.is_some() {
                        continue;
                    }
                    if self.context.def_interner.function_modifiers(&id).is_comptime {
                        continue;
                    }
                    let (def_name, def) = self.emit_free_function_def(ind, id, &ctx)?;
                    // [TODO] fix
                    if def_name.starts_with('_') {
                        continue;
                    }
                    func_refs.insert(format!("«{def_name}»"));

                    let location = self.context.def_interner.function_modifiers(&id).name_location;

                    (Some(location), EmitOutput::Function(def))
                }
                ModuleDefId::GlobalId(id) => {
                    let (global_name, global_string) = self.emit_global(ind, id, &ctx)?;

                    func_refs.insert(format!("«{global_name}»"));

                    let location = self.context.def_interner.get_global(id).location;

                    (Some(location), EmitOutput::Global(global_string))
                }
                // Structs and Type aliases are emitted in a separate file.
                // Modules and trait definitions are skipped
                _ => continue,
            };

            accumulator.push(emit_output);
        }

        let defs = accumulator
            .into_iter()
            .filter(|(_, d)| !d.is_empty())
            .map(|(loc, mut d)| {
                d.push_str("\n");
                (loc, d)
            })
            .collect();

        Ok(ModuleEntries {
            impl_refs,
            func_refs,
            defs,
        })
    }

    /// Emits the string indicating that a given type has explicitly implemented
    /// a given trait.
    ///
    /// Trait implementations do not appear to carry their method definitions
    /// with them, so we instead emit lines that serve as "notices" of a given
    /// type implementing a trait. The corresponding method definitions are
    /// instead emitted as functions (see [`emit_function`]).
    ///
    /// # Errors
    ///
    /// - [`Error`] if the extraction process fails for any reason.
    pub fn emit_trait_impl(
        &self,
        ind: &mut Indenter,
        trait_impl: &TraitImpl,
        impl_id: &str,
        ctx: &EmitterCtx,
    ) -> Result<String> {
        let trait_def_id = trait_impl.trait_id;
        let trait_data = self.context.def_interner.get_trait(trait_def_id);
        let fq_crate_name = self.fq_trait_name_from_crate_id(trait_data.crate_id, trait_def_id);
        let name = &trait_impl.ident;
        let full_name = if fq_crate_name.is_empty() {
            name.to_string()
        } else {
            format!("{fq_crate_name}::{name}")
        };
        let target = self.emit_fully_qualified_type(&trait_impl.typ, ctx);

        let where_clause_str = trait_impl
            .where_clause
            .iter()
            .map(|cons| {
                let typ_str = self.emit_fully_qualified_type(&cons.typ, ctx);
                let trait_name =
                    &self.context.def_interner.get_trait(cons.trait_bound.trait_id).name;
                let trait_generics_str = cons
                    .trait_bound
                    .trait_generics
                    .ordered
                    .iter()
                    .map(|g| self.emit_fully_qualified_type(g, ctx))
                    .join(", ");
                let trait_str = format!("{trait_name}<{trait_generics_str}>");
                format!("{typ_str} : {trait_str}")
            })
            .join(", ");
        let trait_generic_values = &trait_impl
            .trait_generics
            .iter()
            .map(|g| self.emit_fully_qualified_type(g, ctx))
            .collect_vec()
            .join(", ");
        // Get the named generics of the trait reference.
        // These must be included in the type variable declarations of the impl block.
        let trait_generic_vars = &trait_impl
            .trait_generics
            .iter()
            // Only named generics need to be included in the `<>`.
            .filter(|g| matches!(g, Type::NamedGeneric(..)))
            .map(|g| self.emit_fully_qualified_type(g, ctx))
            .collect_vec();

        let mut impl_generic_decls = HashSet::new();
        // Extend with the generics for the trait.
        impl_generic_decls.extend(trait_generic_vars.iter().cloned());
        // Extend with the generics for the implementor.
        impl_generic_decls.extend(collect_named_generics(&trait_impl.typ));
        let impl_generic_decls_str = impl_generic_decls.iter().join(", ");

        // Emit the implemented functions.
        ind.indent();
        let mut method_strings = Vec::<String>::default();
        for func_id in &trait_impl.methods {
            let method_string = self.emit_trait_function_def(ind, *func_id, ctx)?;
            method_strings.push(method_string);
        }
        ind.dedent()?;

        let methods = method_strings.join(";\n");
        Ok(syntax::format_trait_impl(
            impl_id,
            &impl_generic_decls_str,
            &full_name,
            trait_generic_values,
            &target,
            &methods,
            &where_clause_str,
        ))
    }

    /// Emits the Lean code corresponding to a type alias in Noir.
    ///
    /// # Errors
    ///
    /// - [`Error`] if the extraction process fails for any reason.
    #[allow(clippy::unnecessary_wraps)]
    pub fn emit_alias(&self, alias: TypeAliasId, ctx: &EmitterCtx) -> Result<String> {
        let alias_data = self.context.def_interner.get_type_alias(alias);
        let alias_data = alias_data.borrow();
        let alias_name = alias_data.name.to_string();
        let generics = alias_data
            .generics
            .iter()
            .map(|g| self.emit_resolved_generic(g, ctx))
            .join(", ");
        let typ = self.emit_fully_qualified_type(&alias_data.typ, ctx);
        Ok(syntax::format_alias(&alias_name, &generics, &typ))
    }

    /// Emits the Lean code corresponding to a Noir global definition.
    ///
    /// # Errors
    ///
    /// - [`Error`] if the extraction process fails for any reason.
    pub fn emit_global(
        &self,
        ind: &mut Indenter,
        global: GlobalId,
        ctx: &EmitterCtx,
    ) -> Result<(String, String)> {
        let global_data = self.context.def_interner.get_global(global);
        let statement = self.context.def_interner.statement(&global_data.let_statement);

        match statement {
            HirStatement::Let(lets) => {
                let ident = match &lets.pattern {
                    HirPattern::Identifier(hir_ident) => {
                        Ok(self.context.def_interner.definition_name(hir_ident.id).to_string())
                    }
                    _ => Err(Error::GlobalStatementNotLet),
                }?;

                let expr_type = self.emit_fully_qualified_type(&lets.r#type, ctx);

                let bound_expr = self.emit_expr(ind, lets.expression, ctx)?;

                // Get indentation right
                // TODO: Am I doing this right?
                ind.indent();
                let body = ind.run(bound_expr);
                ind.dedent()?;

                Ok(syntax::format_free_function_def(
                    &ident, "", "", &expr_type, &body,
                ))
            }
            _ => Err(Error::GlobalStatementNotLet),
        }
    }

    /// Emits the Lean source code corresponding to a resolved generics occurring
    /// at generic declarations.
    #[allow(clippy::unused_self)]
    pub fn emit_resolved_generic(&self, g: &ResolvedGeneric, _ctx: &EmitterCtx) -> String {
        let (is_num, u_size) = match g.kind() {
            Kind::Numeric(num_tp) => match num_tp.as_ref() {
                Type::Integer(_, bit_size) => (true, Some(bit_size.bit_size())),
                _ => (true, None),
            },
            _ => (false, None),
        };
        syntax::format_generic_def(&g.name, is_num, u_size)
    }

    /// Emits the Lean source code corresponding to a Noir structure at the
    /// module level.
    ///
    /// # Errors
    ///
    /// - [`Error`] if the extraction process fails for any reason.
    pub fn emit_struct_def(
        &self,
        ind: &mut Indenter,
        s: StructId,
        ctx: &EmitterCtx,
    ) -> Result<String> {
        let struct_data = self.context.def_interner.get_struct(s);
        let struct_data = struct_data.borrow();
        let fq_path = self
            .context
            .fully_qualified_struct_path(&struct_data.id.module_id().krate, s);
        let generics = &struct_data.generics;
        let generics_str = generics.iter().map(|g| self.emit_resolved_generic(g, ctx)).join(", ");
        let fields = struct_data.get_fields_as_written();

        // We generate the fields under a higher indentation level to make it look nice
        ind.indent();
        let field_strings = fields
            .iter()
            .map(|field| {
                let name = &field.name;
                let typ = &field.typ;
                ind.run(format!(
                    "{name} : {typ}",
                    typ = self.emit_fully_qualified_type(typ, ctx)
                ))
            })
            .collect_vec();
        ind.dedent()?;

        let fields_string = field_strings.join(",\n");

        Ok(syntax::format_struct_def(
            &fq_path,
            &generics_str,
            &fields_string,
        ))
    }

    fn is_func_unconstrained(tp: &Type) -> bool {
        match tp {
            Type::Function(_, _, _, is_unconstrained) => *is_unconstrained,
            Type::Forall(_, tp) => Self::is_func_unconstrained(tp),
            _ => false,
        }
    }

    /// Emits the Lean source code corresponding to a Noir function at the
    /// module level. Returns the definition name and the emitted function
    /// definition.
    ///
    /// # Errors
    ///
    /// - [`Error`] if the extraction process fails for any reason.
    pub fn emit_free_function_def(
        &self,
        ind: &mut Indenter,
        func: FuncId,
        ctx: &EmitterCtx,
    ) -> Result<(String, String)> {
        let func_meta = self.context.function_meta(&func);
        // The parameters whose type must be replaced by a type variable should be
        // appended to the list of generics.
        let impl_generics = func_meta
            .parameters
            .iter()
            .filter_map(|(_, ty, _)| ctx.get_impl_param(ty))
            .map(std::string::ToString::to_string);
        let generics_string = func_meta
            .all_generics
            .iter()
            .map(|g| self.emit_resolved_generic(g, ctx))
            .chain(impl_generics)
            .join(", ");
        let parameters = self.emit_parameters(&func_meta.parameters, ctx)?;
        let ret_type = self.emit_fully_qualified_type(func_meta.return_type(), ctx);

        let is_unconstrained = Self::is_func_unconstrained(&func_meta.typ);

        // Generate the function body ready for insertion
        ind.indent();
        let body = if is_unconstrained {
            ind.run(format_builtin_call(&"fresh".into(), "", &ret_type))
        } else {
            self.emit_expr(
                ind,
                self.context.def_interner.function(&func).as_expr(),
                ctx,
            )?
        };
        ind.dedent()?;

        // For struct methods that have a self-type, we add a flag that tells the extractor to
        // circumvent the usual namespace resolution and use the type's namespace instead
        let (has_path_already, self_type_str) = match &func_meta.self_type {
            Some(ty) => {
                let fq_type = self.emit_fully_qualified_type(ty, ctx);
                (true, format!("{fq_type}::"))
            }
            _ => (false, String::new()),
        };

        let fn_ident = if has_path_already {
            let fn_name = self.context.function_name(&func);
            format!("{self_type_str}{fn_name}")
        } else {
            self.context
                .fully_qualified_function_name(&func_meta.source_crate, &func)
        };

        // [TODO] discard the dummy trait methods

        // Now we can actually build our function
        Ok(syntax::format_free_function_def(
            &fn_ident,
            &generics_string,
            &parameters,
            &ret_type,
            &body,
        ))
    }

    /// Emits the Lean source code corresponding to a Noir function that belongs
    /// to a trait implementation.
    ///
    /// # Errors
    ///
    /// - [`Error`] if the extraction process fails for any reason.
    pub fn emit_trait_function_def(
        &self,
        ind: &mut Indenter,
        func: FuncId,
        ctx: &EmitterCtx,
    ) -> Result<String> {
        // [TODO] signature generation should be moved to a separate function that is
        // also called from `emit_free_function_def`.
        let func_meta = self.context.function_meta(&func);
        let fq_path = self
            .context
            .fully_qualified_function_name(&func_meta.source_crate, &func);
        // The parameters whose type must be replaced by a type variable should be
        // appended to the list of generics.
        let impl_generics = func_meta
            .parameters
            .iter()
            .filter_map(|(_, ty, _)| ctx.get_impl_param(ty))
            .map(std::string::ToString::to_string);
        let generics_string = func_meta
            .direct_generics
            .iter()
            .map(|g| self.emit_resolved_generic(g, ctx))
            .chain(impl_generics)
            .join(", ");
        let parameters = self.emit_parameters(&func_meta.parameters, ctx)?;
        let ret_type = self.emit_fully_qualified_type(func_meta.return_type(), ctx);

        // Generate the function body ready for insertion
        ind.indent();
        let body = self.emit_expr(
            ind,
            self.context.def_interner.function(&func).as_expr(),
            ctx,
        )?;
        ind.dedent()?;

        Ok(syntax::format_trait_function_def(
            &fq_path,
            &generics_string,
            &parameters,
            &ret_type,
            &body,
        ))
    }

    /// Emits a fully-qualified type name for types where this is relevant.
    ///
    /// The correct operation of this function relies on type resolution having
    /// been conducted properly by the Noir compiler. Absent that, it may return
    /// nonsensical results.
    ///
    /// # Panics
    ///
    /// When encountering situations that would indicate a bug in the Noir
    /// compiler.
    pub fn emit_fully_qualified_type(&self, typ: &Type, ctx: &EmitterCtx) -> String {
        // If `typ` is an `impl` param type, directly return the substituted type
        // variable name.
        if let Some(name) = ctx.get_impl_param(typ) {
            return name.to_string();
        }
        // If `typ` is an `impl` return type, return the substituted type's string
        // representation.
        if let Some(typ) = ctx.get_impl_return(typ) {
            return self.emit_fully_qualified_type(typ, ctx);
        }
        // If `typ` is still an `impl` type, return a placeholder type.
        if context::is_impl(typ) {
            return syntax::r#type::format_placeholder();
        }
        match typ {
            Type::Unit => syntax::r#type::format_unit(),
            Type::Array(size, elem_type) => {
                let elem_type = self.emit_fully_qualified_type(elem_type, ctx);
                let size = emit_numeric_type_const(size.as_ref());
                syntax::r#type::format_array(&elem_type, &size)
            }
            Type::Slice(elem_type) => {
                let elem_type = self.emit_fully_qualified_type(elem_type, ctx);
                syntax::r#type::format_slice(&elem_type)
            }
            Type::Tuple(elems) => {
                let elem_types = elems
                    .iter()
                    .map(|typ| self.emit_fully_qualified_type(typ, ctx))
                    .collect_vec();
                let elems_str = elem_types.join(", ");
                syntax::r#type::format_tuple(&elems_str)
            }
            Type::Struct(struct_type, generics) => {
                let struct_type = struct_type.borrow();
                let module_id = struct_type.id.module_id();
                let name = self
                    .context
                    .fully_qualified_struct_path(&module_id.krate, struct_type.id);
                let generics_resolved = generics
                    .iter()
                    .map(|g| self.emit_fully_qualified_type(g, ctx))
                    .collect_vec();
                let generics_str = generics_resolved.join(", ");
                syntax::r#type::format_struct(&name, &generics_str)
            }
            Type::Function(args, ret, _env, _is_unconstrained) => {
                let arg_types = args
                    .iter()
                    .map(|arg| self.emit_fully_qualified_type(arg, ctx))
                    .collect_vec();
                let arg_types_str = arg_types.join(", ");
                let ret_str = self.emit_fully_qualified_type(ret, ctx);
                syntax::r#type::format_function(&arg_types_str, &ret_str)
            }
            Type::MutableReference(typ) => {
                let typ_str = self.emit_fully_qualified_type(typ, ctx);
                syntax::r#type::format_mut_ref(&typ_str)
            }
            Type::Alias(alias, generics) => {
                let generics_resolved = generics
                    .iter()
                    .map(|g| self.emit_fully_qualified_type(g, ctx))
                    .collect_vec();
                let generics_str = generics_resolved.join(", ");
                let alias_name_str = alias.borrow().name.to_string();
                syntax::r#type::format_alias(&alias_name_str, &generics_str)
            }
            Type::Constant(num, Kind::Numeric(num_typ)) => match num_typ.as_ref() {
                Type::Integer(_, bit_size) => {
                    let bit_size = bit_size.bit_size();
                    syntax::r#type::format_uint_const(&num.to_string(), &format!("{bit_size}"))
                }
                Type::FieldElement => syntax::r#type::format_field_const(&num.to_string()),
                _ => unimplemented!("unsupported numeric type {num_typ}"),
            },
            Type::TypeVariable(tv) => match &*tv.borrow() {
                TypeBinding::Bound(b) => {
                    let b = b.follow_bindings();
                    self.emit_fully_qualified_type(&b, ctx)
                }
                TypeBinding::Unbound(..) => format!("{typ}"),
            },
            // _ if context::is_impl(typ) => {
            //     panic!("impl types must be replaced with type variables or concrete types")
            // }
            // In all the other cases we can use the default printing as internal type vars are
            // non-existent, constrained to be types we don't care about customizing, or are
            // non-existent in the phase the emitter runs after.
            _ => format!("{typ}"),
        }
    }

    /// Generates a fully-qualified module name from a module id.
    ///
    /// # Panics
    ///
    /// When encountering a situation that would occur due to a bug in the Noir
    /// compiler.
    pub fn fq_module_name_from_mod_id(&self, id: ModuleId) -> String {
        let krate = self
            .context
            .def_map(&id.krate)
            .expect("Module should exist in context");
        let (ix, data) = krate
            .modules()
            .iter()
            .find(|(i, _)| *i == id.local_id.0)
            .expect("Module should exist in context");
        let module_path = krate.get_module_path_with_separator(ix, data.parent, "::");

        if id.krate.is_stdlib() {
            format!("std::{module_path}")
        } else {
            module_path
        }
    }

    /// Generates a fully-qualified module name from a crate id.
    ///
    /// # Panics
    ///
    /// When encountering a situation that would occur due to a bug in the Noir
    /// compiler.
    pub fn fq_trait_name_from_crate_id(&self, id: CrateId, trait_id: TraitId) -> String {
        let krate = self.context.def_map(&id).expect("Module should exist in context");
        let (ix, data) = krate
            .modules()
            .iter()
            .find(|(_, m)| {
                let mut type_defs = m.type_definitions();
                type_defs.any(|item| match item {
                    ModuleDefId::TraitId(trait_id_inner) => trait_id == trait_id_inner,
                    _ => false,
                })
            })
            .expect("Should work");
        let module_path = krate.get_module_path_with_separator(ix, data.parent, "::");

        if id.is_stdlib() {
            format!("std::{module_path}")
        } else {
            module_path
        }
    }

    /// Emits the Lean source code corresponding to a Noir expression.
    ///
    /// # Errors
    ///
    /// - [`Error`] if the extraction process fails for any reason.
    ///
    /// # Panics
    ///
    /// When encountering macros, which should have been eliminated by the Noir
    /// compilation process before calling this function.
    #[allow(clippy::too_many_lines)] // Not possible to reasonably split up
    pub fn emit_expr(&self, ind: &mut Indenter, expr: ExprId, ctx: &EmitterCtx) -> Result<String> {
        let expr_data = self.context.def_interner.expression(&expr);
        // Get the output type of this expression.
        let out_ty = self.id_bound_type(expr);
        let out_ty_str = self.emit_fully_qualified_type(&out_ty, ctx);
        let expression = match expr_data {
            HirExpression::Block(block) | HirExpression::Unsafe(block) => {
                let mut statements: Vec<String> = block
                    .statements
                    .iter()
                    .map(|stmt| {
                        let stmt_line = self.emit_statement(ind, *stmt, ctx)?;
                        Ok(ind.run(stmt_line))
                    })
                    .try_collect()?;

                if let Some(last_stmt_id) = block.statements.iter().last() {
                    let last_stmt = self.context.def_interner.statement(last_stmt_id);
                    if matches!(
                        last_stmt,
                        HirStatement::Constrain(_) | HirStatement::Assign(_)
                    ) {
                        statements.push(ind.run("skip;"));
                    }
                }

                statements.join("\n")
            }
            HirExpression::Prefix(prefix) => {
                let rhs = self.emit_expr(ind, prefix.rhs, ctx)?;
                let rhs_ty = self.id_bound_type(prefix.rhs);
                let rhs_builtin_ty = unfold_alias(rhs_ty.clone()).try_into().ok();
                if let Some(builtin_name) =
                    builtin::try_prefix_into_builtin_name(prefix.operator, rhs_builtin_ty)
                {
                    syntax::expr::format_builtin_call(&builtin_name, &rhs, &out_ty_str)
                } else {
                    // Convert to a trait call if this prefix call doesn't correspond to a builtin
                    // call.
                    let rhs_ty_str = self.emit_fully_qualified_type(&rhs_ty, ctx);
                    let trait_method_id = self
                        .context
                        .def_interner
                        .get_prefix_operator_trait_method(&prefix.operator)
                        .expect("no trait corresponds to {prefix.operator:?}");
                    let func_name = self.context.def_interner.definition_name(
                        self.context.def_interner.trait_method_id(trait_method_id),
                    );
                    let corresp_trait =
                        self.context.def_interner.get_trait(trait_method_id.trait_id);
                    let trait_name = corresp_trait.name.to_string();
                    syntax::expr::format_call(
                        &syntax::expr::format_trait_func_ident(
                            &rhs_ty_str,
                            &trait_name,
                            "",
                            func_name,
                            "",
                        ),
                        &rhs,
                        &self.emit_fully_qualified_type(
                            &Type::Function(
                                vec![rhs_ty],
                                Box::new(out_ty),
                                Box::new(Type::Unit),
                                false,
                            ),
                            ctx,
                        ),
                    )
                }
            }
            HirExpression::Infix(infix) => {
                let lhs = self.emit_expr(ind, infix.lhs, ctx)?;
                let rhs = self.emit_expr(ind, infix.rhs, ctx)?;
                let lhs_ty = self.id_bound_type(infix.lhs);
                let rhs_ty = self.id_bound_type(infix.rhs);
                if let Some(builtin_name) = match (
                    unfold_alias(lhs_ty.clone()).try_into(),
                    unfold_alias(rhs_ty.clone()).try_into(),
                ) {
                    (Ok(lhs_ty), Ok(rhs_ty)) => {
                        builtin::try_infix_into_builtin_name(infix.operator.kind, lhs_ty, rhs_ty)
                    }
                    _ => None,
                } {
                    syntax::expr::format_builtin_call(
                        &builtin_name,
                        &[lhs, rhs].join(", "),
                        &out_ty_str,
                    )
                } else {
                    // Convert to a trait call if this infix call doesn't correspond to a builtin
                    // call.
                    let lhs_ty_str = self.emit_fully_qualified_type(&lhs_ty, ctx);
                    let rhs_ty_str = self.emit_fully_qualified_type(&rhs_ty, ctx);
                    let args_str = [lhs_ty_str.as_str(), rhs_ty_str.as_str()].join(", ");
                    let trait_method_id = self
                        .context
                        .def_interner
                        .get_operator_trait_method(infix.operator.kind);
                    let func_name = self.context.def_interner.definition_name(
                        self.context.def_interner.trait_method_id(trait_method_id),
                    );
                    let trait_name = self
                        .context
                        .def_interner
                        .get_trait(trait_method_id.trait_id)
                        .name
                        .to_string();
                    syntax::expr::format_call(
                        &syntax::expr::format_trait_func_ident(
                            &lhs_ty_str,
                            &trait_name,
                            "",
                            func_name,
                            "",
                        ),
                        &args_str,
                        &self.emit_fully_qualified_type(
                            &Type::Function(
                                vec![lhs_ty, rhs_ty],
                                Box::new(out_ty),
                                Box::new(Type::Unit),
                                false,
                            ),
                            ctx,
                        ),
                    )
                }
            }
            HirExpression::Call(call) => {
                assert!(
                    !call.is_macro_call,
                    "Macros should be resolved before running this tool"
                );
                let args: Vec<_> = call
                    .arguments
                    .iter()
                    .map(|arg| self.emit_expr(ind, *arg, ctx))
                    .try_collect()?;
                let args_str = args.join(", ");
                let func_expr_str = self.emit_expr(ind, call.func, ctx)?;

                if let Some(builtin_name) = builtin::try_func_expr_into_builtin_name(&func_expr_str)
                {
                    syntax::expr::format_builtin_call(&builtin_name, &args_str, &out_ty_str)
                } else {
                    let fn_typ_str =
                        self.emit_fully_qualified_type(&self.id_bound_type(call.func), ctx);
                    syntax::expr::format_call(&func_expr_str, &args_str, &fn_typ_str)
                }
            }
            HirExpression::Ident(ident, generics) => {
                let name = self.context.def_interner.definition_name(ident.id);
                let ident_def = self.context.def_interner.definition(ident.id);
                let bindings = self.context.def_interner.get_instantiation_bindings(expr);

                match &ident_def.kind {
                    DefinitionKind::Function(func_id) => {
                        let func_meta = self.context.def_interner.function_meta(func_id);
                        // Find the `impl` generic values.
                        // These are later appended to the emitted generics.
                        let impl_generics = bindings
                            .iter()
                            // Find the instantiation bindings that are not part of the generics of
                            // this ident expression.
                            .filter(|(_, (tv, ..))| {
                                !func_meta
                                    .all_generics
                                    .iter()
                                    .map(|resolved_gen| &resolved_gen.type_var)
                                    .any(|tv2| tv2.id() == tv.id())
                            })
                            // Ensure that the original type variable is substituted in the context.
                            .filter(|(_, (tv, ..))| {
                                ctx.get_impl_param(&Type::TypeVariable(tv.clone())).is_some()
                            })
                            .map(|(_, (tv, ..))| {
                                self.emit_fully_qualified_type(&Type::TypeVariable(tv.clone()), ctx)
                            });
                        match (func_meta.trait_impl, func_meta.trait_id) {
                            (Some(trait_impl_id), _) => {
                                let trait_impl = self
                                    .context
                                    .def_interner
                                    .get_trait_implementation(trait_impl_id);
                                let trait_impl = trait_impl.borrow();
                                let self_type = func_meta
                                    .self_type
                                    .as_ref()
                                    .map(|t| substitute_bindings(t, bindings))
                                    .expect(
                                        "the function associated with a trait function identifier \
                                         must have a self type",
                                    );
                                let self_type_str = self.emit_fully_qualified_type(&self_type, ctx);
                                let trait_name = trait_impl.ident.to_string();
                                let trait_generics = trait_impl
                                    .trait_generics
                                    .iter()
                                    .map(|g| substitute_bindings(g, bindings))
                                    .map(|t| self.emit_fully_qualified_type(&t, ctx))
                                    .join(", ");
                                let ident_generics = generics
                                    .unwrap_or_default()
                                    .iter()
                                    .map(|g| substitute_bindings(g, bindings))
                                    .map(|t| self.emit_fully_qualified_type(&t, ctx))
                                    .chain(impl_generics)
                                    .join(", ");
                                syntax::expr::format_trait_func_ident(
                                    &self_type_str,
                                    &trait_name,
                                    &trait_generics,
                                    name,
                                    &ident_generics,
                                )
                            }
                            // This branch is executed when the trait method is called on an `impl`
                            // type, i.e., the concrete type is unknown.
                            (None, Some(trait_id)) => {
                                let trt = self.context.def_interner.get_trait(trait_id);
                                let trait_name = trt.name.to_string();
                                let trait_generics = trt
                                    .generics
                                    .iter()
                                    .map(|rg| Type::TypeVariable(rg.type_var.clone()))
                                    .map(|g| substitute_bindings(&g, bindings))
                                    .map(|t| self.emit_fully_qualified_type(&t, ctx))
                                    .join(", ");
                                let ident_generics = generics
                                    .unwrap_or_default()
                                    .iter()
                                    .map(|g| substitute_bindings(g, bindings))
                                    .map(|t| self.emit_fully_qualified_type(&t, ctx))
                                    .chain(impl_generics)
                                    .join(", ");
                                let self_type = func_meta
                                    .self_type
                                    .as_ref()
                                    .map(|t| substitute_bindings(t, bindings))
                                    .map(|t| self.emit_fully_qualified_type(&t, ctx))
                                    .expect("self type must be present");
                                syntax::expr::format_trait_func_ident(
                                    &self_type,
                                    &trait_name,
                                    &trait_generics,
                                    name,
                                    &ident_generics,
                                )
                            }
                            _ => {
                                let (has_path_already, fn_name) = match &func_meta.self_type {
                                    Some(self_type) => {
                                        let self_type_str =
                                            self.emit_fully_qualified_type(self_type, ctx);

                                        // If the self-type is a slice or array, we treat this
                                        // differently and use the `std::slice` or `std::array` as
                                        // the namespace. This is what is detected by the builtin
                                        // syntax emitter to detect whether something is a builtin
                                        // or not.
                                        if syntax::is_slice_or_array(&self_type_str) {
                                            (false, name.to_string())
                                        } else {
                                            (true, format!("{self_type_str}::{name}"))
                                        }
                                    }
                                    _ => (false, name.to_string()),
                                };
                                let func_module_id = ModuleId {
                                    krate: func_meta.source_crate,
                                    local_id: func_meta.source_module,
                                };
                                let fq_mod_name = self.fq_module_name_from_mod_id(func_module_id);
                                let fq_func_name = if fq_mod_name.is_empty() || has_path_already {
                                    fn_name.clone()
                                } else {
                                    format!("{fq_mod_name}::{fn_name}")
                                };
                                let ident_generics = func_meta
                                    .all_generics
                                    .iter()
                                    .filter_map(|t| bindings.get(&t.type_var.id()))
                                    .map(|(_, _, ty)| self.emit_fully_qualified_type(ty, ctx))
                                    .chain(impl_generics)
                                    .join(", ");

                                syntax::expr::format_decl_func_ident(&fq_func_name, &ident_generics)
                            }
                        }
                    }
                    DefinitionKind::Global(id) => {
                        let global_info = self.context.def_interner.get_global(*id);
                        let let_stmt =
                            self.context.def_interner.statement(&global_info.let_statement);

                        let (global_name, global_type) = match let_stmt {
                            HirStatement::Let(let_stmt) => {
                                let ident = match &let_stmt.pattern {
                                    HirPattern::Identifier(hir_ident) => Ok(self
                                        .context
                                        .def_interner
                                        .definition_name(hir_ident.id)
                                        .to_string()),
                                    _ => Err(Error::GlobalStatementNotLet),
                                }?;

                                Ok((ident, let_stmt.r#type))
                            }
                            _ => Err(Error::GlobalStatementNotLet),
                        }?;

                        let dummy_func_type = Type::Function(
                            vec![],
                            Box::new(global_type),
                            Box::new(Type::Unit),
                            false,
                        );

                        let global_name = syntax::expr::format_decl_func_ident(&global_name, "");
                        let global_type = self.emit_fully_qualified_type(&dummy_func_type, ctx);
                        syntax::expr::format_call(&global_name, "", &global_type)
                    }
                    DefinitionKind::Local(..) => syntax::expr::format_var_ident(name),
                    DefinitionKind::NumericGeneric(_, tt) => match *tt.clone() {
                        Type::Integer(..) => syntax::expr::format_uint_const(name),
                        Type::FieldElement => syntax::expr::format_field_const(name),
                        _ => unimplemented!(),
                    },
                }
            }
            HirExpression::Index(index) => {
                let coll_type = self.id_bound_type(index.collection);
                let coll_builtin_type: builtin::BuiltinType =
                    unfold_alias(coll_type.clone()).try_into().unwrap();
                let index_builtin_name = builtin::get_index_builtin_name(coll_builtin_type)
                    .unwrap_or_else(|| panic!("cannot index {coll_builtin_type:?}"));

                let collection_expr_str = self.emit_expr(ind, index.collection, ctx)?;
                let index_expr_str = self.emit_expr(ind, index.index, ctx)?;
                // Wrap the index expression with a cast to u32.
                // [TODO] is this the best way?
                let index_expr_str = self.emit_cast_to_u32(&index_expr_str, ctx);
                let args_str = format!("{collection_expr_str}, {index_expr_str}");

                syntax::expr::format_builtin_call(&index_builtin_name, &args_str, &out_ty_str)
            }
            HirExpression::Literal(lit) => self.emit_literal(ind, &lit, expr, ctx)?,
            HirExpression::Constructor(constructor) => {
                let struct_def = constructor.r#type;
                let struct_def = struct_def.borrow();
                let crate_id = &self.root_crate();
                let name = self.context.fully_qualified_struct_path(crate_id, struct_def.id);
                let fields = constructor.fields;
                // Map a field name to its order.
                let field_orders: HashMap<_, usize> = (0..struct_def.num_fields())
                    .map(|i| {
                        let StructField { name, .. } = struct_def.field_at(i);
                        (name.clone(), i)
                    })
                    .collect();
                // Reorder the constructor fields before creating the string, so that they
                // correspond to the order in the original definition.
                let fields_strings: Vec<String> = fields
                    .iter()
                    .sorted_by_key(|(i, _)| field_orders.get(i).copied().unwrap_or_default())
                    .map(|(_, expr)| {
                        let expr_str = self.emit_expr(ind, *expr, ctx)?;
                        Ok(expr_str.to_string())
                    })
                    .try_collect()?;
                let fields_str = fields_strings.join(", ");
                let constructor_gen_vals_str = constructor
                    .struct_generics
                    .iter()
                    .map(|ty| self.emit_fully_qualified_type(ty, ctx))
                    .join(",");

                syntax::expr::format_constructor(
                    &name.to_string(),
                    &constructor_gen_vals_str,
                    &fields_str,
                )
            }
            HirExpression::MemberAccess(member) => {
                let lhs_expr_ty = self.id_bound_type(member.lhs);
                let target_expr_str = self.emit_expr(ind, member.lhs, ctx)?;
                let member_iden = member.rhs;
                match unfold_alias(lhs_expr_ty.clone()) {
                    Type::Struct(..) => {
                        let struct_ty_str = self.emit_fully_qualified_type(&lhs_expr_ty, ctx);
                        syntax::expr::format_member_access(
                            &struct_ty_str,
                            &target_expr_str,
                            &member_iden.to_string(),
                        )
                    }
                    Type::Tuple(..) => syntax::expr::format_tuple_access(
                        &target_expr_str,
                        &member_iden.to_string(),
                    ),
                    _ => panic!("member access lhs is not a struct or tuple: {lhs_expr_ty:?}"),
                }
            }
            HirExpression::Cast(cast) => {
                let source = self.emit_expr(ind, cast.lhs, ctx)?;
                let target_type = self.emit_fully_qualified_type(&cast.r#type, ctx);

                syntax::expr::format_builtin_call(
                    &builtin::CAST_BUILTIN_NAME.into(),
                    &source,
                    &target_type,
                )
            }
            HirExpression::If(if_expr) => {
                let if_cond = self.emit_expr(ind, if_expr.condition, ctx)?;
                let then_exec = self.emit_expr(ind, if_expr.consequence, ctx)?;
                let else_exec = if let Some(expr) = if_expr.alternative {
                    Some(self.emit_expr(ind, expr, ctx)?)
                } else {
                    None
                };

                syntax::expr::format_ite(&if_cond, &then_exec, else_exec.as_deref())
            }
            HirExpression::Tuple(tuple) => {
                let item_exprs: Vec<String> = tuple
                    .iter()
                    .map(|expr| self.emit_expr(ind, *expr, ctx))
                    .try_collect()?;
                let items = item_exprs.join(", ");

                syntax::expr::format_tuple(&items)
            }
            HirExpression::Lambda(lambda) => {
                let ret_type = self.emit_fully_qualified_type(&lambda.return_type, ctx);

                // Divide the parameters into simple and complex parameters, where simple
                // parameters are parameters that can be expressed as a single let or let mut
                // binding.
                let (simple_params, complex_params): (Vec<_>, Vec<_>) =
                    lambda.parameters.iter().enumerate().partition_map(
                        |(param_idx, (pat, param_typ))| {
                            let rhs = self.emit_fully_qualified_type(param_typ, ctx);
                            if let Some((_, lhs)) =
                                pattern::try_format_simple_pattern(pat, "", self, ctx)
                            {
                                // If the parameter is simple, we can directly use the ident as the lhs.
                                let lhs = self.context.def_interner.definition_name(lhs.id);
                                itertools::Either::Left(format!("{lhs} : {rhs}"))
                            } else {
                                // If the parameter is complex, we need to generate a fresh binding for
                                // it.
                                let lhs = format!("π{param_idx}");
                                itertools::Either::Right((pat.clone(), lhs, rhs))
                            }
                        },
                    );
                // Convert the parameters into strings.
                let params_str = complex_params
                    .iter()
                    .map(|(_, lhs, rhs)| format!("{lhs} : {rhs}"))
                    .chain(simple_params)
                    .join(", ");
                // Convert the complex parameters into a series of let (mut) bindings.
                let pattern_stmts_str = complex_params
                    .iter()
                    .map(|(pat, lhs, _)| pattern::format_pattern(pat, lhs, self, ctx).join(";\n"))
                    .join(";\n");
                let body = self.emit_expr(ind, lambda.body, ctx)?;
                // Prepend the body with the appropriate block of let (mut) bindings if there
                // are any complex parameters.
                let body = if pattern_stmts_str.is_empty() {
                    body
                } else {
                    ind.run(format!("{{\n{pattern_stmts_str};\n{{\n{body}\n}}\n}}"))
                };

                syntax::expr::format_lambda(&params_str, &body, &ret_type)
            }
            HirExpression::MethodCall(..) => {
                panic!("Method call expressions should not exist after type checking")
            }
            HirExpression::Comptime(..) => {
                panic!("Comptime expressions should not exist after compilation is done")
            }
            HirExpression::Quote(..) => {
                panic!("Quote expressions should not exist after macro resolution")
            }
            HirExpression::Unquote(..) => {
                panic!("Unquote expressions should not exist after macro resolution")
            }
            HirExpression::Error => {
                panic!("Encountered error expression where none should exist")
            }
        };

        Ok(expression)
    }

    /// Identifies the type of an expression, returning the bound type if the
    /// expression's type is a `TypeVariable` that is already bound.
    pub fn id_bound_type(&self, expr_id: ExprId) -> Type {
        let identified_ty = self.context.def_interner.id_type(expr_id);
        let expr_bindings = self.context.def_interner.try_get_instantiation_bindings(expr_id);
        // Get the instantiated type of the expression.
        let expr_ty = match (identified_ty, expr_bindings) {
            (Type::TypeVariable(tv), Some(expr_bindings))
                if expr_bindings.contains_key(&tv.id()) =>
            {
                expr_bindings[&tv.id()].2.clone()
            }
            (ty, _) => ty,
        };
        match &expr_ty {
            Type::TypeVariable(tv) => {
                if let TypeBinding::Bound(bound_ty) = &*tv.borrow() {
                    bound_ty.clone()
                } else {
                    // [TODO] fix the unnecessary clone.
                    expr_ty.clone()
                }
            }
            _ => expr_ty,
        }
    }

    /// Emits the Lean source code corresponding to a Noir statement.
    ///
    /// # Errors
    ///
    /// - [`Error`] if the extraction process fails for any reason.
    ///
    /// # Panics
    ///
    /// Upon reaching an unsupported construct that should have been eliminated
    /// by the Noir compiler at the point this function is called.
    pub fn emit_statement(
        &self,
        ind: &mut Indenter,
        statement: StmtId,
        ctx: &EmitterCtx,
    ) -> Result<String> {
        let stmt_data = self.context.def_interner.statement(&statement);
        let result = match stmt_data {
            HirStatement::Expression(expr) => self.emit_expr(ind, expr, ctx)?,
            HirStatement::Let(lets) => {
                let bound_expr = self.emit_expr(ind, lets.expression, ctx)?;
                if let Some((simple_stmt, _)) =
                    pattern::try_format_simple_pattern(&lets.pattern, &bound_expr, self, ctx)
                {
                    simple_stmt
                } else {
                    let pat_rhs = "π0";
                    let mut stmts = vec![syntax::stmt::format_let_in(pat_rhs, &bound_expr)];
                    stmts.extend(pattern::format_pattern(&lets.pattern, pat_rhs, self, ctx));
                    stmts.join(";\n")
                }
            }
            HirStatement::Constrain(constraint) => {
                let constraint_expr = self.emit_expr(ind, constraint.0, ctx)?;

                syntax::expr::format_builtin_call(
                    &builtin::ASSERT_BUILTIN_NAME.into(),
                    &constraint_expr,
                    &self.emit_fully_qualified_type(&Type::Unit, ctx),
                )
            }
            HirStatement::Assign(assign) => {
                let rhs_expr = self.emit_expr(ind, assign.expression, ctx)?;
                let lval = self.emit_l_value(ind, &assign.lvalue, ctx)?;
                syntax::stmt::format_assign(&lval, &rhs_expr)
            }
            HirStatement::For(fors) => {
                let loop_var = self.context.def_interner.definition_name(fors.identifier.id);
                let loop_var = &syntax::expr::format_var_ident(loop_var);
                let loop_start = self.emit_expr(ind, fors.start_range, ctx)?;
                let loop_end = self.emit_expr(ind, fors.end_range, ctx)?;
                let body = self.emit_expr(ind, fors.block, ctx)?;
                syntax::stmt::format_for_loop(loop_var, &loop_start, &loop_end, &body)
            }
            HirStatement::Break => "break".into(),
            HirStatement::Continue => "continue".into(),
            HirStatement::Semi(semi) => self.emit_expr(ind, semi, ctx)?,
            HirStatement::Comptime(_) => {
                panic!("Comptime statements should not exist after compilation")
            }
            HirStatement::Error => panic!("Encountered error statement where none should exist"),
        };
        // Append a semicolon to the statement if it doesn't already end with one.
        // We emit some statements already with a semicolon, so we don't want to add
        // another. [TODO] maybe fix this for consistency
        if result.ends_with(';') {
            Ok(result)
        } else {
            Ok(format!("{result};"))
        }
    }

    /// Generates a Lean representation of a Noir l-value (something that can be
    /// assigned to).
    ///
    /// # Errors
    ///
    /// - [`Error`] if the extraction process fails for any reason.
    pub fn emit_l_value(
        &self,
        ind: &mut Indenter,
        l_val: &HirLValue,
        ctx: &EmitterCtx,
    ) -> Result<String> {
        let result = match l_val {
            HirLValue::Ident(ident, _) => {
                let ident_str = self.context.def_interner.definition_name(ident.id);
                Ok(syntax::expr::format_var_ident(ident_str))
            }
            HirLValue::MemberAccess {
                object, field_name, ..
            } => {
                let lhs_lval_str = self.emit_l_value(ind, object.as_ref(), ctx)?;
                let lhs_ty = match object.as_ref() {
                    HirLValue::Ident(_, typ)
                    | HirLValue::MemberAccess { typ, .. }
                    | HirLValue::Index { typ, .. }
                    | HirLValue::Dereference {
                        element_type: typ, ..
                    } => typ,
                };
                match lhs_ty {
                    Type::Tuple(..) => Ok(syntax::lval::format_tuple_access(
                        &lhs_lval_str,
                        &field_name.to_string(),
                    )),
                    Type::Struct(..) => {
                        let struct_ty_str = self.emit_fully_qualified_type(lhs_ty, ctx);
                        Ok(syntax::lval::format_member_access(
                            &struct_ty_str,
                            &lhs_lval_str,
                            &field_name.to_string(),
                        ))
                    }
                    _ => Err(Error::UnexpectedType(
                        lhs_lval_str,
                        "tuple or struct".to_string(),
                    )),
                }
            }
            HirLValue::Index { array, index, .. } => {
                let lhs_lval_str = self.emit_l_value(ind, array.as_ref(), ctx)?;
                let idx_expr = self.emit_expr(ind, *index, ctx)?;
                let idx_expr = self.emit_cast_to_u32(&idx_expr, ctx);

                let lhs_ty = match array.as_ref() {
                    HirLValue::Ident(_, typ)
                    | HirLValue::MemberAccess { typ, .. }
                    | HirLValue::Index { typ, .. }
                    | HirLValue::Dereference {
                        element_type: typ, ..
                    } => typ,
                };
                match lhs_ty {
                    Type::Array(..) => {
                        Ok(syntax::lval::format_array_access(&lhs_lval_str, &idx_expr))
                    }
                    Type::Slice(..) => {
                        Ok(syntax::lval::format_slice_access(&lhs_lval_str, &idx_expr))
                    }
                    _ => Err(Error::UnexpectedType(
                        lhs_lval_str,
                        "array or slice".to_string(),
                    )),
                }
            }
            HirLValue::Dereference { lvalue, .. } => {
                let lhs_lval = self.emit_l_value(ind, lvalue.as_ref(), ctx)?;
                Ok(syntax::lval::format_deref_access(&lhs_lval))
            }
        };

        result
    }

    /// Emits the Lean source code corresponding to a Noir literal.
    ///
    /// # Errors
    ///
    /// - [`Error`] if the extraction process fails for any reason.
    pub fn emit_literal(
        &self,
        ind: &mut Indenter,
        literal: &HirLiteral,
        expr: ExprId,
        ctx: &EmitterCtx,
    ) -> Result<String> {
        let result = match &literal {
            HirLiteral::Array(array) | HirLiteral::Slice(array) => match array {
                HirArrayLiteral::Standard(elems) => {
                    let elems: Vec<String> = elems
                        .iter()
                        .map(|elem| self.emit_expr(ind, *elem, ctx))
                        .try_collect()?;
                    match literal {
                        HirLiteral::Array(..) => syntax::literal::format_array(&elems),
                        HirLiteral::Slice(..) => syntax::literal::format_slice(&elems),
                        _ => unreachable!(),
                    }
                }
                HirArrayLiteral::Repeated {
                    repeated_element,
                    length,
                } => {
                    let elem_str = self.emit_expr(ind, *repeated_element, ctx)?;
                    let rep_str = format!("{length}");
                    match literal {
                        HirLiteral::Array(..) => {
                            syntax::literal::format_repeated_array(&elem_str, &rep_str)
                        }
                        HirLiteral::Slice(..) => {
                            syntax::literal::format_repeated_slice(&elem_str, &rep_str)
                        }
                        _ => unreachable!(),
                    }
                }
            },
            HirLiteral::Bool(bool) => syntax::literal::format_bool(*bool),
            HirLiteral::Integer(felt, neg) => {
                let typ = self.id_bound_type(expr).to_string();
                syntax::literal::format_num(
                    &format!("{minus}{felt}", minus = if *neg { "-" } else { "" }),
                    &typ,
                )
            }
            HirLiteral::Str(str) => format!("\"{str}\""),
            HirLiteral::FmtStr(str_parts, vars, _) => {
                let output_str = str_parts.iter().fold(String::new(), |mut acc, part| {
                    match part {
                        noirc_frontend::token::FmtStrFragment::String(s) => acc.push_str(s),
                        noirc_frontend::token::FmtStrFragment::Interpolation(inner, _) => {
                            acc.push_str(&format!("{{{inner}}}"));
                        }
                    }
                    acc
                });

                let output_vars: String =
                    vars.iter()
                        .try_fold(String::new(), |mut acc, &var_id| -> Result<String> {
                            let var_name = self.emit_expr(ind, var_id, ctx)?;
                            acc.push_str(&var_name.to_string());
                            acc.push_str(", ");
                            Ok(acc)
                        })?;

                let output_vars = output_vars.trim_end_matches(", ");

                format!("#format(\"{output_str}\", {output_vars})")
            }
            HirLiteral::Unit => syntax::literal::format_unit(),
        };

        Ok(result)
    }

    /// Generates a function parameter string from the provided parameters.
    ///
    /// # Errors
    ///
    /// - [`Error`] if the extraction process fails for any reason.
    pub fn emit_parameters(&self, params: &Parameters, ctx: &EmitterCtx) -> Result<String> {
        let result_params: Vec<String> = params
            .iter()
            .map(|(pattern, typ, ..)| {
                let name = self
                    .context
                    .def_interner
                    .definition_name(expect_identifier(pattern)?.id);

                let qualified_type = self.emit_fully_qualified_type(typ, ctx);

                Ok(format!("{name} : {qualified_type}"))
            })
            .try_collect()?;

        Ok(result_params.join(", "))
    }

    fn emit_cast_to_u32(&self, expr: &str, ctx: &EmitterCtx) -> String {
        syntax::expr::format_builtin_call(
            &builtin::CAST_BUILTIN_NAME.into(),
            expr,
            &self.emit_fully_qualified_type(
                &Type::Integer(Signedness::Unsigned, IntegerBitSize::ThirtyTwo),
                ctx,
            ),
        )
    }
}

/// Collects the named generics from a type recursively.
#[must_use]
pub fn collect_named_generics(typ: &Type) -> Vec<String> {
    match typ {
        Type::Array(inner_type, _)
        | Type::Slice(inner_type)
        | Type::MutableReference(inner_type) => collect_named_generics(inner_type),
        Type::Tuple(elems) => elems.iter().flat_map(collect_named_generics).collect_vec(),
        Type::Struct(_, generics)
        | Type::TraitAsType(
            _,
            _,
            TraitGenerics {
                ordered: generics, ..
            },
        ) => generics.iter().flat_map(collect_named_generics).collect_vec(),
        Type::Bool
        | Type::Integer(..)
        | Type::String(..)
        | Type::FmtString(..)
        | Type::Unit
        | Type::FieldElement => Vec::new(),
        Type::NamedGeneric(..) => Vec::from([format!("{typ}")]),
        _ => unimplemented!("cannot collect named generics from {typ} (yet)"),
    }
}

#[must_use]
fn emit_numeric_type_const(typ: &Type) -> String {
    match typ {
        Type::TypeVariable(tv) => match &*tv.borrow() {
            TypeBinding::Bound(b) => {
                let b = b.follow_bindings();
                emit_numeric_type_const(&b)
            }
            TypeBinding::Unbound(..) => format!("{typ}"),
        },
        Type::Constant(num, Kind::Numeric(_)) => format!("{num}"),

        _ => format!("{typ}"),
    }
}

/// Given a type `T` and a `TypeBindings` map `m`, returns a new type where
/// the type variables in `T` have been recursively substituted with the
/// values in `m`.
#[must_use]
fn substitute_bindings(typ: &Type, bindings: &TypeBindings) -> Type {
    match typ {
        Type::TypeVariable(tv) | Type::NamedGeneric(tv, _) => bindings
            .get(&tv.id())
            .map(|(_, _, t)| t)
            .cloned()
            .unwrap_or(typ.clone()),
        Type::Array(n, e) => Type::Array(
            Box::new(substitute_bindings(n.as_ref(), bindings)),
            Box::new(substitute_bindings(e.as_ref(), bindings)),
        ),
        Type::Slice(e) => Type::Slice(Box::new(substitute_bindings(e.as_ref(), bindings))),
        Type::String(n) => Type::String(Box::new(substitute_bindings(n, bindings))),
        Type::FmtString(n, vec) => Type::FmtString(
            Box::new(substitute_bindings(n, bindings)),
            Box::new(substitute_bindings(vec, bindings)),
        ),
        Type::Tuple(vec) => {
            Type::Tuple(vec.iter().map(|t| substitute_bindings(t, bindings)).collect())
        }
        Type::Struct(def, generics) => Type::Struct(
            def.clone(),
            generics.iter().map(|t| substitute_bindings(t, bindings)).collect(),
        ),
        Type::Alias(def, generics) => Type::Alias(
            def.clone(),
            generics.iter().map(|t| substitute_bindings(t, bindings)).collect(),
        ),
        Type::Function(params, ret, env, unconstrained) => Type::Function(
            params.iter().map(|t| substitute_bindings(t, bindings)).collect(),
            Box::new(substitute_bindings(ret, bindings)),
            Box::new(substitute_bindings(env, bindings)),
            *unconstrained,
        ),
        Type::TraitAsType(id, name, generics) => Type::TraitAsType(
            *id,
            name.clone(),
            TraitGenerics {
                ordered: generics
                    .ordered
                    .iter()
                    .map(|t| substitute_bindings(t, bindings))
                    .collect(),
                named: generics
                    .named
                    .iter()
                    .map(|t| NamedType {
                        name: t.name.clone(),
                        typ: substitute_bindings(&t.typ, bindings),
                    })
                    .collect(),
            },
        ),
        Type::MutableReference(t) => {
            Type::MutableReference(Box::new(substitute_bindings(t, bindings)))
        }
        Type::Forall(tvs, t) => {
            Type::Forall(tvs.clone(), Box::new(substitute_bindings(t, bindings)))
        }
        _ => typ.clone(),
    }
}

/// If `typ` is an alias, unfolds it until it is no longer an alias.
#[must_use]
fn unfold_alias(typ: Type) -> Type {
    match typ {
        Type::Alias(alias, generics) => {
            let unfolded_typ = alias.borrow().get_type(&generics);
            unfold_alias(unfolded_typ)
        }
        typ => typ,
    }
}

/// Expects that the provided pattern is an HIR identifier.
///
/// # Errors
///
/// - [`Error::MissingIdentifier`] if the provided `pattern` is not an
///   identifier.
pub fn expect_identifier(pattern: &HirPattern) -> Result<&HirIdent> {
    match pattern {
        HirPattern::Identifier(ident) => Ok(ident),
        _ => Err(Error::MissingIdentifier(format!("{pattern:?}"))),
    }
}

// TODO Proper emit tests
