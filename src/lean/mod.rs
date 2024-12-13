//! Functionality for emitting Lean definitions from Noir source.
mod builtin;
pub mod indent;
mod syntax;

use std::collections::{HashMap, HashSet};

use fm::FileId;
use indoc::formatdoc;
use itertools::Itertools;
use noirc_frontend::{
    ast::Visibility,
    graph::CrateId,
    hir::{
        def_map::{ModuleData, ModuleId},
        Context,
    },
    hir_def::{
        expr::{HirArrayLiteral, HirIdent},
        function::Parameters,
        stmt::{HirLValue, HirPattern},
        traits::TraitImpl,
    },
    macros_api::{HirExpression, HirLiteral, HirStatement, ModuleDefId, StructId},
    node_interner::{DefinitionKind, ExprId, FuncId, GlobalId, StmtId, TraitId, TypeAliasId},
    Type,
};

use crate::{
    error::emit::{Error, Result},
    lean::indent::Indenter,
    noir::project::KnownFiles,
};

/// The stringified Lean definitions corresponding to a Noir module.
pub struct ModuleEntries {
    pub impl_refs: Vec<String>,
    pub defs: Vec<String>,
}

/// An emitter for specialized Lean definitions based on the corresponding Noir
/// intermediate representation.
pub struct LeanEmitter {
    /// The compilation context of the Noir project.
    pub context: Context<'static, 'static>,

    /// The files that were explicitly added to the compilation context.
    ///
    /// This will contain the file IDs for files added manually during
    /// extraction tool execution, and not identifiers for files in the standard
    /// library and other implicit libraries. These are used for filtering to
    /// prevent emission of definitions for the standard library that are
    /// already carefully manually defined in Lean.
    known_files: KnownFiles,

    /// The identifier for the root crate in the Noir compilation context.
    root_crate: CrateId,
}

impl LeanEmitter {
    /// Creates a new emitter for Lean source code.
    ///
    /// The emitter wraps the current noir compilation `context`, and also has
    /// knowledge of the `known_files` that were added explicitly to the
    /// extraction process by the user.
    pub fn new(
        context: Context<'static, 'static>,
        known_files: KnownFiles,
        root_crate: CrateId,
    ) -> Self {
        Self {
            context,
            known_files,
            root_crate,
        }
    }

    /// Enables reference tracking in the internal context.
    pub fn track_references(&mut self) {
        self.context.track_references();
    }

    /// Checks if the emitter knows about the file with the given ID, returning
    /// `true` if it does and `false` otherwise.
    pub fn knows_file(&self, file: FileId) -> bool {
        self.known_files.contains(&file)
    }

    /// Gets the identifier of the root crate for this compilation context.
    pub fn root_crate(&self) -> CrateId {
        self.root_crate
    }
}

impl LeanEmitter {
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
    pub fn emit(&self) -> Result<String> {
        let mut indenter = Indenter::default();
        let mut output = Vec::new();
        let mut all_impl_refs = HashSet::new();

        // Emit definitions for each of the modules in the context in an arbitrary
        // iteration order
        for module in self
            .context
            .def_map(&self.root_crate())
            .expect("Root crate was missing in compilation context")
            .modules()
        {
            let ModuleEntries { impl_refs, defs } = self.emit_module(&mut indenter, module)?;
            output.extend(defs);
            all_impl_refs.extend(impl_refs);
        }

        // Remove all entries that are duplicated as we do not necessarily have the
        // means to prevent emission of duplicates in all cases
        let mut set: HashSet<String> = HashSet::new();
        set.extend(output);
        let no_dupes: Vec<String> = set.into_iter().collect();
        let module_defs = no_dupes.join("\n");

        let env_funcs = "";
        let env_traits = all_impl_refs.into_iter().join(", ");
        let env_def = format!("def env := Lampe.Env.mk [{env_funcs}] [{env_traits}]");

        // Smoosh the de-duplicated entries back together to yield a file.
        Ok(format!("{module_defs}\n\n{env_def}"))
    }

    /// Emits the Lean source code corresponding to a Noir module based on the
    /// `module`'s definition.
    ///
    /// # Errors
    ///
    /// - [`Error`] if the extraction process fails for any reason.
    pub fn emit_module(&self, ind: &mut Indenter, module: &ModuleData) -> Result<ModuleEntries> {
        let mut accumulator = Vec::new();

        // We start by emitting the trait implementations.
        let mut impl_ids = Vec::new();
        for (id, trait_impl) in self
            .context
            .def_interner
            .trait_implementations
            .iter()
            .filter(|(_, t)| self.knows_file(t.borrow().file))
        {
            let impl_id = format!("impl_{}", id.0);
            let trait_impl = self.emit_trait_impl(ind, &trait_impl.borrow(), &impl_id)?;
            accumulator.push(trait_impl);
            impl_ids.push(impl_id);
        }

        // We then emit all definitions that correspond to the given module.
        for typedef in module.type_definitions().chain(module.value_definitions()) {
            let definition = match typedef {
                ModuleDefId::FunctionId(id) => {
                    // Skip the trait methods, as these are already handled by `emit_trait_impl`.
                    if self.context.function_meta(&id).trait_impl.is_some() {
                        continue;
                    }
                    self.emit_function_def(ind, id, "nr_def", true, true)?
                }
                ModuleDefId::TypeId(id) => self.emit_struct_def(ind, id, "nr_struct_def")?,
                ModuleDefId::GlobalId(id) => self.emit_global(ind, id)?,
                ModuleDefId::TypeAliasId(id) => self.emit_alias(id)?,
                ModuleDefId::ModuleId(_) => {
                    unimplemented!("It is unclear what actually generates these.")
                }
                // Skip the trait definitions.
                ModuleDefId::TraitId(_) => continue,
            };

            accumulator.push(definition.to_string());
        }

        let defns = accumulator
            .into_iter()
            .filter(|d| !d.is_empty())
            .map(|d| format!("{d}\n"))
            .collect();

        Ok(ModuleEntries {
            impl_refs: impl_ids,
            defs: defns,
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
        let target = self.emit_fully_qualified_type(&trait_impl.typ);

        let generics = &trait_impl
            .trait_generics
            .iter()
            .map(|g| self.emit_fully_qualified_type(g))
            .collect_vec();
        let trait_gens = generics.join(", ");

        let mut all_generics = Vec::new();
        all_generics.extend(generics.iter().cloned());
        all_generics.extend(self.collect_generics(&trait_impl.typ));
        let all_generics_str = all_generics.join(", ");

        // Emit the implemented functions.
        ind.indent();
        let mut method_strings = Vec::<String>::default();
        for func_id in trait_impl.methods.iter() {
            let method_string = self.emit_function_def(ind, func_id.clone(), "fn", false, false)?;
            method_strings.push(method_string);
        }
        ind.dedent()?;

        let methods = method_strings.join(";\n");
        Ok(syntax::format_trait_impl(
            impl_id,
            &all_generics_str,
            &full_name,
            &trait_gens,
            &target,
            &methods,
        ))
    }

    /// Collects the named generics from a type recursively.
    pub fn collect_generics(&self, typ: &Type) -> Vec<String> {
        match typ {
            Type::Array(inner_type, _)
            | Type::Slice(inner_type)
            | Type::MutableReference(inner_type) => self.collect_generics(&inner_type),
            Type::Tuple(elems) => {
                elems.iter().flat_map(|typ| self.collect_generics(typ)).collect_vec()
            }
            Type::Struct(_, generics) | Type::TraitAsType(_, _, generics) => {
                generics.iter().flat_map(|g| self.collect_generics(g)).collect_vec()
            }
            Type::Bool
            | Type::Integer(..)
            | Type::String(..)
            | Type::FmtString(..)
            | Type::Unit
            | Type::FieldElement => Vec::new(),
            Type::NamedGeneric(..) => Vec::from([format!("{typ}")]),
            _ => unimplemented!("cannot collect generics from {typ} (yet)"),
        }
    }

    /// Emits Lean code corresponding to a trait definition in Noir.
    ///
    /// Note that this doesn't currently contend with associated types or consts
    /// in traits due to a strange indexing issue that may or may not be a Noir
    /// compiler bug.
    ///
    /// # Errors
    ///
    /// - [`Error`] if the extraction process fails for any reason.
    pub fn emit_trait(&self, ind: &mut Indenter, trait_id: TraitId) -> Result<String> {
        let trait_data = self.context.def_interner.get_trait(trait_id);
        let trait_name = &trait_data.name;
        let fq_crate_name = self.fq_trait_name_from_crate_id(trait_data.crate_id, trait_id);
        let full_name = if fq_crate_name.is_empty() {
            trait_name.to_string()
        } else {
            format!("{fq_crate_name}::{trait_name}")
        };
        let generics = trait_data.generics.iter().map(|g| g.name.clone()).join(", ");

        let method_strings = &trait_data
            .methods
            .iter()
            .map(|method| {
                let name = &method.name;
                let generics = method.direct_generics.iter().map(|g| &g.name).join(", ");
                let typ = self.emit_fully_qualified_type(&method.typ);

                // We ignore defaults as they appear to be instantiated by this point for
                // implementing types.
                format!("fn {name}<{generics}> : {typ};")
            })
            .collect_vec();

        ind.indent();
        let methods = ind.run(method_strings.join("\n"));
        ind.dedent()?;

        let trait_def = formatdoc! {
            r"trait {full_name}<{generics}> {{
            {methods}
            }}"
        };

        Ok(trait_def)
    }

    /// Emits the Lean code corresponding to a type alias in Noir.
    ///
    /// # Errors
    ///
    /// - [`Error`] if the extraction process fails for any reason.
    pub fn emit_alias(&self, alias: TypeAliasId) -> Result<String> {
        let alias_data = self.context.def_interner.get_type_alias(alias);
        let alias_data = alias_data.borrow();
        let alias_name = &alias_data.name;
        let generics = alias_data
            .generics
            .iter()
            .map(|g| {
                let gen = &g.name;
                format!("{gen}")
            })
            .join(", ");
        let typ = self.emit_fully_qualified_type(&alias_data.typ);

        Ok(format!("type {alias_name}<{generics}> = {typ};"))
    }

    /// Emits the Lean code corresponding to a Noir global definition.
    ///
    /// # Errors
    ///
    /// - [`Error`] if the extraction process fails for any reason.
    pub fn emit_global(&self, ind: &mut Indenter, global: GlobalId) -> Result<String> {
        let global_data = self.context.def_interner.get_global(global);
        let value = self.emit_statement(ind, global_data.let_statement)?;

        Ok(format!("global {value}"))
    }

    /// Emits the Lean source code corresponding to a Noir structure at the
    /// module level.
    ///
    /// # Errors
    ///
    /// - [`Error`] if the extraction process fails for any reason.
    pub fn emit_struct_def(&self, ind: &mut Indenter, s: StructId, prefix: &str) -> Result<String> {
        let struct_data = self.context.def_interner.get_struct(s);
        let struct_data = struct_data.borrow();
        let fq_path = self
            .context
            .fully_qualified_struct_path(&struct_data.id.module_id().krate, s);
        let generics = &struct_data.generics;
        let generics_string = generics.iter().map(|g| &g.name).join(", ");
        let fields = struct_data.get_fields_as_written();

        // We generate the fields under a higher indentation level to make it look nice
        ind.indent();
        let field_strings = fields
            .iter()
            .map(|(name, typ)| {
                ind.run(format!(
                    "{name} : {typ}",
                    typ = self.emit_fully_qualified_type(typ)
                ))
            })
            .collect_vec();
        ind.dedent()?;

        let fields_string = field_strings.join(",\n");

        let result = formatdoc! {
            r"{prefix} {fq_path}<{generics_string}> {{
            {fields_string}
            }}"
        };

        Ok(result)
    }

    /// Emits the Lean source code corresponding to a Noir function at the
    /// module level.
    ///
    /// If `qualify_trait` is set to `true` and if the function
    /// identified by `func` is from a trait impl, then the trait path is prepended
    /// to the function name.
    ///
    /// If `qualify_self` is set to `true` and if the function
    /// identified by `func` is from an impl, then the trait path is prepended
    /// to the function name.
    ///
    /// # Errors
    ///
    /// - [`Error`] if the extraction process fails for any reason.
    pub fn emit_function_def(
        &self,
        ind: &mut Indenter,
        func: FuncId,
        prefix: &str,
        qualify_trait: bool,
        qualify_self_typ: bool,
    ) -> Result<String> {
        // Get the various parameters
        let func_data = self.context.function_meta(&func);
        let generics = &func_data.all_generics;
        let fq_path = self
            .context
            .fully_qualified_function_name(&func_data.source_crate, &func);
        let generics_string = generics.iter().map(|g| &g.name).join(", ");
        let parameters = self.function_param_string(&func_data.parameters)?;
        let ret_type = self.emit_fully_qualified_type(func_data.return_type());
        let assoc_trait_string = match func_data.trait_impl {
            Some(trait_id) if qualify_trait => {
                let impl_data = self.context.def_interner.get_trait_implementation(trait_id);
                let impl_data = impl_data.borrow();
                let trait_data = self.context.def_interner.get_trait(impl_data.trait_id);
                let fq_crate_name =
                    self.fq_trait_name_from_crate_id(trait_data.crate_id, impl_data.trait_id);
                let trait_name = &trait_data.name;
                let impl_type = self.emit_fully_qualified_type(&impl_data.typ);

                let impl_generics = &impl_data
                    .trait_generics
                    .iter()
                    .map(|g| self.emit_fully_qualified_type(g))
                    .collect_vec();
                let generics_str = impl_generics.join(", ");

                let fq_trait_name = if fq_crate_name.is_empty() {
                    format!("{trait_name}<{generics_str}>")
                } else {
                    format!("{fq_crate_name}::{trait_name}<{generics_str}>")
                };

                format!("({impl_type} as {fq_trait_name})::")
            }
            _ => String::new(),
        };

        // Generate the function body ready for insertion
        ind.indent();
        let body = self.emit_expr(ind, self.context.def_interner.function(&func).as_expr())?;
        ind.dedent()?;

        let self_type_str = match &func_data.self_type {
            Some(ty) if qualify_self_typ => {
                let fq_type = self.emit_fully_qualified_type(ty);
                format!("{fq_type}::")
            }
            _ => String::new(),
        };

        // Now we can actually build our function
        let result = formatdoc! {
            r"{prefix} {assoc_trait_string}{self_type_str}{fq_path}<{generics_string}>({parameters}) -> {ret_type} {{
            {body}
            }}"
        };

        if result.contains(&format!("{prefix} _::")) {
            // This is a dummy trait method that we don't care about, so we discard it.
            Ok(String::new())
        } else {
            Ok(result)
        }
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
    pub fn emit_fully_qualified_type(&self, typ: &Type) -> String {
        let str: String = match typ {
            Type::Array(elem_type, size) => {
                let elem_type = self.emit_fully_qualified_type(elem_type);

                format!("[{elem_type}; {size}]")
            }
            Type::Slice(elem_type) => {
                let elem_type = self.emit_fully_qualified_type(elem_type);

                format!("[{elem_type}]")
            }
            Type::Tuple(elems) => {
                let elem_types = elems
                    .iter()
                    .map(|typ| self.emit_fully_qualified_type(typ))
                    .collect_vec();
                let elems_str = elem_types.join(", ");

                format!("({elems_str})")
            }
            Type::Struct(struct_type, generics) => {
                let struct_type = struct_type.borrow();
                let module_id = struct_type.id.module_id();
                let name = self
                    .context
                    .fully_qualified_struct_path(&module_id.krate, struct_type.id);

                let generics_resolved = generics
                    .iter()
                    .map(|g| self.emit_fully_qualified_type(g))
                    .collect_vec();
                let generics_str = generics_resolved.join(", ");

                format!("{name}<{generics_str}>")
            }
            Type::TraitAsType(trait_id, name, generics) => {
                let module_id = trait_id.0;
                let module_path = self.fq_module_name_from_mod_id(module_id);

                let generics_resolved = generics
                    .iter()
                    .map(|g| self.emit_fully_qualified_type(g))
                    .collect_vec();
                let generics_str = generics_resolved.join(", ");

                if module_path.is_empty() {
                    format!("{name}<{generics_str}>")
                } else {
                    format!("{module_path}::{name}<{generics_str}>")
                }
            }
            Type::Function(args, ret, environment) => {
                let arg_types = args
                    .iter()
                    .map(|arg| self.emit_fully_qualified_type(arg))
                    .collect_vec();
                let arg_types_str = arg_types.join(", ");
                let ret_str = self.emit_fully_qualified_type(ret);

                let env_string = environment.to_string();
                let env_string = env_string
                    .strip_prefix("(")
                    .expect("Environment did not contain a tuple type")
                    .strip_suffix(")")
                    .expect("Environment did not contain a tuple type");
                format!("{{{env_string}}} -> ({arg_types_str}) -> {ret_str}")
            }
            Type::MutableReference(typ) => {
                let typ_str = self.emit_fully_qualified_type(typ);
                format!("&mut {typ_str}")
            }
            // In all the other cases we can use the default printing as internal type vars are
            // non-existent, constrained to be types we don't care about customizing, or are
            // non-existent in the phase the emitter runs after.
            _ => format!("{typ}"),
        };

        str
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
    pub fn emit_expr(&self, ind: &mut Indenter, expr: ExprId) -> Result<String> {
        let expr_data = self.context.def_interner.expression(&expr);
        // Get the output type of this expression.
        let out_ty = self.context.def_interner.id_type(&expr);
        let out_ty_str = self.emit_fully_qualified_type(&out_ty);
        let expression = match expr_data {
            HirExpression::Block(block) => {
                let statements: Vec<String> = block
                    .statements
                    .iter()
                    .map(|stmt| {
                        let stmt_line = self.emit_statement(ind, *stmt)?;
                        Ok(ind.run(stmt_line))
                    })
                    .try_collect()?;
                statements.join("\n")
            }
            HirExpression::Infix(infix) => {
                let lhs_ty = self.context.def_interner.id_type(infix.lhs);
                let rhs_ty = self.context.def_interner.id_type(infix.rhs);
                let lhs_builtin_ty = lhs_ty.try_into().unwrap();
                let rhs_builtin_ty = rhs_ty.try_into().unwrap();
                let builtin_func_name = builtin::try_infix_as_builtin(
                    infix.operator.kind,
                    lhs_builtin_ty,
                    rhs_builtin_ty,
                )
                .expect("not a builtin");

                let lhs = self.emit_expr(ind, infix.lhs)?;
                let rhs = self.emit_expr(ind, infix.rhs)?;

                syntax::expr::format_infix_builtin_call(&builtin_func_name, &lhs, &rhs, &out_ty_str)
            }
            HirExpression::Prefix(prefix) => {
                let rhs_ty = self.context.def_interner.id_type(prefix.rhs);
                let rhs_builtin_ty = rhs_ty.try_into().unwrap();
                let builtin_func_name =
                    builtin::try_prefix_as_builtin(prefix.operator, rhs_builtin_ty)
                        .expect("not a builtin");

                let rhs = self.emit_expr(ind, prefix.rhs)?;

                syntax::expr::format_prefix_builtin_call(&builtin_func_name, &rhs, &out_ty_str)
            }
            HirExpression::Ident(ident, _generics) => {
                let name = self.context.def_interner.definition_name(ident.id);
                let ident_def = self.context.def_interner.definition(ident.id);

                match ident_def.kind {
                    DefinitionKind::Function(func) => {
                        let function_info = self.context.def_interner.function_meta(&func);
                        let self_type = match &function_info.self_type.as_ref() {
                            Some(s) => self.emit_fully_qualified_type(s),
                            None => String::new(),
                        };

                        let fn_name = if self_type.is_empty() {
                            name.to_string()
                        } else {
                            format!("{self_type}::{name}")
                        };

                        if let Some(builtin_fn_name) =
                            builtin::try_func_as_builtin(&fn_name, function_info)
                        {
                            syntax::expr::format_ident(&builtin_fn_name, true)
                        } else {
                            syntax::expr::format_ident(&fn_name, true)
                        }
                    }
                    DefinitionKind::Global(..)
                    | DefinitionKind::Local(..)
                    | DefinitionKind::GenericType(..) => syntax::expr::format_ident(name, false),
                }
            }
            HirExpression::Index(index) => {
                let collection = self.emit_expr(ind, index.collection)?;
                let index = self.emit_expr(ind, index.index)?;

                syntax::expr::format_index(&collection, &index)
            }
            HirExpression::Literal(lit) => self.emit_literal(ind, lit, expr)?,
            HirExpression::Constructor(constructor) => {
                let struct_def = constructor.r#type;
                let struct_def = struct_def.borrow();
                let name = &struct_def.name;
                let fields = constructor.fields;
                // Map a field name to its order.
                let field_orders: HashMap<_, usize> = (0..struct_def.num_fields())
                    .map(|i| {
                        let (k, _) = struct_def.field_at(i);
                        (k.clone(), i)
                    })
                    .collect();
                // Reorder the constructor fields before creating the string, so that they correspond to the order in the original definition.
                let fields_strings: Vec<String> = fields
                    .iter()
                    .sorted_by_key(|(i, _)| field_orders.get(i).cloned().unwrap_or_default())
                    .map(|(_, expr)| {
                        let expr_str = self.emit_expr(ind, *expr)?;
                        Ok(format!("{expr_str}"))
                    })
                    .try_collect()?;
                let fields_str = fields_strings.join(", ");
                let constructor_gen_vals_str = constructor
                    .struct_generics
                    .iter()
                    .map(|ty| self.emit_fully_qualified_type(ty))
                    .join(",");

                syntax::expr::format_constructor(name, &constructor_gen_vals_str, &fields_str)
            }
            HirExpression::MemberAccess(member) => {
                let lhs_expr_ty = self.context.def_interner.id_type(member.lhs);
                let struct_ty_str = match &lhs_expr_ty {
                    Type::Struct(..) => self.emit_fully_qualified_type(&lhs_expr_ty),
                    _ => panic!("member access lhs is not a struct"),
                };
                let target_expr_str = self.emit_expr(ind, member.lhs)?;
                let member_iden = member.rhs;

                syntax::expr::format_member_access(&struct_ty_str, &target_expr_str, member_iden)
            }
            HirExpression::Call(call) => {
                assert!(
                    !call.is_macro_call,
                    "Macros should be resolved before running this tool"
                );
                let function = self.emit_expr(ind, call.func)?;
                let args: Vec<_> = call
                    .arguments
                    .iter()
                    .map(|arg| self.emit_expr(ind, *arg))
                    .try_collect()?;
                let args_str = args.join(", ");
                let is_lambda = match self.context.def_interner.id_type(call.func) {
                    Type::Function(_, _, env) if matches!(*env, Type::Tuple(..)) => true,
                    _ => false,
                };

                syntax::expr::format_call(&function, &args_str, &out_ty_str, is_lambda)
            }
            HirExpression::MethodCall(method_call) => {
                let receiver = self.emit_expr(ind, method_call.object)?;
                let generics = match method_call.generics {
                    Some(gs) => {
                        let generic_strings =
                            gs.iter().map(|g| self.emit_fully_qualified_type(g)).collect_vec();
                        generic_strings.join(", ")
                    }
                    _ => String::new(),
                };

                let arguments: Vec<String> = method_call
                    .arguments
                    .iter()
                    .map(|arg| self.emit_expr(ind, *arg))
                    .try_collect()?;
                let args_string = arguments.join(", ");

                syntax::expr::format_method_call(&receiver, &generics, &args_string)
            }
            HirExpression::Cast(cast) => {
                let source = self.emit_expr(ind, cast.lhs)?;
                let target_type = self.emit_fully_qualified_type(&cast.r#type);

                syntax::expr::format_cast(&source, &target_type)
            }
            HirExpression::If(if_expr) => {
                let if_cond = self.emit_expr(ind, if_expr.condition)?;
                let then_exec = self.emit_expr(ind, if_expr.consequence)?;
                let else_exec = if let Some(expr) = if_expr.alternative {
                    Some(self.emit_expr(ind, expr)?)
                } else {
                    None
                };
                syntax::expr::format_ite(
                    &if_cond,
                    &then_exec,
                    else_exec.as_ref().map(|s| s.as_str()),
                )
            }
            HirExpression::Tuple(tuple) => {
                let item_exprs: Vec<String> =
                    tuple.iter().map(|expr| self.emit_expr(ind, *expr)).try_collect()?;
                let items = item_exprs.join(", ");

                syntax::expr::format_tuple(&items)
            }
            HirExpression::Lambda(lambda) => {
                let ret_type = self.emit_fully_qualified_type(&lambda.return_type);

                let arg_strs: Vec<String> = lambda
                    .parameters
                    .iter()
                    .map(|(pattern, ty)| {
                        let pattern_str = self.emit_pattern(pattern)?;
                        let typ = self.emit_fully_qualified_type(ty);

                        Ok(format!("{pattern_str} : {typ}"))
                    })
                    .try_collect()?;
                let args = arg_strs.join(", ");

                let captures = lambda
                    .captures
                    .iter()
                    .map(|capture| {
                        let capture_type =
                            self.context.def_interner.definition_type(capture.ident.id);
                        let name = self.context.def_interner.definition_name(capture.ident.id);

                        format!("{name} : {capture_type}")
                    })
                    .join(", ");

                let body = self.emit_expr(ind, lambda.body)?;

                syntax::expr::format_lambda(&captures, &args, &body, &ret_type)
            }
            HirExpression::Comptime(_) => {
                panic!("Comptime expressions should not exist after compilation is done")
            }
            HirExpression::Quote(_) => {
                panic!("Quote expressions should not exist after macro resolution")
            }
            HirExpression::Unquote(_) => {
                panic!("Unquote expressions should not exist after macro resolution")
            }
            HirExpression::Error => panic!("Encountered error expression where none should exist"),
        };

        Ok(expression)
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
    pub fn emit_statement(&self, ind: &mut Indenter, statement: StmtId) -> Result<String> {
        let stmt_data = self.context.def_interner.statement(&statement);

        let result = match stmt_data {
            HirStatement::Expression(expr) => self.emit_expr(ind, expr)?,
            HirStatement::Let(lets) => {
                let binding_type = self.emit_fully_qualified_type(&lets.r#type);
                let bound_expr = self.emit_expr(ind, lets.expression)?;
                let name = self.emit_pattern(&lets.pattern)?;

                syntax::stmt::format_let_in(&name, &binding_type, &bound_expr)
            }
            HirStatement::Constrain(constraint) => {
                let constraint_expr = self.emit_expr(ind, constraint.0)?;
                let print_expr = if let Some(expr) = constraint.2 {
                    Some(self.emit_expr(ind, expr)?)
                } else {
                    None
                };

                syntax::stmt::format_assert(
                    &constraint_expr,
                    print_expr.as_ref().map(|s| s.as_str()),
                )
            }
            HirStatement::Assign(assign) => {
                let l_val = self.emit_l_value(ind, &assign.lvalue)?;
                let expr = self.emit_expr(ind, assign.expression)?;

                syntax::stmt::format_assign(&l_val, &expr)
            }
            HirStatement::For(fors) => {
                let loop_var = self.context.def_interner.definition_name(fors.identifier.id);
                let loop_start = self.emit_expr(ind, fors.start_range)?;
                let loop_end = self.emit_expr(ind, fors.end_range)?;
                let body = self.emit_expr(ind, fors.block)?;

                syntax::stmt::format_for_loop(loop_var, &loop_start, &loop_end, &body)
            }
            HirStatement::Break => "break".into(),
            HirStatement::Continue => "continue".into(),
            HirStatement::Semi(semi) => self.emit_expr(ind, semi)?,
            HirStatement::Comptime(_) => {
                panic!("Comptime statements should not exist after compilation")
            }
            HirStatement::Error => panic!("Encountered error statement where none should exist"),
        };

        Ok(format!("{result};"))
    }

    /// Generates a Lean representation of a Noir l-value (something that can be
    /// assigned to).
    ///
    /// # Errors
    ///
    /// - [`Error`] if the extraction process fails for any reason.
    pub fn emit_l_value(&self, ind: &mut Indenter, l_val: &HirLValue) -> Result<String> {
        let result = match l_val {
            HirLValue::Ident(ident, ty) => {
                let ident_str = self.context.def_interner.definition_name(ident.id);
                let ty_str = self.emit_fully_qualified_type(ty);
                format!("({ident_str} : {ty_str})")
            }
            HirLValue::MemberAccess {
                object,
                field_name,
                typ,
                ..
            } => {
                let obj_str = self.emit_l_value(ind, object.as_ref())?;
                let typ_str = self.emit_fully_qualified_type(typ);

                format!("({obj_str}.{field_name} : {typ_str})")
            }
            HirLValue::Index {
                array, index, typ, ..
            } => {
                let array_expr = self.emit_l_value(ind, array.as_ref())?;
                let ix_expr = self.emit_expr(ind, *index)?;
                let typ_str = self.emit_fully_qualified_type(typ);

                format!("({array_expr}[{ix_expr}] : {typ_str})")
            }
            HirLValue::Dereference {
                lvalue,
                element_type,
                ..
            } => {
                let l_val_expr = self.emit_l_value(ind, lvalue.as_ref())?;
                let elem_ty = self.emit_fully_qualified_type(element_type);

                format!("(*{l_val_expr} : {elem_ty})")
            }
        };

        Ok(result)
    }

    /// Emits the Lean code corresponding to a Noir pattern.
    ///
    /// # Errors
    ///
    /// - [`Error`] if the extraction process fails for any reason.
    pub fn emit_pattern(&self, pattern: &HirPattern) -> Result<String> {
        let result = match pattern {
            HirPattern::Identifier(id) => {
                self.context.def_interner.definition_name(id.id).to_string()
            }
            HirPattern::Mutable(pattern, _) => {
                let child_pattern = self.emit_pattern(pattern.as_ref())?;
                format!("mut {child_pattern}")
            }
            HirPattern::Tuple(patterns, _) => {
                let pattern_strs: Vec<String> = patterns
                    .iter()
                    .map(|pattern| self.emit_pattern(pattern))
                    .try_collect()?;
                let patterns_str = pattern_strs.join(", ");

                format!("({patterns_str})")
            }
            HirPattern::Struct(struct_ty, patterns, _) => {
                let ty_str = self.emit_fully_qualified_type(struct_ty);

                let pattern_strs: Vec<String> = patterns
                    .iter()
                    .map(|(pat_name, pat_expr)| {
                        let child_pat = self.emit_pattern(pat_expr)?;

                        Ok(format!("{pat_name}: {child_pat}"))
                    })
                    .try_collect()?;
                let patterns_str = pattern_strs.join(", ");

                format!("{ty_str} {{{patterns_str}}}")
            }
        };

        Ok(result)
    }

    /// Emits the Lean source code corresponding to a Noir literal.
    ///
    /// # Errors
    ///
    /// - [`Error`] if the extraction process fails for any reason.
    pub fn emit_literal(
        &self,
        ind: &mut Indenter,
        literal: HirLiteral,
        expr: ExprId,
    ) -> Result<String> {
        let result = match literal {
            HirLiteral::Array(array) => self.emit_array_literal(ind, array)?,
            HirLiteral::Slice(slice) => {
                let array_lit = self.emit_array_literal(ind, slice)?;
                format!("&{array_lit}")
            }
            HirLiteral::Bool(bool) => {
                if bool {
                    "true".to_string()
                } else {
                    "false".to_string()
                }
            }
            HirLiteral::Integer(felt, neg) => {
                let typ = self.context.def_interner.id_type(expr).to_string();
                format!("{minus}{felt} : {typ}", minus = if neg { "-" } else { "" })
            }
            HirLiteral::Str(str) => {
                format!(r#""{str}""#)
            }
            HirLiteral::FmtStr(template, exprs) => {
                let expr_strings: Vec<String> =
                    exprs.iter().map(|expr| self.emit_expr(ind, *expr)).try_collect()?;
                let exprs = expr_strings.join(", ");

                format!(r#""{template}".fmt({exprs})"#)
            }
            HirLiteral::Unit => "()".into(),
        };

        Ok(result)
    }

    /// Emits the Lean code corresponding to a Noir array literal.
    ///
    /// # Errors
    ///
    /// - [`Error`] if the extraction process fails for any reason.
    pub fn emit_array_literal(
        &self,
        ind: &mut Indenter,
        literal: HirArrayLiteral,
    ) -> Result<String> {
        let result = match literal {
            HirArrayLiteral::Standard(elems) => {
                let elem_strings: Vec<String> =
                    elems.iter().map(|elem| self.emit_expr(ind, *elem)).try_collect()?;
                let elems_string = elem_strings.join(", ");

                format!("[{elems_string}]")
            }
            HirArrayLiteral::Repeated {
                repeated_element,
                length,
            } => {
                let elem = self.emit_expr(ind, repeated_element)?;
                let len_ty = self.emit_fully_qualified_type(&length);
                format!("[{elem}; {len_ty}]")
            }
        };

        Ok(result)
    }

    /// Generates a function parameter string from the provided parameters.
    ///
    /// # Errors
    ///
    /// - [`Error`] if the extraction process fails for any reason.
    pub fn function_param_string(&self, params: &Parameters) -> Result<String> {
        let result_params: Vec<String> = params
            .iter()
            .map(|(pattern, typ, vis)| {
                let name = self
                    .context
                    .def_interner
                    .definition_name(expect_identifier(pattern)?.id);
                let vis_string: String = match vis {
                    Visibility::Public => "pub ",
                    Visibility::Private => "",
                    Visibility::CallData(_) => "call_data ",
                    Visibility::ReturnData => "ret_data ",
                }
                .into();

                let qualified_type = self.emit_fully_qualified_type(typ);

                Ok(format!("{name} : {vis_string}{qualified_type}"))
            })
            .try_collect()?;

        Ok(result_params.join(", "))
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

impl From<LeanEmitter> for Context<'static, 'static> {
    fn from(value: LeanEmitter) -> Self {
        value.context
    }
}

// TODO Proper emit tests
