use crate::{
    file_generator::NoirPackageIdentifier,
    lean::{
        ast::{
            FunctionDefinition,
            GlobalDefinition,
            Module,
            ModuleDefinition,
            TraitImplementation,
            WhereClause,
        },
        emit::{context::EmitContext, writer::Writer},
    },
};

/// An emitter for the generated module information in the AST.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ModuleEmitter {
    /// The context handling the emission.
    context: EmitContext,

    //// The package that owns the module.
    package: NoirPackageIdentifier,

    /// The module to emit.
    module: Module,
}

/// The basic interface to the module emitter.
impl ModuleEmitter {
    /// Creates a new emitter for the provided `module`.
    #[must_use]
    pub fn new(package: NoirPackageIdentifier, module: Module) -> ModuleEmitter {
        Self {
            context: EmitContext::default(),
            package,
            module,
        }
    }

    /// Emits code representing the module, consuming the emitter.
    #[must_use]
    pub fn emit(mut self) -> String {
        for def in &self.module.entries.clone() {
            match def {
                ModuleDefinition::Global(g) => self.emit_global(g),
                ModuleDefinition::Function(f) => self.emit_function_definition(f, false),
                ModuleDefinition::TraitImpl(t) => self.emit_trait_impl(t),
            }

            self.context.end_line();
        }

        // Emit the environment
        self.emit_environment();

        self.context.consume()
    }
}

/// The actual functions for emitting the module components.
impl ModuleEmitter {
    /// Emits the code corresponding to the provided trait implementation.
    pub fn emit_function_definition(&mut self, function: &FunctionDefinition, with_semi: bool) {
        let mut writer = Writer::new(&mut self.context);

        writer.append_to_line("noir_def ");
        writer.append_to_line(&function.name);

        writer.append_to_line("<");
        writer.write_sep_by(&function.generics, Writer::write_type_pattern, ", ");
        writer.append_to_line(">");

        writer.append_to_line("(");
        writer.write_sep_by(
            &function.parameters,
            |w, p| {
                if p.is_mut {
                    w.append_to_line("mut ");
                }
                w.append_to_line(&p.name);
                w.append_to_line(": ");
                w.write_type_value(&p.typ, false);
            },
            ", ",
        );
        writer.append_to_line(")");
        writer.append_to_line(" -> ");
        writer.write_type_value(&function.return_type, false);
        writer.append_to_line(" := ");
        writer.write_expression(&function.body);
        if with_semi {
            writer.append_to_line(";");
        }
        writer.end_line();
    }

    /// Emits the code corresponding to the provided where clause.
    pub fn emit_where_clause(&mut self, where_clause: &WhereClause) {
        let mut writer = Writer::new(&mut self.context);

        writer.write_type_value(&where_clause.var, false);
        writer.append_to_line(": ");
        writer.write_type_value(&where_clause.bound, false);
    }

    /// Emits the code corresponding to the provided trait implementation.
    pub fn emit_trait_impl(&mut self, trait_impl: &TraitImplementation) {
        let mut writer = Writer::new(&mut self.context);

        writer.append_to_line("noir_trait_impl");
        writer.append_to_line("[");
        writer.append_to_line(&format!(
            "{}.{}",
            self.package.formatted(true),
            &trait_impl.name
        ));
        writer.append_to_line("]");

        writer.append_to_line("<");
        writer.write_sep_by(&trait_impl.generic_vars, Writer::write_type_pattern, ", ");
        writer.append_to_line(">");

        writer.space();
        writer.append_to_line(&trait_impl.trait_name);

        writer.append_to_line("<");
        writer.write_sep_by(
            &trait_impl.generic_vals,
            |w, t| w.write_type_value(t, false),
            ", ",
        );
        writer.append_to_line(">");

        writer.append_to_line(" for ");
        writer.write_type_value(&trait_impl.self_type, false);

        // Where clauses
        writer.append_to_line(" where [");

        for (ix, where_clause) in trait_impl.where_clauses.clone().iter().enumerate() {
            self.emit_where_clause(where_clause);

            if ix + 1 != trait_impl.where_clauses.len() {
                let mut writer = Writer::new(&mut self.context);
                writer.append_to_line(", ");
            }
        }

        // Avoiding mutability and ownership issues.
        let mut writer = Writer::new(&mut self.context);

        writer.append_to_line("]");

        // The body with method impls
        writer.finish_line_with_and_then_indent(" := {");

        for (i, method) in trait_impl.methods.iter().enumerate() {
            self.emit_function_definition(method, true);

            if i + 1 != trait_impl.methods.len() {
                self.context.end_line();
            }
        }

        // Avoid extending the lifetime of the mutable borrow into the loop where it is
        // not needed.
        let mut writer = Writer::new(&mut self.context);

        writer.decrease_indent();
        writer.append_to_line("}");
        writer.end_line();
    }

    /// Emits the code corresponding to the definition of a global.
    pub fn emit_global(&mut self, global: &GlobalDefinition) {
        let mut writer = Writer::new(&mut self.context);

        writer.append_to_line("noir_global_def ");
        writer.append_to_line(&global.name);
        writer.append_to_line(": ");
        writer.write_type_value(&global.typ, false);
        writer.append_to_line(" = ");
        writer.write_expression(&global.expr);
        writer.append_to_line(";");
        writer.end_line();
    }

    pub fn emit_environment(&mut self) {
        // Pre-compute the lists we need so we don't hold an immutable borrow of
        // self.module while a Writer (mutable borrow of self.context) is
        // active.
        let function_and_globals: Vec<_> = self
            .module
            .entries
            .iter()
            .filter(|def| {
                matches!(
                    def,
                    ModuleDefinition::Function(..) | ModuleDefinition::Global(..)
                )
            })
            .collect();
        let trait_impls: Vec<_> = self
            .module
            .entries
            .iter()
            .filter(|def| matches!(def, ModuleDefinition::TraitImpl(..)))
            .collect();

        let mut writer = Writer::new(&mut self.context);
        writer.append_to_line("def ");

        writer.append_to_line(&format!(
            "{}.{}.env",
            self.package.formatted(true),
            &self.module.name
        ));
        writer.append_to_line(" : Env := Env.mk");
        writer.end_line();
        writer.increase_indent();

        // Function & global decls
        writer.append_to_line("[");
        writer.write_sep_by(
            &function_and_globals,
            |w, def| w.append_to_line(&EmitContext::quote_name_if_needed(def.name())),
            ", ",
        );
        writer.append_to_line("]");

        writer.end_line();

        // Trait impl decls
        writer.append_to_line("[");
        writer.write_sep_by(
            &trait_impls,
            |w, def| {
                let namespace = self.package.formatted(true);
                let full_name = format!(
                    "{}.{}",
                    namespace,
                    &EmitContext::quote_name_if_needed(def.name())
                );
                w.append_to_line(&full_name);
            },
            ", ",
        );
        writer.append_to_line("]");
        writer.end_line();
    }
}
