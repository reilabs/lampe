use crate::lean::{
    ast::{FunctionDefinition, GlobalDefinition, Module, TraitImplementation},
    emit::{context::EmitContext, writer::Writer},
};

/// An emitter for the generated module information in the AST.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ModuleEmitter {
    /// The context handling the emission.
    context: EmitContext,

    /// The module to emit.
    module: Module,
}

/// The basic interface to the module emitter.
impl ModuleEmitter {
    /// Creates a new emitter for the provided `module`.
    #[must_use]
    pub fn new(module: Module) -> ModuleEmitter {
        Self {
            context: EmitContext::default(),
            module,
        }
    }

    /// Emits code representing the module, consuming the emitter.
    #[must_use]
    pub fn emit(mut self) -> String {
        for global in &self.module.globals.clone() {
            self.emit_global(global);
            self.context.end_line();
        }

        for trait_impl in &self.module.trait_impls.clone() {
            self.emit_trait_impl(trait_impl);
            self.context.end_line();
        }

        for func_def in &self.module.functions.clone() {
            self.emit_function_definition(func_def);
            self.context.end_line();
        }

        self.context.consume()
    }
}

/// The actual functions for emitting the module components.
impl ModuleEmitter {
    /// Emits the code corresponding to the provided trait implementation.
    pub fn emit_function_definition(&mut self, function: &FunctionDefinition) {
        let mut writer = Writer::new(&mut self.context);

        writer.append_to_line("nr_def ");
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
                w.append_to_line(" : ");
                w.write_type_value(&p.typ, false);
            },
            ", ",
        );
        writer.append_to_line(")");
        writer.append_to_line(" -> ");
        writer.write_type_value(&function.return_type, false);
        writer.append_to_line(" := ");
        writer.write_expression(&function.body);
        writer.end_line();
    }

    /// Emits the code corresponding to the provided trait implementation.
    pub fn emit_trait_impl(&mut self, trait_impl: &TraitImplementation) {
        let mut writer = Writer::new(&mut self.context);

        writer.append_to_line("impl");
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
        writer.append_to_line(" as ");
        writer.append_to_line(&trait_impl.name);
        writer.finish_line_with_and_then_indent("{");

        for method in &trait_impl.methods {
            self.emit_function_definition(method);
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

        writer.append_to_line("nr_global_def ");
        writer.append_to_line(&global.name);
        writer.append_to_line(" : ");
        writer.write_type_value(&global.typ, false);
        writer.append_to_line(" = ");
        writer.write_expression(&global.expr);
        writer.append_to_line(";");
        writer.end_line();
    }
}
