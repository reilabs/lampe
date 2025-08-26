use crate::lean::{
    ast::{StructDefinition, TraitDefinition, TypeAlias, TypeDefinition},
    emit::{context::EmitContext, writer::Writer},
};

/// An emitter for the generated type information in the AST.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TypesEmitter {
    /// The context handling the emission.
    context: EmitContext,

    /// The type definitions to emit.
    types: Vec<TypeDefinition>,
}

/// The basic interface to the types emitter.
impl TypesEmitter {
    /// Creates a new emitter for the provided `types`.
    #[must_use]
    pub fn new(types: Vec<TypeDefinition>) -> TypesEmitter {
        Self {
            context: EmitContext::default(),
            types,
        }
    }

    /// Emits code representing the types, consuming the emitter.
    #[must_use]
    pub fn emit(mut self) -> String {
        for typ in self.types.clone() {
            match typ {
                TypeDefinition::Alias(alias) => self.emit_alias(&alias),
                TypeDefinition::Struct(struct_) => self.emit_struct(&struct_),
                TypeDefinition::Trait(trait_) => self.emit_trait(&trait_),
            }

            self.context.end_line();
        }

        self.context.consume()
    }
}

/// The functionality that actually implements the type emit.
impl TypesEmitter {
    /// Emits the code corresponding to a type alias into the current context.
    pub fn emit_alias(&mut self, alias: &TypeAlias) {
        let mut writer = Writer::new(&mut self.context);

        writer.append_to_line("noir_type_alias ");
        writer.append_to_line(&alias.name);

        writer.append_to_line("<");
        writer.write_sep_by(&alias.generics, Writer::write_type_pattern, ", ");
        writer.append_to_line(">");

        writer.append_to_line(" := ");
        writer.write_type_value(&alias.typ, false);
        writer.append_to_line(";");
        writer.end_line();
    }

    /// Emits the code corresponding to a type definition into the current
    /// context.
    pub fn emit_struct(&mut self, struct_: &StructDefinition) {
        let mut writer = Writer::new(&mut self.context);

        writer.append_to_line("noir_struct_def ");
        writer.append_to_line(&struct_.name);

        writer.append_to_line("<");
        writer.write_sep_by(&struct_.generics, Writer::write_type_pattern, ", ");
        writer.append_to_line(">");

        writer.space();

        if struct_.members.is_empty() {
            writer.append_to_line("{}");
            writer.end_line();
        } else {
            writer.finish_line_with_and_then_indent("{");

            for typ in &struct_.members {
                writer.write_type_value(typ, false);
                writer.append_to_line(",");
                writer.end_line();
            }

            writer.decrease_indent();
            writer.append_to_line("}");
            writer.end_line();
        }
    }

    /// Emits the code corresponding to a trait definition into the current
    /// context.
    pub fn emit_trait(&mut self, trait_: &TraitDefinition) {
        let mut writer = Writer::new(&mut self.context);

        writer.append_to_line("noir_trait_def ");
        writer.append_to_line(&trait_.name);
        writer.append_to_line("<");
        writer.write_sep_by(&trait_.generics, Writer::write_type_pattern, ", ");
        writer.append_to_line(">");
        writer.space();

        writer.append_to_line("[");
        writer.write_sep_by(&trait_.associated_types, Writer::write_type_pattern, ", ");
        writer.append_to_line("]");
        writer.append_to_line(" := ");

        if trait_.methods.is_empty() {
            writer.append_to_line("{}");
            writer.end_line();
        } else {
            writer.finish_line_with_and_then_indent("{");

            for method in &trait_.methods {
                writer.append_to_line("method ");
                writer.append_to_line(&method.name);

                writer.append_to_line("<");
                writer.write_sep_by(&method.generics, Writer::write_type_pattern, ", ");
                writer.append_to_line(">");

                writer.append_to_line("(");
                writer.write_sep_by(
                    &method.parameters,
                    |w, t| w.write_type_value(t, false),
                    ", ",
                );
                writer.append_to_line(")");
                writer.append_to_line(" -> ");
                writer.write_type_value(&method.return_type, false);
                writer.append_to_line(";");
                writer.end_line();
            }

            writer.decrease_indent();
            writer.append_to_line("}");
            writer.end_line();
        }
    }
}
