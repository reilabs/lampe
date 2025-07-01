use crate::lean::{ast::TypeDefinition, emit::context::EmitContext};

/// An emitter for the generated type information in the AST.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TypesEmitter {
    /// The context handling the emission.
    context: EmitContext,

    /// The type definitions to emit.
    types: Vec<TypeDefinition>,
}

impl TypesEmitter {
    /// Creates a new emitter for the provided `types`.
    pub fn new(types: Vec<TypeDefinition>) -> TypesEmitter {
        Self {
            context: EmitContext::default(),
            types,
        }
    }

    /// Emits code representing the types, consuming the emitter.
    pub fn emit(self) -> String {
        todo!("Types emit")
    }
}
