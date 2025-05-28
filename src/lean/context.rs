use std::collections::HashMap;

use noirc_frontend::{Type, hir::def_map::ModuleData, node_interner::NodeInterner};

pub struct EmitterCtx {
    // Maps an impl parameter type to a type variable name.
    impl_param_overrides: HashMap<Type, String>,
    // Maps an impl return type to the concrete type of the function body.
    impl_ret_overrides: HashMap<Type, Type>,
}

/// Returns true if and only if `typ` is an `impl` type.
pub(super) fn is_impl(typ: &Type) -> bool {
    matches!(typ, Type::TypeVariable(_) | Type::TraitAsType(_,_,_) | Type::NamedGeneric(_) if typ.to_string().starts_with("impl"))
}

impl EmitterCtx {
    /// Builds the context from the module.
    pub fn from_module(module: &ModuleData, interner: &NodeInterner) -> Self {
        let mut impl_param_overrides = HashMap::new();
        let mut impl_ret_overrides = HashMap::new();
        // Get the function definitions from the module.
        let module_fns = module.value_definitions().filter_map(|value_def| match value_def {
            noirc_frontend::hir::def_map::ModuleDefId::FunctionId(func_id) => Some(func_id),
            _ => None,
        });
        // Iterate over the the functions in the module.
        for fn_id in module_fns {
            let fn_meta = interner.function_meta(&fn_id);
            // Override the parameters.
            let params = fn_meta.parameters.0.iter();
            for (param_idx, (_, typ, _)) in params.enumerate() {
                if is_impl(typ) {
                    let var_name = format!("μ{param_idx}");
                    impl_param_overrides.insert(typ.clone(), var_name);
                }
            }
            // Override the return type with the concrete type of the body.
            let ret_type = fn_meta.return_type();
            if is_impl(ret_type) {
                let fn_body = interner.function(&fn_id).as_expr();
                let fn_body_ret = interner.id_type(fn_body);
                // If the return type of the body is not a concrete type, then we fail.
                // As of Noir v1.0.0-beta.1, the compiler cannot handle these.
                match fn_body_ret {
                    Type::TypeVariable(_) | Type::TraitAsType(..) | Type::NamedGeneric(..) => {
                        todo!("impl returns that are not concrete types are not supported")
                    }
                    _ => {}
                }
                impl_ret_overrides.insert(ret_type.clone(), fn_body_ret);
            }
        }
        EmitterCtx {
            impl_param_overrides,
            impl_ret_overrides,
        }
    }

    pub fn get_impl_param<'a>(&'a self, typ: &Type) -> Option<&'a str> {
        self.impl_param_overrides.get(typ).map(std::string::String::as_str)
    }

    pub fn get_impl_return<'a>(&'a self, typ: &Type) -> Option<&'a Type> {
        self.impl_ret_overrides.get(typ)
    }
}
