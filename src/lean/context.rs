use std::collections::HashMap;

use noirc_frontend::{
    hir::def_map::ModuleData,
    hir_def::{expr::HirExpression, stmt::HirStatement},
    node_interner::NodeInterner,
    Type,
};

pub struct EmitterCtx {
    // Maps an impl parameter type to a type variable name.
    impl_param_overrides: HashMap<Type, String>,
    // Maps an impl return type to the concrete type of the function body.
    impl_ret_overrides: HashMap<Type, Type>,
}

/// Returns true if and only if `typ` is an `impl` type.
pub(super) fn is_impl(typ: &Type) -> bool {
    match typ {
        Type::TypeVariable(_) | Type::TraitAsType(_, _, _) | Type::NamedGeneric(_, _)
            if typ.to_string().starts_with("impl") =>
        {
            true
        }
        _ => false,
    }
}

impl EmitterCtx {
    /// Builds the context from the module.
    pub fn from_module(module: &ModuleData, interner: &NodeInterner) -> Self {
        let mut impl_param_overrides = HashMap::new();
        let mut impl_ret_overrides = HashMap::new();
        // Get the function definitions from the module.
        let module_fns = module.value_definitions().flat_map(|value_def| match value_def {
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
                    let var_name = format!("I#{param_idx}");
                    impl_param_overrides.insert(typ.clone(), var_name);
                }
            }
            // Override the return type with the concrete type of the body.
            let ret_type = fn_meta.return_type();
            if is_impl(ret_type) {
                let fn_body = interner.function(&fn_id).as_expr();
                let fn_body_ret = interner.id_type(fn_body);
                match &fn_body_ret {
                    Type::TypeVariable(tv) | Type::NamedGeneric(tv, ..) => {
                        let fn_body_last_expr = match &interner.expression(&fn_body) {
                            HirExpression::Block(block_expr) => match block_expr
                                .statements()
                                .last()
                                .map(|stmt_id| interner.statement(stmt_id))
                            {
                                Some(HirStatement::Expression(expr_id)) => expr_id,
                                _ => fn_body,
                            },
                            _ => fn_body,
                        };
                        let bindings = interner.try_get_instantiation_bindings(fn_body_last_expr);
                        if let Some((_, _, subst_typ)) =
                            bindings.and_then(|bindings| bindings.get(&tv.id()))
                        {
                            if impl_param_overrides.contains_key(subst_typ) {
                                panic!("oh no!");
                            }
                        }
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
        self.impl_param_overrides.get(typ).map(|s| s.as_str())
    }

    pub fn get_impl_return<'a>(&'a self, typ: &Type) -> Option<&'a Type> {
        self.impl_ret_overrides.get(typ)
    }
}
