use indoc::formatdoc;
use itertools::Itertools;

// Drops the generic arguments wrapped between angled brackets from a string of form `T<...>`.
fn without_generic_args(ty_str: &str) -> String {
    let mut ty_str = ty_str.to_string();
    let Some(left_bracket_idx) = ty_str.find('<') else {
        return ty_str;
    };
    let Some(right_bracket_idx) = ty_str.rfind('>') else {
        return ty_str;
    };
    ty_str.replace_range(left_bracket_idx..(right_bracket_idx + 1), "");
    ty_str
}

fn normalize_ident(ident: &str) -> String {
    ident.split("::").map(|p| without_generic_args(p)).join("::")
}

#[inline]
pub(super) fn format_struct_def(name: &str, def_generics: &str, fields: &str) -> String {
    formatdoc! {
        r"nr_struct_def {name}<{def_generics}> {{
            {fields}
            }}"
    }
}

#[inline]
pub(super) fn format_trait_impl(
    impl_id: &str,
    impl_generics: &str,
    trait_name: &str,
    trait_generics: &str,
    target: &str,
    methods: &str,
    trait_constraints: &str,
) -> String {
    formatdoc! {
        "nr_trait_impl[{impl_id}] <{impl_generics}> {trait_name}<{trait_generics}> for {target} where {trait_constraints} {{
                {methods} 
            }}"
    }
}

#[inline]
pub(super) fn format_free_function_def(
    func_ident: &str,
    def_generics: &str,
    params: &str,
    ret_type: &str,
    body: &str,
) -> (String, String) {
    let func_ident = normalize_ident(func_ident);
    (
        func_ident.clone(),
        formatdoc! {
            r"nr_def «{func_ident}»<{def_generics}>({params}) -> {ret_type} {{
            {body}
            }}"
        },
    )
}

#[inline]
pub(super) fn format_trait_function_def(
    func_ident: &str,
    def_generics: &str,
    params: &str,
    ret_type: &str,
    body: &str,
) -> String {
    let func_ident = normalize_ident(func_ident);
    formatdoc! {
        r"fn {func_ident}<{def_generics}> ({params}) -> {ret_type} {{
            {body}
            }}"
    }
}

pub(super) mod r#type {
    #[inline]
    pub fn format_unit() -> String {
        format!("Unit")
    }

    #[inline]
    pub fn format_tuple(param_types: &str) -> String {
        format!("`({param_types})")
    }

    #[inline]
    pub fn format_slice(elem_type: &str) -> String {
        format!("[{elem_type}]")
    }

    #[inline]
    pub fn format_array(elem_type: &str, size: &str) -> String {
        format!("[{elem_type}; {size}]")
    }

    #[inline]
    pub fn format_struct(struct_name: &str, generics: &str) -> String {
        format!("{struct_name}<{generics}>")
    }

    #[inline]
    pub fn format_mut_ref(inner_type: &str) -> String {
        format!("&{inner_type}")
    }

    #[inline]
    pub fn format_trait_as_type(_trait_name: &str, _generics: &str) -> String {
        todo!("TraitAsType not implemented yet")
        // format!("?{trait_name}<{generics}>")
    }

    #[inline]
    pub fn format_function(param_types: &str, ret_type: &str) -> String {
        format!("λ({param_types}) → {ret_type}")
    }
}

pub(super) mod lval {
    use super::*;

    #[inline]
    pub fn format_member_access(struct_name: &str, lhs_lval: &str, member: &str) -> String {
        expr::format_member_access(struct_name, lhs_lval, member)
    }

    #[inline]
    pub fn format_tuple_access(lhs_lval: &str, member: &str) -> String {
        expr::format_tuple_access(lhs_lval, member)
    }

    #[inline]
    pub fn format_array_access(lhs_lval: &str, idx_expr: &str) -> String {
        expr::format_array_access(lhs_lval, idx_expr)
    }

    #[inline]
    pub fn format_slice_access(lhs_lval: &str, idx_expr: &str) -> String {
        expr::format_slice_access(lhs_lval, idx_expr)
    }

    #[inline]
    pub fn format_deref_access(lhs_lval: &str) -> String {
        expr::format_deref(lhs_lval)
    }
}

pub(super) mod expr {
    use crate::lean::builtin::BuiltinName;

    use super::*;

    #[inline]
    pub fn format_constructor(
        struct_ident: &str,
        struct_generic_vals: &str,
        fields_ordered: &str,
    ) -> String {
        format!("{struct_ident}<{struct_generic_vals}> {{ {fields_ordered} }}")
    }

    #[inline]
    pub fn format_call(func_expr: &str, func_args: &str, fn_type: &str) -> String {
        format!("({func_expr} as {fn_type})({func_args})")
    }

    #[inline]
    pub fn format_builtin_call(builtin_name: BuiltinName, func_args: &str, out_ty: &str) -> String {
        format!("#{builtin_name}({func_args}) : {out_ty}")
    }

    #[inline]
    pub fn format_member_access(struct_name: &str, target_expr: &str, member: &str) -> String {
        format!("({target_expr} as {struct_name}).{member}")
    }

    #[inline]
    pub fn format_tuple_access(target_expr: &str, member: &str) -> String {
        format!("{target_expr}.{member}")
    }

    #[inline]
    pub fn format_array_access(array_expr: &str, idx_expr: &str) -> String {
        format!("{array_expr}[{idx_expr}]")
    }

    #[inline]
    pub fn format_slice_access(slice_expr: &str, idx_expr: &str) -> String {
        format!("{slice_expr}[[{idx_expr}]]")
    }

    #[inline]
    pub fn format_deref(expr: &str) -> String {
        format!("*{expr}")
    }

    #[inline]
    pub fn format_ite(cond: &str, then_branch: &str, else_branch: Option<&str>) -> String {
        if let Some(else_branch) = else_branch {
            formatdoc! {
                r"if {cond} {{
                    {then_branch}
                }} else {{
                    {else_branch}
                }}"
            }
        } else {
            formatdoc! {
                r"if {cond} {{
                    {then_branch}
                }}"
            }
        }
    }

    #[inline]
    pub fn format_tuple(args: &str) -> String {
        format!("`({args})")
    }

    #[inline]
    pub fn format_var_ident(ident: &str) -> String {
        normalize_ident(ident)
    }

    #[inline]
    pub fn format_decl_func_ident(ident: &str, generics: &str) -> String {
        let ident = normalize_ident(ident);
        format!("@{ident}<{generics}>")
    }

    #[inline]
    pub fn format_trait_func_ident(
        sub_type: &str,
        trait_name: &str,
        trait_generics: &str,
        func_ident: &str,
        generics: &str,
    ) -> String {
        let func_ident = normalize_ident(func_ident);
        format!("({sub_type} as {trait_name}<{trait_generics}>)::{func_ident}<{generics}>")
    }

    #[inline]
    pub fn format_lambda(_captures: &str, args: &str, body: &str, ret_type: &str) -> String {
        format!("|{args}| -> {ret_type} {body}")
    }
}

pub(super) mod stmt {

    use super::*;

    #[inline]
    pub fn format_let_in(pat: &str, _binding_type: &str, bound_expr: &str) -> String {
        format!("let {pat} = {bound_expr}")
    }

    #[inline]
    pub fn format_for_loop(loop_var: &str, loop_start: &str, loop_end: &str, body: &str) -> String {
        formatdoc! {
            r"for {loop_var} in {loop_start} .. {loop_end} {{
                {body}
            }}
            "
        }
    }

    #[inline]
    pub fn format_assign(lhs: &str, rhs: &str) -> String {
        format!("{lhs} = {rhs}")
    }
}
