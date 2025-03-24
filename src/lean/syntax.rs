use indoc::formatdoc;
use itertools::Itertools;

/// Drops the generic arguments wrapped between angled brackets from a string of form `T<...>`.
fn without_generic_args(ty_str: &str) -> String {
    let mut ty_str = ty_str.to_string();
    let Some(left_bracket_idx) = ty_str.find('<') else {
        return ty_str;
    };
    let Some(right_bracket_idx) = ty_str.rfind('>') else {
        return ty_str;
    };
    ty_str.replace_range(left_bracket_idx..=right_bracket_idx, "");
    ty_str
}

/// Returns true if the given type string (extracted by `format_type`) is a slice or array type, e.g., `[T]`.
fn is_slice_or_array(ty_str: &str) -> bool {
    ty_str.starts_with('[') && ty_str.ends_with(']')
}

fn normalize_ident(ident: &str) -> String {
    ident
        .split("::")
        .map(without_generic_args)
        .filter(|p| !is_slice_or_array(p))
        .join("::")
}

fn escape_ident(ident: &str) -> String {
    ident.split("::").map(|s| format!("«{s}»")).join("::")
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
    let escaped_func_ident = escape_ident(&func_ident);
    (
        func_ident.clone(),
        formatdoc! {
            r"nr_def {escaped_func_ident}<{def_generics}>({params}) -> {ret_type} {{
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
    let escaped_func_ident = escape_ident(&func_ident);
    formatdoc! {
        r"fn {escaped_func_ident}<{def_generics}> ({params}) -> {ret_type} {{
            {body}
            }}"
    }
}

#[inline]
pub(super) fn format_generic_def(name: &str, is_num: bool, u_size: Option<u8>) -> String {
    if is_num {
        if let Some(w) = u_size {
            format!("@{name} : u{w}")
        } else {
            format!("@{name} : Field")
        }
    } else {
        name.to_string()
    }
}

#[inline]
pub(super) fn format_alias(alias_name: &str, generics: &str, typ: &str) -> String {
    format!("nr_type_alias {alias_name}<{generics}> = {typ}")
}

pub(super) mod literal {
    #[inline]
    pub fn format_bool(v: bool) -> String {
        if v {
            "true".to_string()
        } else {
            "false".to_string()
        }
    }

    #[inline]
    pub fn format_array(elems: &[String]) -> String {
        let elems_str = elems.join(", ");
        format!("[{elems_str}]")
    }

    #[inline]
    pub fn format_slice(elems: &[String]) -> String {
        let array_lit = format_array(elems);
        format!("&{array_lit}")
    }

    #[inline]
    pub fn format_repeated_array(elem: &str, rep: &str) -> String {
        format!("[{elem} ; {rep}]")
    }

    #[inline]
    pub fn format_repeated_slice(elem: &str, rep: &str) -> String {
        let array_lit = format_repeated_array(elem, rep);
        format!("&{array_lit}")
    }

    #[inline]
    pub fn format_num(val: &str, typ: &str) -> String {
        format!("{val} : {typ}")
    }

    pub fn format_unit() -> String {
        "#unit".to_string()
    }
}

pub(super) mod r#type {
    #[inline]
    pub fn format_unit() -> String {
        "Unit".to_string()
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
    pub fn format_function(param_types: &str, ret_type: &str) -> String {
        format!("λ({param_types}) → {ret_type}")
    }

    #[inline]
    pub fn format_alias(alias_name: &str, alias_generics: &str) -> String {
        format!("@{alias_name}<{alias_generics}>")
    }

    #[inline]
    pub fn format_placeholder() -> String {
        "_".to_string()
    }

    #[inline]
    pub fn format_uint_const(ident: &str, size: &str) -> String {
        format!("{ident} : u{size}")
    }

    #[inline]
    pub fn format_field_const(ident: &str) -> String {
        format!("{ident} : Field")
    }
}

pub(super) mod lval {
    use super::expr;

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

    use super::{formatdoc, normalize_ident};

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
    pub fn format_builtin_call(
        builtin_name: &BuiltinName,
        func_args: &str,
        out_ty: &str,
    ) -> String {
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
        format!("*({expr})")
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
        let var = normalize_ident(ident);
        // Replace placeholders `_` with a valid Lean identifier.
        let var = if var == "_" { "_?".to_string() } else { var };
        // The compiler seems to add intermediate variables with `$` prefix.
        // We have to replace these with valid Lean identifier characters.

        var.replace('$', "ζ")
    }

    #[inline]
    pub fn format_uint_const(ident: &str) -> String {
        let var = normalize_ident(ident);
        format!("u@{var}")
    }

    #[inline]
    pub fn format_field_const(ident: &str) -> String {
        let var = normalize_ident(ident);
        format!("f@{var}")
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
    pub fn format_lambda(args: &str, body: &str, ret_type: &str) -> String {
        format!("|{args}| -> {ret_type} {body}")
    }
}

pub(super) mod stmt {

    use super::formatdoc;

    #[inline]
    pub fn format_let_in(lhs: &str, rhs: &str) -> String {
        format!("let {lhs} = {rhs}")
    }

    #[inline]
    pub fn format_let_mut_in(lhs: &str, rhs: &str) -> String {
        format!("let mut {lhs} = {rhs}")
    }

    #[inline]
    pub fn format_for_loop(loop_var: &str, loop_start: &str, loop_end: &str, body: &str) -> String {
        formatdoc! {
            r"for {loop_var} in {loop_start} .. {loop_end} {{
                {body}
            }}"
        }
    }

    #[inline]
    pub fn format_assign(lhs: &str, rhs: &str) -> String {
        format!("{lhs} = {rhs}")
    }
}
