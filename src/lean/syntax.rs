use indoc::formatdoc;
use noirc_frontend::macros_api::Ident;

const BUILTIN_PREFIX: &str = "#";

#[inline]
pub(super) fn format_trait_impl(
    impl_id: impl std::fmt::Display,
    impl_generics: impl std::fmt::Display,
    trait_name: impl std::fmt::Display,
    trait_generics: impl std::fmt::Display,
    target: impl std::fmt::Display,
    methods: impl std::fmt::Display,
) -> String {
    formatdoc! {
        "nr_trait_impl [{impl_id}] <{impl_generics}> {trait_name}<{trait_generics}> for {target} where {{
                {methods} 
            }}"
    }
}

pub(super) mod expr {
    use super::*;

    #[inline]
    pub fn format_constructor(
        struct_ident: &Ident,
        struct_generic_vals: &str,
        fields: &str,
    ) -> String {
        format!("{struct_ident}<{struct_generic_vals}> {{ {fields} }}")
    }

    #[inline]
    pub fn format_index(lhs_expr: &str, index: &str) -> String {
        format!("{lhs_expr}[{index}]")
    }

    #[inline]
    pub fn format_call(func_expr: &str, func_args: &str, out_ty: &str, is_lambda: bool) -> String {
        if is_lambda {
            format!("(^{func_expr}({func_args}) : {out_ty})")
        } else {
            format!("({func_expr}({func_args}) : {out_ty})")
        }
    }

    #[inline]
    pub fn format_method_call(receiver: &str, generic_vals: &str, args: &str) -> String {
        format!("{receiver}<{generic_vals}>({args})")
    }

    #[inline]
    pub fn format_member_access(struct_name: &str, target_expr: &str, member: Ident) -> String {
        format!("{struct_name} {target_expr} [{member}]")
    }

    #[inline]
    pub fn format_cast(source: &str, target_ty: &str) -> String {
        format!("{source} as {target_ty}")
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
    pub fn format_tuple(items: &str) -> String {
        format!("({items})")
    }

    #[inline]
    pub fn format_ident(ident: &str, is_builtin: bool) -> String {
        if is_builtin {
            format!("{BUILTIN_PREFIX}{ident}")
        } else {
            format!("{ident}")
        }
    }

    #[inline]
    pub fn format_infix_builtin_call(
        builtin_name: &str,
        lhs: &str,
        rhs: &str,
        ret_type: &str,
    ) -> String {
        format!("({BUILTIN_PREFIX}{builtin_name}({lhs}, {rhs}) : {ret_type})")
    }

    #[inline]
    pub fn format_prefix_builtin_call(builtin_name: &str, rhs: &str, ret_type: &str) -> String {
        format!("({BUILTIN_PREFIX}{builtin_name}({rhs}) : {ret_type})")
    }

    #[inline]
    pub fn format_lambda(_captures: &str, args: &str, body: &str, ret_type: &str) -> String {
        format!("|{args}| -> {ret_type} {body}")
    }
}

pub(super) mod stmt {
    use super::*;

    #[inline]
    pub fn format_let_in(name: &str, binding_type: &str, bound_expr: &str) -> String {
        format!("let {name}: {binding_type} = {bound_expr}")
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

    pub fn format_assert(constraint_expr: &str, print_expr: Option<&str>) -> String {
        if let Some(print_expr) = print_expr {
            format!("{BUILTIN_PREFIX}assert({constraint_expr}, {print_expr})")
        } else {
            format!("{BUILTIN_PREFIX}assert({constraint_expr})")
        }
    }

    pub fn format_assign(lhs: &str, rhs: &str) -> String {
        format!("{lhs} = {rhs}")
    }
}
