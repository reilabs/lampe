use noirc_frontend::{
    ast::Ident,
    hir_def::{expr::HirIdent, stmt::HirPattern},
    Type,
};

use super::{context::EmitterCtx, LeanEmitter};

#[derive(Clone, Debug)]
enum PatType {
    Tuple(usize),
    Struct { struct_type: Type, field: Ident },
}

/// The context of a pattern which contains all the necessary information to convert a nested `HirPattern::Identifier` pattern into a let (mut) binding.
/// This means, it contains the stack of tuple and struct patterns that the identifier is nested in, and whether the identifier is mutable.
#[derive(Clone, Debug, Default)]
struct PatCtx {
    stack: Vec<PatType>,
    is_mut: bool,
}

impl PatCtx {
    fn push(&mut self, pat_type: PatType) {
        self.stack.push(pat_type);
    }

    fn pop(&mut self) {
        self.stack.pop();
    }

    fn set_mut(&mut self, is_mut: bool) {
        self.is_mut = is_mut;
    }
}

#[derive(Clone, Debug)]
struct PatRes(/** lhs **/ HirIdent, /** rhs **/ PatCtx);

fn parse_pattern(pat: &HirPattern, ctx: &mut PatCtx) -> Vec<PatRes> {
    match pat {
        HirPattern::Identifier(hir_ident) => {
            vec![PatRes(hir_ident.clone(), ctx.clone())]
        }
        // A `mut` pattern makes the whole sub-pattern mutable.
        // Note that nested mut patterns are unnecessary, and they are forbidden by the compiler.
        HirPattern::Mutable(sub_pat, ..) => {
            ctx.set_mut(true);
            let res = parse_pattern(sub_pat, ctx);
            ctx.set_mut(false);
            res
        }
        HirPattern::Tuple(sub_pats, ..) => {
            let mut res = Vec::new();
            for (i, pat) in sub_pats.iter().enumerate() {
                ctx.push(PatType::Tuple(i));
                res.extend(parse_pattern(pat, ctx));
                ctx.pop();
            }
            res
        }
        HirPattern::Struct(struct_type, sub_pats, ..) => {
            let mut res = Vec::new();
            for (ident, pat) in sub_pats {
                ctx.push(PatType::Struct {
                    struct_type: struct_type.clone(),
                    field: ident.clone(),
                });
                res.extend(parse_pattern(pat, ctx));
                ctx.pop();
            }
            res
        }
    }
}

/// Emits the Lean code corresponding to a Noir pattern as a single `let` or `let mut` binding, along with the `HirIdent` at the lhs of the pattern.
/// Returns `None` if the pattern is not simple enough to be expressed as a single binding.
pub(super) fn try_format_simple_pattern(
    pat: &HirPattern,
    pat_rhs: &str,
    emitter: &LeanEmitter,
    ctx: &EmitterCtx,
) -> Option<(String, HirIdent)> {
    match pat {
        HirPattern::Identifier(ident) => format_pattern(pat, pat_rhs, emitter, ctx)
            .pop()
            .map(|pat| (pat, ident.clone())),
        HirPattern::Mutable(sub_pat, ..) => {
            if let HirPattern::Identifier(ident) = sub_pat.as_ref() {
                format_pattern(pat, pat_rhs, emitter, ctx)
                    .pop()
                    .map(|pat| (pat, ident.clone()))
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Emits the Lean code corresponding to a Noir pattern as a series of `let` or `let mut` bindings.
pub(super) fn format_pattern(
    pat: &HirPattern,
    pat_rhs: &str,
    emitter: &LeanEmitter,
    emitter_ctx: &EmitterCtx,
) -> Vec<String> {
    let mut ctx = PatCtx::default();
    parse_pattern(pat, &mut ctx)
        .into_iter()
        .map(|pat_res| {
            let PatRes(id, ctx) = pat_res;
            let lhs = emitter.context.def_interner.definition_name(id.id).to_string();
            let lhs = super::syntax::expr::format_var_ident(&lhs);
            let mut rhs = pat_rhs.to_string();
            for pat_type in ctx.stack {
                match pat_type {
                    PatType::Tuple(i) => {
                        rhs = super::syntax::expr::format_tuple_access(&rhs, &format!("{i}"));
                    }
                    PatType::Struct { struct_type, field } => {
                        let struct_name =
                            emitter.emit_fully_qualified_type(&struct_type, emitter_ctx);
                        rhs = super::syntax::expr::format_member_access(
                            &struct_name,
                            &rhs,
                            &field.to_string(),
                        );
                    }
                }
            }
            if ctx.is_mut {
                super::syntax::stmt::format_let_mut_in(&lhs, &rhs)
            } else {
                super::syntax::stmt::format_let_in(&lhs, &rhs)
            }
        })
        .collect()
}
