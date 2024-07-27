use std::path::Path;
use nargo::parse_all;
use noirc_driver::{file_manager_with_stdlib, prepare_crate};
use noirc_frontend::{
    graph::{CrateId, CrateName},
    hir::{def_map::parse_file, Context, ParsedFiles},
};
use noirc_frontend::ast::BinaryOpKind;
use noirc_frontend::hir_def::expr::HirIdent;
use noirc_frontend::hir_def::stmt::{HirConstrainStatement, HirPattern};
use noirc_frontend::macros_api::{HirExpression, HirStatement};
use noirc_frontend::node_interner::{ExprId, StmtId};
use itertools::Itertools;

fn expect_identifier(pattern: &HirPattern) -> HirIdent {
    match pattern {
        HirPattern::Identifier(ident) => ident.clone(),
        _ => panic!("can only fetch hir ident from HirPattern::Identifier"),
    }
}

fn op_to_lean(op: BinaryOpKind) -> String {
    match op {
        BinaryOpKind::Equal => "=".to_string(),
        BinaryOpKind::NotEqual => "≠".to_string(),
        _ => "???????".to_string()
    }
}

fn expr_to_lean(context: &Context, expr: &ExprId) -> String {
    let expr = context.def_interner.expression(expr);
    match expr {
        HirExpression::Infix(infix) => {
            let lhs = expr_to_lean(context, &infix.lhs);
            let rhs = expr_to_lean(context, &infix.rhs);
            let op = op_to_lean(infix.operator.kind);
            format!("{} {} {}", lhs, op, rhs)
        }
        HirExpression::Ident(ident, _) => {
            let name = context.def_interner.definition_name(ident.id);
            name.to_string()
        }
        _ => {panic!("nope!")}
    }
}

fn stmt_to_lean(context: &Context, stmt: &StmtId, indent: String) -> String {
    let stmt = context.def_interner.statement(stmt);
    let unindented = match stmt {
        HirStatement::Constrain(HirConstrainStatement(expr, _, _)) => {
            let expr_str = expr_to_lean(context, &expr);
            format!("assert ({})", expr_str)
        }
        _ => panic!("unsupported")
    };
    format!("{}{}", indent, unindented)
}

fn main() {
    let root = Path::new("");
    let file_name = Path::new("main.nr");
    let mut file_manager = file_manager_with_stdlib(root);
    let source = r"
        fn main(x : Field, y : pub Field) {
            assert(x != y);
            assert(x == y);
        }
    ";
    file_manager.add_file_with_source(file_name, source.to_string()).expect(
        "Adding source buffer to file manager should never fail when file manager is empty",
    );
    let parsed_files = parse_all(&file_manager);
    let mut context = Context::new(file_manager, parsed_files);
    context.track_references();

    let root_crate_id = prepare_crate(&mut context, file_name);
    let _check_result = noirc_driver::check_crate(&mut context, root_crate_id, false, false, None);
    let main_func_id = context.get_main_function(&root_crate_id).unwrap();
    let meta = context.function_meta(&main_func_id);
    let fname = context.def_interner.definition_name(meta.name.id);
    let params = meta.parameters.iter().map(|(pat, ty, _)| {
        let name = context.def_interner.definition_name(expect_identifier(pat).id);
        format!("({} : {})", name, ty)
    }).join(" ");

    println!("def {} {} : NoirM Unit :=", fname, params);

    let func = context.def_interner.function(&main_func_id);
    let block = func.block(&context.def_interner);
    for stmt in block.statements() {
        println!("{}", stmt_to_lean(&context, stmt, "  ".to_string()));
    }
}
