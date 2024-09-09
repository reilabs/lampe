use std::any::Any;
use std::path::Path;
use nargo::parse_all;
use noirc_driver::{file_manager_with_stdlib, prepare_crate};
use noirc_frontend::{graph::{CrateId, CrateName}, hir::{def_map::parse_file, Context, ParsedFiles}, Type, TypeVariable, TypeVariableId, TypeVariableKind};
use noirc_frontend::ast::{BinaryOpKind, UnaryOp};
use noirc_frontend::hir_def::expr::HirIdent;
use noirc_frontend::hir_def::stmt::{HirAssignStatement, HirConstrainStatement, HirForStatement, HirLetStatement, HirLValue, HirPattern};
use noirc_frontend::macros_api::{HirExpression, HirLiteral, HirStatement, ModuleDefId};
use noirc_frontend::node_interner::{DefinitionKind, ExprId, FuncId, StmtId};
use itertools::Itertools;
use noirc_frontend::hir_def::function::FuncMeta;

fn expect_identifier(pattern: &HirPattern) -> HirIdent {
    match pattern {
        HirPattern::Identifier(ident) => ident.clone(),
        _ => panic!("can only fetch hir ident from HirPattern::Identifier"),
    }
}

fn op_to_lean(op: BinaryOpKind) -> String {
    match op {
        BinaryOpKind::Equal => "==".to_string(),
        BinaryOpKind::NotEqual => "!=".to_string(),
        BinaryOpKind::Add => "+".to_string(),
        BinaryOpKind::Subtract => "-".to_string(),
        BinaryOpKind::Divide => "/".to_string(),
        BinaryOpKind::Less => "<".to_string(),

        _ => panic!("unsupported {:?}", op)
    }
}

fn expr_to_lean(context: &Context, exprId: &ExprId, indent: &str) -> String {
    let expr = context.def_interner.expression(exprId);
    match expr {
        HirExpression::Infix(infix) => {
            let lhs = expr_to_lean(context, &infix.lhs, indent);
            let rhs = expr_to_lean(context, &infix.rhs, indent);
            let op = op_to_lean(infix.operator.kind);
            format!("({} {} {})", lhs, op, rhs)
        }
        HirExpression::Prefix(prefix) => {
            let rhs = expr_to_lean(context, &prefix.rhs, indent);
            let op = match prefix.operator {
                UnaryOp::Not => "!",
                _ => panic!("unsupported {:?}", prefix.operator)
            };
            format!("({}{})", op, rhs)
        }
        HirExpression::Ident(ident, generics) => {
            let def = context.def_interner.definition(ident.id);
            let generics2 = context.def_interner.get_instantiation_bindings(*exprId);
            println!("assigned gens: {:?}", generics2);
            let pfx = match def.kind {
                DefinitionKind::Function(id) => {
                    let fun = context.def_interner.function(&id);
                    let idType = context.def_interner.id_type(exprId);
                    match idType {
                        Type::Function(args, ret, boop) => {
                            println!("{} -> {}", args.iter().map(|t| format!("{}", t)).join(", "), ret);
                            let ret = ret.clone();
                            println!("{} -> {}", args.iter().map(|t| format!("{}", t)).join(", "), ret);
                        }
                        _ => panic!("expected function type, got {:?}", idType)
                    }
                    // let id_type_str = format!("{}", idType);
                    let meta = context.def_interner.function_meta(&id);
                    println!("all generics: {:?}", meta.all_generics);
                    let module_id = context.def_interner.function_module(id);
                    let krate = context.def_map(&module_id.krate).unwrap();
                    let name = context.fully_qualified_function_name(&module_id.krate, &id);
                    let (ix, data) = krate.modules().iter().find(|(i, _)| *i == module_id.local_id.0).unwrap();
                    let module = krate.get_module_path_with_separator(ix, data.parent, "::");
                    let self_type = match &meta.self_type {
                        Some(selfType) => format!("{}::", selfType),
                        None => "".to_string()
                    };
                    module + "::" + self_type.as_str()
                }
                _ => "".to_string()
            };
            let name = pfx + context.def_interner.definition_name(ident.id);
            name
        }
        HirExpression::Call(call) => {
            if call.is_macro_call {
                panic!("macros should be resolved by now");
            }


            let func = expr_to_lean(context, &call.func, indent);
            let args = call.arguments.iter().map(|arg| expr_to_lean(context, arg, indent)).join(", ");
            format!("{}({})", func, args)
        }
        HirExpression::Cast(cast) => {
            format!("({} #as {})", expr_to_lean(context, &cast.lhs, indent), cast.r#type)
        }
        HirExpression::Literal(HirLiteral::Integer(felt, neg)) => {
            if neg {
                todo!("negative literals")
            }
            format!("({}:{})", felt.to_string(), context.def_interner.id_type(exprId).to_string())
        }
        HirExpression::Literal(HirLiteral::Bool(b)) => {
            if b {
                "true".to_string()
            } else {
                "false".to_string()
            }
        }
        HirExpression::Block(block) => {
            let stmts = block.statements.iter().map(|stmt| stmt_to_lean(context, stmt, &format!("    {}", indent))).join("\n");
            format!("{{\n{}\n{}}}", stmts, indent)
        }
        HirExpression::If(ite) => {
            let cond = expr_to_lean(context, &ite.condition, indent);
            let then = expr_to_lean(context, &ite.consequence, indent);
            let else_ = ite.alternative.map(|e| format!(" else {}", expr_to_lean(context, &e, indent))).unwrap_or("".to_string());
            format!("if {} then {}{}", cond, then, else_)
        }
        HirExpression::Index(index) => {
            let collection = expr_to_lean(context, &index.collection, indent);
            let idx = expr_to_lean(context, &index.index, indent);
            format!("{}[{}]", collection, idx)
        }
        HirExpression::Constructor(cons) => {
            let cons_name = cons.r#type.borrow().name.clone();
            let ty_args = cons.struct_generics.iter().map(|t| format!("{}", t)).join(", ");
            let fields = cons.fields.iter().map(|(name, expr)| {
                let expr_str = expr_to_lean(context, expr, indent);
                format!("(\"{}\", {})", name, expr_str)
            }).join(", ");
            format!("Expr.constructor ({}.apply [{}]) [{}]", cons_name, ty_args, fields)
        }

        _ => { panic!("nope! {:?}", expr) }
    }
}

fn stmt_to_lean(context: &Context, stmt: &StmtId, indent: &str) -> String {
    let stmt = context.def_interner.statement(stmt);
    let unindented = match stmt {
        HirStatement::Constrain(HirConstrainStatement(expr, _, _)) => {
            let expr_str = expr_to_lean(context, &expr, indent);
            format!("assert({});", expr_str)
        }
        HirStatement::Let(HirLetStatement { pattern: HirPattern::Identifier(id), expression, .. }) => {
            let name = context.def_interner.definition_name(id.id);
            let expr_str = expr_to_lean(context, &expression, indent);
            format!("let {} = {};", name, expr_str)
        }
        HirStatement::Let(HirLetStatement { pattern: HirPattern::Mutable(id, _), expression, .. }) => {
            let name = context.def_interner.definition_name(expect_identifier(&id).id);
            let expr_str = expr_to_lean(context, &expression, indent);
            format!("let mut {} = {};", name, expr_str)
        }
        HirStatement::Expression(expr) => format!("{};", expr_to_lean(context, &expr, indent)),
        HirStatement::For(HirForStatement { start_range, end_range, identifier, block }) => {
            let start = expr_to_lean(context, &start_range, indent);
            let end = expr_to_lean(context, &end_range, indent);
            let name = context.def_interner.definition_name(identifier.id);
            let block_str = expr_to_lean(context, &block, indent);
            format!("for {} in {}..{} {};", name, start, end, block_str)
        }
        HirStatement::Assign(HirAssignStatement{lvalue: HirLValue::Ident(id, _), expression}) => {
            let name = context.def_interner.definition_name(id.id);
            let expr_str = expr_to_lean(context, &expression, indent);
            format!("{} = {};", name, expr_str)
        },
        _ => panic!("unsupported {:?}", stmt)
    };
    format!("{}{}", indent, unindented)
}

fn func_header(context: &Context, funId: &FuncMeta) -> String {
    let fname = context.def_interner.definition_name(funId.name.id);
    let params = funId.parameters.iter().map(|(pat, _, _)| {
        let name = context.def_interner.definition_name(expect_identifier(pat).id);
        name
    }).join(", ");
    format!("fn {}({})", fname, params)
}

fn function_to_lean(context: &Context, funId: &FuncId) -> String {
    let meta = context.function_meta(funId);
    let header = func_header(context, meta);

    let fun = context.def_interner.function(funId);

    let body_str = expr_to_lean(context, &fun.as_expr(), "");
    format!("{} {}", header, body_str)
}

fn main() {
    let root = Path::new("");
    let file_name = Path::new("main.nr");
    let mut file_manager = file_manager_with_stdlib(root);
    let source = r"
        use std::hash::{Hash, Hasher};
        use std::cmp::{Ordering, Ord, Eq};
        use std::default::Default;

        struct Option2<T> {
            _is_some: bool,
            _value: T,
        }

        impl <T> Option2<T> {
            /// Constructs a None value
            pub fn none() -> Self {
                Self { _is_some: false, _value: std::unsafe::zeroed() }
            }

            /// Constructs a Some wrapper around the given value
            pub fn some(_value: T) -> Self {
                Self { _is_some: true, _value }
            }
            //
            // /// True if this Option is None
            // pub fn is_none(self) -> bool {
            //     !self._is_some
            // }
            //
            // /// True if this Option is Some
            // pub fn is_some(self) -> bool {
            //     self._is_some
            // }
        }
    ";
    let fid = file_manager.add_file_with_source(file_name, source.to_string()).expect(
        "Adding source buffer to file manager should never fail when file manager is empty",
    );
    let parsed_files = parse_all(&file_manager);
    let mut context = Context::new(file_manager, parsed_files);
    context.track_references();


    let root_crate_id = prepare_crate(&mut context, file_name);
    let check_result = noirc_driver::check_crate(&mut context, root_crate_id, false, false, None);
    println!("{:?}", check_result);
    // for (trait_id, trait_impl) in context.def_interner.trait_implementations.iter().filter(|(_, imp)| imp.borrow().file == fid) {
    //     let imp = trait_impl.borrow();
    //     println!("impl! id:{:?} of {:?} for {:?}", trait_id, imp.trait_id, imp.typ);
    // }
    for module in context.def_map(&root_crate_id).unwrap().modules() {
        println!("module: {:?}", module.location);
        // println!("{:?}", module.parent);
        // for def in module.type_definitions() {
        //     match def {
        //         ModuleDefId::TraitId(traitId) => {
        //             let meta = context.def_interner.get_trait(traitId);
        //             // let tname = context.def_interner.definition_name(traitId);
        //             println!("trait {} : {:?}", meta.name,  meta);
        //         }
        //         _ => {}
        //     }
        // }
        for def in module.type_definitions() {
            match def {
                ModuleDefId::TypeId(structId) => {
                    let meta = context.def_interner.get_struct(structId);
                    let meta = meta.borrow();
                    let name = meta.name.clone();
                    // let generics_count = meta.generics.len();
                    // let generics: Vec<_> = meta.generics.iter().enumerate().map(|(i, g)| {
                    //     let var_id = TypeVariableId(generics_count - i - 1);
                    //     Type::TypeVariable(TypeVariable::unbound(var_id), TypeVariableKind::Normal)
                    // }).collect();
                    // let fields = meta.get_fields(&generics).iter().map(|(name, tpe)| {
                    //     let tpe_rep = match tpe {
                    //         Type::TypeVariable(tyVar, _) => format!("(BVar {})", tyVar.id().0),
                    //         other => format!("{}", other)
                    //     };
                    //     format!("(\"{}\", {})", name, tpe_rep)
                    // }).join(", ");

                    // let tname = context.def_interner.definition_name(traitId);
                    println!("def {} : Lampe.Type", name);
                }
                other => {
                    println!("{:?}", other);
                }
            }
        }
        for def in module.value_definitions() {
            match def {
                ModuleDefId::FunctionId(fun) => {
                    let local_generics = context.function_meta(&fun).all_generics.clone();
                    println!("defining gens: {:?}", local_generics);
                    let tp = context.function_meta(&fun).typ.clone();
                    match &tp {
                        Type::Forall(tvas, tp) =>
                            println!("{:?} -> {}", tvas, tp),
                        _ => {}
                    }
                    println!("{}", tp);
                    println!("{}", function_to_lean(&context, &fun));
                }
                other => {
                    println!("{:?}", other);
                }
            }
        }
    }
}
