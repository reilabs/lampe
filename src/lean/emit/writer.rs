use std::ops::{Deref, DerefMut};

use convert_case::{Case, Casing};
use itertools::Itertools;

use crate::{
    constants::LAMPE_STRUCT_METHOD_SEPARATOR,
    lean::{
        ast::{
            AssignStatement,
            Block,
            BuiltinCallRef,
            BuiltinTag,
            BuiltinTypeExpr,
            Call,
            Cast,
            CastTypeExpr,
            DataTypeExpr,
            DeclCallRef,
            Expression,
            ForStatement,
            FunctionTypeExpr,
            GlobalCallRef,
            IdentCallRef,
            Identifier,
            IfThenElse,
            Index,
            Kind,
            LValue,
            Lambda,
            LetStatement,
            Literal,
            MemberAccess,
            Pattern,
            Statement,
            TraitCallRef,
            Type,
            TypeArithExpr,
            TypeArithOp,
            TypeExpr,
            TypePattern,
        },
        builtin::{
            ALIAS_PREFIX,
            ARRAY_GET_BUILTIN_NAME,
            BUILTIN_PREFIX,
            CAST_BUILTIN_NAME,
            SKIP_BUILTIN_NAME,
            UNIT_TYPE_NAME,
        },
        emit::context::EmitContext,
    },
};

/// A provider of basic functionality for writing standard portions of the AST
/// into Lean DSL source code.
///
/// It should be dropped once it is finished being used.
#[derive(Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Writer<'emit_context> {
    context: &'emit_context mut EmitContext,
}

/// Basic utility functions for the writer.
impl Writer<'_> {
    /// Wraps the provided context in the basic writer.
    pub fn new(context: &mut EmitContext) -> Writer<'_> {
        Writer { context }
    }

    /// Writes each element of `elems` into the buffer using the provided
    /// `operation`, writing `sep` into the buffer after each operation except
    /// the last.
    pub fn write_sep_by<T>(&mut self, elems: &[T], operation: impl Fn(&mut Self, &T), sep: &str) {
        for (i, elem) in elems.iter().enumerate() {
            operation(self, elem);

            if i + 1 != elems.len() {
                self.append_to_line(sep);
            }
        }
    }

    /// Writes a literal space into the current buffer.
    pub fn space(&mut self) {
        self.append_to_line(" ");
    }
}

/// The functionality for actually writing using higher-level types.
impl Writer<'_> {
    /// Directly writes the contents of the provided expression into the
    /// builder.
    pub fn write_expression(&mut self, expr: &Expression) {
        match expr {
            Expression::Block(block) => self.write_block_expression(block),
            Expression::BuiltinCallRef(call_ref) => self.write_builtin_call_ref(call_ref),
            Expression::Call(call) => self.write_call_expression(call),
            Expression::Cast(cast) => self.write_cast_expression(cast),
            Expression::DeclCallRef(call_ref) => self.write_decl_call_ref(call_ref),
            Expression::Ident(ident) => self.write_identifier(ident, false),
            Expression::IdentCallRef(call_ref) => self.write_ident_call_ref(call_ref),
            Expression::IfThenElse(ite) => self.write_ite(ite),
            Expression::Index(index) => self.write_index(index),
            Expression::Lambda(lambda) => self.write_lambda(lambda),
            Expression::Literal(literal) => self.write_literal(literal),
            Expression::MemberAccess(member_access) => self.write_member_access(member_access),
            Expression::Skip => {
                self.append_to_line(BUILTIN_PREFIX);
                self.append_to_line(SKIP_BUILTIN_NAME);
            }
            Expression::TraitCallRef(call_ref) => self.write_trait_call_ref(call_ref),
            Expression::GlobalCallRef(call_ref) => self.write_global_call_ref(call_ref),
        }
    }

    /// Directly writes the contents of the provided statement into the builder.
    pub fn write_statement(&mut self, statement: &Statement) {
        match statement {
            Statement::Assign(assign) => self.write_assign(assign),
            Statement::Expression(expr) => {
                self.write_expression(expr);
                self.append_to_line(";");
            }
            Statement::For(for_loop) => self.write_for(for_loop),
            Statement::Let(lets) => self.write_let(lets),
        }
    }

    /// Directly writes the contents of the provided type into the builder,
    /// optionally including the kind information of the type.
    pub fn write_type_value(&mut self, typ: &Type, include_kind: bool) {
        self.write_type_expression(&typ.expr);

        // We ALWAYS want to kind-annotate expressions with a type not `Type`.
        let include_kind = include_kind || matches!(typ.kind, Kind::Field | Kind::U(_));

        if include_kind {
            self.append_to_line(": ");
            self.write_kind(&typ.kind);
        }
    }

    /// Directly writes the contents of the provided type expression into the
    /// builder.
    pub fn write_type_expression(&mut self, expr: &TypeExpr) {
        match expr {
            TypeExpr::Alias(data) => self.write_alias_type_expression(data),
            TypeExpr::Struct(data) => self.write_data_type_expression(data),
            TypeExpr::Arith(arith) => self.write_type_arith_expression(arith),
            TypeExpr::Builtin(builtin) => self.write_builtin_type_expression(builtin),
            TypeExpr::Cast(cast) => self.write_cast_type_expression(cast),
            TypeExpr::Function(function) => self.write_function_type_expression(function),
            TypeExpr::NumericConst(number) => self.append_to_line(number),
            TypeExpr::TypeVariable(var) => self.append_to_line(var),
        }
    }

    /// Directly writes the contents of the provided type pattern into the
    /// builder.
    pub fn write_type_pattern(&mut self, pattern: &TypePattern) {
        self.append_to_line(&pattern.pattern);
        self.append_to_line(": ");
        self.write_kind(&pattern.kind);
    }
}

impl Writer<'_> {
    /// Directly writes the contents of the let statement into the builder.
    pub fn write_let(&mut self, lets: &LetStatement) {
        self.append_to_line("let ");
        self.write_pattern(&lets.pattern);
        self.append_to_line(" = ");
        self.write_expression(&lets.expression);
        self.append_to_line(";");
    }

    /// Directly writes the contents of the assign statement into the builder.
    pub fn write_for(&mut self, for_loop: &ForStatement) {
        self.append_to_line("for ");
        self.append_to_line(&for_loop.loop_variable);
        self.append_to_line(" in ");
        self.write_expression(&for_loop.start_range);
        self.append_to_line(" .. ");
        self.write_expression(&for_loop.end_range);
        self.append_to_line(" do ");
        self.write_expression(&for_loop.body);
        self.append_to_line(";");
    }

    /// Directly writes the contents of the assign statement into the builder.
    pub fn write_assign(&mut self, assign: &AssignStatement) {
        self.write_lvalue(&assign.name);
        self.append_to_line(" = ");
        self.write_expression(&assign.expression);
        self.append_to_line(";");
    }

    /// Directly writes the contents of the lvalue into the builder.
    pub fn write_lvalue(&mut self, lvalue: &LValue) {
        match lvalue {
            LValue::Ident(ident) => {
                self.write_identifier(ident, false);
            }
            LValue::MemberAccess { object, index, typ } => {
                self.append_to_line("(");
                self.write_lvalue(object);
                self.append_to_line(".");
                self.append_to_line(&index.to_string());
                self.append_to_line(": ");
                self.write_type_value(typ, false);
                self.append_to_line(")");
            }
            LValue::ArrayIndex { array, index, typ } => {
                self.append_to_line("(");
                self.write_lvalue(array);
                self.append_to_line("[");
                self.write_expression(index);
                self.append_to_line("]");
                self.append_to_line(": ");
                self.write_type_value(typ, false);
                self.append_to_line(")");
            }
            LValue::SliceIndex { slice, index, typ } => {
                self.append_to_line("(");
                self.write_lvalue(slice);
                self.append_to_line("[[");
                self.write_expression(index);
                self.append_to_line("]]");
                self.append_to_line(": ");
                self.write_type_value(typ, false);
                self.append_to_line(")");
            }
            LValue::Dereference {
                object,
                element_type,
            } => {
                self.append_to_line("(");
                self.append_to_line("*");
                self.write_lvalue(object);
                self.append_to_line(": ");
                self.write_type_value(element_type, false);
                self.append_to_line(")");
            }
        }
    }

    /// Directly writes the contents of the trait call reference into the
    /// builder.
    pub fn write_trait_call_ref(&mut self, call_ref: &TraitCallRef) {
        self.append_to_line("(");
        self.append_to_line("(");
        self.write_type_value(&call_ref.self_type, false);
        self.append_to_line(" as ");

        self.append_to_line(&call_ref.trait_name);
        self.append_to_line("<");
        self.write_sep_by(
            call_ref.trait_generics.as_slice(),
            |s, t| Self::write_type_value(s, t, false),
            ", ",
        );
        self.append_to_line(">");
        self.append_to_line(")");

        self.append_to_line(LAMPE_STRUCT_METHOD_SEPARATOR);
        self.append_to_line(&call_ref.function_name);

        self.append_to_line("<");
        self.write_sep_by(
            call_ref.fun_generics.as_slice(),
            |s, t| Self::write_type_value(s, t, false),
            ", ",
        );
        self.append_to_line(">");

        self.append_to_line(" as ");

        self.write_type_expression(&TypeExpr::Function(FunctionTypeExpr {
            arguments:   call_ref.param_types.clone(),
            return_type: Box::new(call_ref.return_type.clone()),
            captures:    Box::new(Type::unit()),
        }));
        self.append_to_line(")");
    }

    /// Directly writes the contents of the builtin call reference expression
    /// into the builder.
    pub fn write_builtin_call_ref(&mut self, call_ref: &BuiltinCallRef) {
        self.append_to_line("(");
        self.append_to_line(BUILTIN_PREFIX);
        self.append_to_line(&call_ref.name.to_case(Case::Camel));
        self.append_to_line(" returning ");
        self.write_type_expression(&call_ref.return_type.expr);
        self.append_to_line(")");
    }

    /// Directly writes the contents of the ident call reference expression into
    /// the builder.
    pub fn write_ident_call_ref(&mut self, call_ref: &IdentCallRef) {
        self.append_to_line("(");
        self.append_to_line(&call_ref.name);
        self.append_to_line(" as ");
        self.write_type_expression(&call_ref.func_type);
        self.append_to_line(")");
    }

    /// Directly writes the contents of the decl call reference expression into
    /// the builder.
    pub fn write_decl_call_ref(&mut self, call_ref: &DeclCallRef) {
        self.append_to_line("(");
        self.append_to_line(&call_ref.function);

        self.append_to_line("<");
        self.write_sep_by(
            call_ref.generics.as_slice(),
            |s, t| Self::write_type_value(s, t, false),
            ", ",
        );
        self.append_to_line(">");

        self.append_to_line(" as ");
        self.write_type_expression(&TypeExpr::Function(FunctionTypeExpr {
            arguments:   call_ref.param_types.clone(),
            return_type: Box::new(call_ref.return_type.clone()),
            captures:    Box::new(Type::unit()),
        }));
        self.append_to_line(")");
    }

    /// Directly writes the contents of the global call reference into the
    /// builder.
    pub fn write_global_call_ref(&mut self, global_ref: &GlobalCallRef) {
        self.append_to_line("(");
        self.append_to_line(&global_ref.name);
        self.append_to_line("<>");
        self.append_to_line(" as λ() -> ");
        self.write_type_expression(&global_ref.typ.expr);
        self.append_to_line(")");
        // Globals are, under the hood, interpreted as functions with no parameters
        self.append_to_line("()");
    }

    /// Directly writes the contents of the member access into the builder.
    pub fn write_member_access(&mut self, member_access: &MemberAccess) {
        self.write_expression(&member_access.value);
        self.append_to_line(".");
        self.append_to_line(&member_access.index.to_string());
    }

    /// Directly writes the contents of the literal into the builder.
    ///
    /// # Panics
    ///
    /// - When encountering a malformed literal.
    pub fn write_literal(&mut self, literal: &Literal) {
        match literal {
            Literal::Bool(b) => {
                if *b {
                    self.append_to_line("#_true");
                } else {
                    self.append_to_line("#_false");
                }
            }
            Literal::ConstGeneric(typ) => {
                match &typ.kind {
                    Kind::Field => self.append_to_line("fConst!("),
                    Kind::U(_) => self.append_to_line("uConst!("),
                    Kind::Type => panic!("Encountered Type-kinded generic used as value"),
                }
                self.append_to_line(&typ.name);
                self.append_to_line(": ");
                self.write_kind(&typ.kind);
                self.append_to_line(")");
            }
            Literal::Numeric(lit) => {
                self.append_to_line("(");
                self.append_to_line(&lit.value);
                self.append_to_line(": ");
                self.write_type_value(&lit.typ, false);
                self.append_to_line(")");
            }
            Literal::String(str) => {
                self.append_to_line("\"");
                self.append_to_line(str);
                self.append_to_line("\"");
            }
            Literal::Unit => self.append_to_line("#_unit"),
        }
    }

    /// Directly writes the contents of the lambda into the builder.
    pub fn write_lambda(&mut self, lambda: &Lambda) {
        self.append_to_line("(");
        self.append_to_line("fn");
        self.append_to_line("(");
        self.write_sep_by(lambda.params.as_slice(), Self::write_lambda_parameter, ", ");
        self.append_to_line("):");
        self.space();
        self.write_type_value(&lambda.return_type, false);
        self.space();
        self.append_to_line(":=");
        self.space();
        self.write_expression(&lambda.body);
        self.append_to_line(")");
    }

    /// Directly writes the contents of the lambda parameter into the builder.
    pub fn write_lambda_parameter(&mut self, param: &(Pattern, Type)) {
        self.write_pattern(&param.0);
        self.append_to_line(": ");
        self.write_type_value(&param.1, false);
    }

    /// Directly writes the contents of the pattern into the builder.
    pub fn write_pattern(&mut self, pattern: &Pattern) {
        match pattern {
            Pattern::Identifier(ident) => {
                self.write_identifier(ident, false);
            }
            Pattern::Mutable(ident) => {
                self.append_to_line("mut ");
                self.write_pattern(ident);
            }
            Pattern::Tuple(pats) => {
                self.append_to_line("(");
                self.write_sep_by(pats, Self::write_pattern, ", ");
                self.append_to_line(")");
            }
            Pattern::Struct(pat) => {
                // We do structs by index here, so we simply delegate to the tuple
                // destructuring.
                self.write_pattern(&Pattern::Tuple(
                    pat.fields.iter().map(|(_, p)| p.clone()).collect_vec(),
                ));
            }
        }
    }

    /// Directly writes the contents of the index expression into the builder.
    pub fn write_index(&mut self, index: &Index) {
        self.append_to_line("(");
        self.append_to_line(ARRAY_GET_BUILTIN_NAME);
        self.append_to_line("(");
        self.write_expression(&index.value);
        self.write_expression(&index.index);
        self.append_to_line(")");
        self.append_to_line(")");
    }

    /// Directly writes the contents of the if-then-else expression into the
    /// builder.
    pub fn write_ite(&mut self, ite: &IfThenElse) {
        self.append_to_line("if ");
        self.write_expression(&ite.condition);
        self.append_to_line(" then ");
        self.write_expression(&ite.then_branch);
        ite.else_branch.iter().for_each(|branch| {
            self.append_to_line(" else ");
            self.write_expression(branch);
        });
    }

    /// Directly writes the contents of the cast expression into the builder.
    pub fn write_cast_expression(&mut self, cast: &Cast) {
        self.append_to_line("(");
        self.append_to_line(BUILTIN_PREFIX);
        self.append_to_line(CAST_BUILTIN_NAME);
        self.append_to_line(" returning ");
        self.write_type_value(&cast.target, false);
        self.append_to_line(")");
        self.append_to_line("(");
        self.write_expression(&cast.lhs);
        self.append_to_line(")");
    }

    /// Directly writes the contents of the call expression into the builder.
    pub fn write_call_expression(&mut self, call: &Call) {
        self.write_expression(&call.function);
        self.append_to_line("(");
        self.write_sep_by(call.params.as_slice(), Self::write_expression, ", ");
        self.append_to_line(")");
    }

    /// Directly writes the contents of the block expression into the builder.
    pub fn write_block_expression(&mut self, block: &Block) {
        if block.statements.is_empty() {
            if let Some(expr) = &block.expression {
                if let Expression::Block(_) = expr.as_ref() {
                    self.write_expression(expr);
                } else {
                    self.finish_line_with_and_then_indent("{");
                    self.write_expression(expr);
                    self.end_line();
                    self.decrease_indent();
                    self.append_to_line("}");
                }
            }
        } else {
            self.finish_line_with_and_then_indent("{");
            for statement in &block.statements {
                self.write_statement(statement);
                self.end_line();
            }

            if let Some(expr) = &block.expression {
                self.write_expression(expr);
                self.end_line();
            }

            self.decrease_indent();
            self.append_to_line("}");
        }
    }

    /// Directly writes the contents of the identifier into the builder.
    pub fn write_identifier(&mut self, ident: &Identifier, include_type: bool) {
        self.append_to_line(&ident.name);
        if include_type {
            self.append_to_line(": ");
            self.write_type_value(&ident.typ, false);
        }
    }

    /// Directly writes the contents of the function type expression into the
    /// builder.
    pub fn write_function_type_expression(&mut self, function: &FunctionTypeExpr) {
        self.append_to_line("λ(");
        self.write_sep_by(
            function.arguments.as_slice(),
            |s, t| Self::write_type_value(s, t, false),
            ", ",
        );
        self.append_to_line(") -> ");
        self.write_type_value(&function.return_type, false);
    }

    /// Directly writes the contents of the cast type expression into the
    /// builder.
    pub fn write_cast_type_expression(&mut self, cast: &CastTypeExpr) {
        // Cast expressions seem to be used solely with type level arithmetic
        // expressions.
        self.write_type_value(&cast.target, true);
    }

    /// Directly writes the contents of the builtin type expression into the
    /// builder.
    ///
    /// # Panics
    ///
    /// - When encountering a malformed reference builtin type.
    pub fn write_builtin_type_expression(&mut self, builtin: &BuiltinTypeExpr) {
        #[allow(clippy::match_same_arms)] // The similarity is incidental.
        match &builtin.tag {
            BuiltinTag::Array => {
                self.append_to_line("Array");
                self.append_to_line("<");
                self.write_sep_by(
                    builtin.generics.as_slice(),
                    |s, t| Self::write_type_value(s, t, false),
                    ", ",
                );
                self.append_to_line(">");
            }
            BuiltinTag::Bool => self.append_to_line("bool"),
            BuiltinTag::Field => self.append_to_line("Field"),
            BuiltinTag::FmtString => {
                self.append_to_line("FmtString");
                self.append_to_line("<");
                self.write_sep_by(
                    builtin.generics.as_slice(),
                    |s, t| Self::write_type_value(s, t, false),
                    ", ",
                );
                self.append_to_line(">");
            }
            BuiltinTag::I(n) => self.append_to_line(&format!("i{n}")),
            BuiltinTag::Quoted(_) => self.append_to_line(UNIT_TYPE_NAME),
            BuiltinTag::Reference(_) => {
                // We don't actually care about mutability, so all refs are the same to us.
                let mutability = "&";
                self.append_to_line(mutability);
                self.space();

                assert_eq!(builtin.generics.len(), 1, "Reference had too many generics");
                self.write_type_value(&builtin.generics[0], false);
            }
            BuiltinTag::Slice => {
                self.append_to_line("Slice");
                self.append_to_line("<");
                self.write_sep_by(
                    builtin.generics.as_slice(),
                    |s, t| Self::write_type_value(s, t, false),
                    ", ",
                );
                self.append_to_line(">");
            }
            BuiltinTag::String => {
                self.append_to_line("String");
                self.append_to_line("<");
                self.write_sep_by(
                    builtin.generics.as_slice(),
                    |s, t| Self::write_type_value(s, t, false),
                    ", ",
                );
                self.append_to_line(">");
            }
            BuiltinTag::Tuple => {
                self.append_to_line("Tuple");
                self.append_to_line("<");
                self.write_sep_by(
                    builtin.generics.as_slice(),
                    |s, t| Self::write_type_value(s, t, false),
                    ", ",
                );
                self.append_to_line(">");
            }
            BuiltinTag::U(n) => self.append_to_line(&format!("u{n}")),
            BuiltinTag::Unit => self.append_to_line(UNIT_TYPE_NAME),
        };
    }

    /// Directly writes the contents of the type arithmetic expression into the
    /// builder.
    pub fn write_type_arith_expression(&mut self, arith: &TypeArithExpr) {
        let op = match arith.op {
            TypeArithOp::Add => "+",
            TypeArithOp::Div => "/",
            TypeArithOp::Mod => "%",
            TypeArithOp::Mul => "*",
            TypeArithOp::Sub => "-",
        };

        self.append_to_line("(");
        self.write_type_expression(&arith.left);
        self.space();
        self.append_to_line(op);
        self.space();
        self.write_type_expression(&arith.right);
        self.append_to_line(")");
    }

    /// Directly writes the contents of the data-type expression into the
    /// builder.
    pub fn write_data_type_expression(&mut self, data_type: &DataTypeExpr) {
        self.append_to_line(&data_type.name);

        self.append_to_line("<");
        self.write_sep_by(
            data_type.generics.as_slice(),
            |s, t| Self::write_type_value(s, t, false),
            ", ",
        );
        self.append_to_line(">");
    }

    /// Directly writes the contents of the alias expression into the builder.
    pub fn write_alias_type_expression(&mut self, alias: &DataTypeExpr) {
        self.append_to_line(ALIAS_PREFIX);
        self.write_data_type_expression(alias);
    }

    /// Directly writes the content of the provided kind into the builder.
    pub fn write_kind(&mut self, kind: &Kind) {
        self.append_to_line(&match kind {
            Kind::Field => "Field".to_string(),
            Kind::Type => "Type".to_string(),
            Kind::U(n) => format!("u{n}"),
        });
    }
}

impl Deref for Writer<'_> {
    type Target = EmitContext;

    fn deref(&self) -> &Self::Target {
        self.context
    }
}

impl DerefMut for Writer<'_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.context
    }
}
