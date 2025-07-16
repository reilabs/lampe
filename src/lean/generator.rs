//! This module contains the logic for analyzing the Noir source code and
//! generating the Lean AST from it.

use std::{
    cell::Ref,
    cmp::Ordering,
    collections::{HashMap, HashSet},
    str::FromStr,
};

use fm::FileId;
use itertools::Itertools;
use noirc_errors::Location;
use noirc_frontend::{
    ast::{FunctionKind, Ident},
    graph::CrateId,
    hir::{
        def_map::{LocalModuleId, ModuleData, ModuleDefId},
        type_check::generics::TraitGenerics,
        Context,
    },
    hir_def::{
        expr::{
            HirArrayLiteral,
            HirBlockExpression,
            HirCallExpression,
            HirCastExpression,
            HirConstrainExpression,
            HirConstructorExpression,
            HirExpression,
            HirIdent,
            HirIfExpression,
            HirIndexExpression,
            HirInfixExpression,
            HirLambda,
            HirLiteral,
            HirMemberAccess,
            HirPrefixExpression,
        },
        function::{FuncMeta, Param},
        stmt::{
            HirAssignStatement,
            HirForStatement,
            HirLValue,
            HirLetStatement,
            HirPattern,
            HirStatement,
        },
        traits::{NamedType, TraitConstraint, TraitImpl},
    },
    node_interner::{
        DefinitionKind,
        DependencyId,
        ExprId,
        FuncId,
        GlobalId,
        StmtId,
        TraitId,
        TypeAliasId,
        TypeId,
    },
    shared::Signedness,
    token::FunctionAttributeKind,
    BinaryTypeOperator,
    DataType,
    Kind as NoirKind,
    NamedGeneric,
    QuotedType,
    ResolvedGeneric,
    Shared,
    StructField,
    Type as NoirType,
    TypeBinding,
    TypeBindings,
    TypeVariable,
    TypeVariableId,
};
use petgraph::data::DataMap;

use crate::lean::{
    ast::{
        AssignStatement,
        Block,
        BuiltinTag,
        BuiltinTypeExpr,
        Call,
        Cast,
        Constructor,
        Crate,
        DeclCallRef,
        Expression,
        ForStatement,
        FunctionDefinition,
        GlobalDefinition,
        Identifier,
        IfThenElse,
        Kind,
        LValue,
        Lambda,
        LetStatement,
        Literal,
        MemberAccess,
        Module,
        NumericLiteral,
        ParamDef,
        Pattern,
        Statement,
        StructDefinition,
        StructPattern,
        TraitCallRef,
        TraitDefinition,
        TraitImplementation,
        TraitMethodDeclaration,
        Type,
        TypeAlias,
        TypeArithOp,
        TypeDefinition,
        TypeExpr,
        TypePattern,
        WhereClause,
    },
    builtin,
    builtin::{BuiltinType, ASSERT_BUILTIN_NAME, TUPLE_BUILTIN_NAME},
    emit::context::EmitContext,
};

/// A generator for Lean definitions that correspond to the Noir project in
/// question.
pub struct LeanGenerator<'file_manager, 'parsed_files> {
    /// The compilation context for the Noir project.
    pub context: Context<'file_manager, 'parsed_files>,

    /// The identifier for the root crate in the Noir compilation context.
    root_crate: CrateId,

    /// The files contained in the root crate, used to filter out `std` and
    /// other crate files during generation.
    known_files: HashSet<FileId>,
}

/// Utility functions for the Lean generator.
impl<'file_manager, 'parsed_files> LeanGenerator<'file_manager, 'parsed_files> {
    /// Constructs a new lean generator from the provided compiler `context`.
    ///
    /// # Panics
    ///
    /// - If the provided `root_crate` is not available in the compilation
    ///   context.
    pub fn new(context: Context<'file_manager, 'parsed_files>, root_crate: CrateId) -> Self {
        let known_files = context
            .def_map(&root_crate)
            .expect("Root crate was missing in compilation context")
            .modules()
            .iter()
            .map(|(_, data)| data.location.file)
            .collect::<HashSet<_>>();

        Self {
            context,
            root_crate,
            known_files,
        }
    }

    /// Gets the root crate from the compilation context.
    pub fn root_crate(&self) -> CrateId {
        self.root_crate
    }
}

impl LeanGenerator<'_, '_> {
    /// Generates the set of Lean definitions that correspond to the Noir
    /// definitions in the compilation context.
    ///
    /// # Panics
    ///
    /// When encountering a bug in the output of the Noir compiler, or due to
    /// programmer error.
    pub fn generate(&self) -> Crate {
        let types = self.generate_types();
        let modules = self
            .known_files
            .iter()
            .map(|file| self.generate_module_contents(*file))
            .collect_vec();

        Crate { types, modules }
    }

    /// Generates the type definitions for the entire crate context.
    ///
    /// # Panics
    ///
    /// - If a cycle is found in the dependencies between type definitions.
    /// - If the root crate is not available in the compilation context.
    pub fn generate_types(&self) -> Vec<TypeDefinition> {
        let mut dep_graph = self.context.def_interner.dependency_graph().clone();

        // We only consider nodes in the dependency graph that could cause
        // issues with dependencies in the extracted Lean code; these are
        // structs, type aliases, and trait definitions.
        dep_graph.retain_nodes(|g, node_idx| {
            if let Some(dep_id) = g.node_weight(node_idx) {
                matches!(
                    dep_id,
                    DependencyId::Struct(_) | DependencyId::Alias(_) | DependencyId::Trait(_)
                )
            } else {
                false
            }
        });

        // We also need to allow for cases where a node may depend on itself. If
        // this recursive dependency was truly an issue, the Noir compiler would
        // already have complained.
        dep_graph.retain_edges(|g, e| {
            if let Some((start, end)) = g.edge_endpoints(e) {
                start != end
            } else {
                false
            }
        });

        // We then have to sort the dependency graph to emit these things in the
        // correct order.
        let dep_graph_sorted = petgraph::algo::toposort(&dep_graph, None)
            .expect("Cycle detected in dependencies between type definitions");

        let dep_weights = dep_graph_sorted
            .iter()
            .map(|id| dep_graph.node_weight(*id).unwrap())
            .collect_vec();

        let modules = self
            .context
            .def_map(&self.root_crate)
            .expect("Root crate was missing in the compilation context")
            .modules();

        let mut all_defs = Vec::default();

        for module in modules {
            let module_items = module.type_definitions().chain(module.value_definitions());
            let module_definitions = module_items
                .into_iter()
                .flat_map(|id| match id {
                    ModuleDefId::TypeId(id) => {
                        let def_order = dep_weights
                            .clone()
                            .into_iter()
                            .position(|item| *item == DependencyId::Struct(id));
                        let def = TypeDefinition::Struct(self.generate_struct_def(id));

                        vec![(def, def_order)]
                    }
                    ModuleDefId::TypeAliasId(id) => {
                        // Check if this is a dummy ID corresponding to an associated type
                        // FIXME: [#112] Is this the right way to handle this?
                        if id.0 == usize::MAX {
                            return vec![];
                        }

                        let def_order = dep_weights
                            .clone()
                            .into_iter()
                            .position(|item| *item == DependencyId::Alias(id));
                        let def = TypeDefinition::Alias(self.generate_alias(id));

                        vec![(def, def_order)]
                    }
                    ModuleDefId::TraitId(id) => {
                        let def_order = dep_weights
                            .clone()
                            .into_iter()
                            .position(|item| *item == DependencyId::Trait(id));
                        let def = TypeDefinition::Trait(self.generate_trait_definition(id));

                        vec![(def, def_order)]
                    }
                    _ => vec![],
                })
                .collect_vec();

            let module_definitions = module_definitions
                .into_iter()
                .sorted_by(|(l_def, l_ord), (r_def, r_ord)| {
                    #[allow(clippy::enum_glob_use)]
                    use TypeDefinition::*;
                    // We push traits toward the end of the file by force, because they are
                    // correctly tracked in the dependency graph, and we know that there are no
                    // structs and aliases depending on traits.
                    match (l_def, r_def) {
                        (Alias(_) | Struct(_), Trait(_)) => Ordering::Greater,
                        (Trait(_), Alias(_) | Struct(_)) => Ordering::Less,
                        _ => match (l_ord, r_ord) {
                            (Some(ord1), Some(ord2)) => ord1.cmp(ord2),
                            // If one of the definitions is not ordered, we push it towards the end,
                            // to increase the probability of it working in the absence of
                            // dependency info.
                            (None, Some(_)) => Ordering::Less,
                            (Some(_), None) => Ordering::Greater,
                            (None, None) => l_def.cmp(r_def),
                        },
                    }
                })
                .rev()
                .map(|(def, _)| def)
                .collect_vec();

            all_defs.extend(module_definitions);
        }

        all_defs
    }

    pub fn generate_struct_def(&self, id: TypeId) -> StructDefinition {
        let struct_data = self.context.def_interner.get_type(id);
        let struct_data = struct_data.borrow();
        let qualified_path = self
            .context
            .fully_qualified_struct_path(&struct_data.id.module_id().krate, id);

        let generics = struct_data
            .generics
            .iter()
            .map(|g| self.generate_lean_type_pattern_from_resolved_generic(g))
            .collect_vec();

        let fields = struct_data.get_fields_as_written().unwrap_or_default();
        let members = fields
            .into_iter()
            .map(|f| self.generate_lean_type_value(&f.typ))
            .collect_vec();

        StructDefinition {
            name: EmitContext::quote_name_if_needed(&qualified_path),
            generics,
            members,
        }
    }

    /// Generates a type _value_ from the provided `typ`.
    ///
    /// # Panics
    ///
    /// - If it encounters an unconstrained function type.
    /// - If it encounters a forall type, as these should be eliminated by the
    ///   time this tool is run.
    /// - If it encounters a quoted type, as these should have been processed by
    ///   the time this tool is run.
    /// - If it encounters a trait being used as a type, as these should have
    ///   been resolved to type variables by this point.
    /// - If it encounters the error type.
    pub fn generate_lean_type_value(&self, typ: &NoirType) -> Type {
        match typ {
            NoirType::FieldElement => Type {
                expr: TypeExpr::builtin(BuiltinTag::Field, &[]),
                kind: Kind::Type,
            },
            NoirType::Array(count, typ) => Type::array(
                self.generate_lean_type_value(typ).expr,
                self.generate_lean_type_value(count).expr,
            ),
            NoirType::Slice(typ) => Type::slice(self.generate_lean_type_value(typ).expr),
            NoirType::Integer(signedness, bit_size) => Type::integer(
                u64::from(bit_size.bit_size()),
                *signedness == Signedness::Signed,
            ),
            NoirType::Bool => Type::bool(),
            NoirType::String(count) => Type::string(self.generate_lean_type_value(count).expr),
            NoirType::FmtString(_, args) => {
                Type::fmt_string(self.generate_lean_type_value(args).expr)
            }
            NoirType::Unit => Type::unit(),
            NoirType::Tuple(elems) => {
                let elems = elems
                    .iter()
                    .map(|e| self.generate_lean_type_value(e).expr)
                    .collect_vec();
                Type::tuple(elems.as_slice())
            }
            NoirType::DataType(struct_type, generics) => {
                let type_def = struct_type.borrow();
                let module_id = type_def.id.module_id();
                let name = EmitContext::quote_name_if_needed(
                    &self
                        .context
                        .fully_qualified_struct_path(&module_id.krate, type_def.id),
                );
                let generics = generics
                    .iter()
                    .map(|g| self.generate_lean_type_value(g).expr)
                    .collect_vec();
                Type::data_type(&name, generics)
            }
            NoirType::Alias(alias, generics) => {
                let alias = alias.borrow();
                let name = EmitContext::quote_name_if_needed(alias.name.as_str());
                let generics = generics
                    .iter()
                    .map(|g| self.generate_lean_type_value(g).expr)
                    .collect_vec();
                Type::alias(&name, generics)
            }
            NoirType::TypeVariable(tv) => {
                self.generate_ty_var(tv, EmitContext::quote_name_if_needed(&format!("TV_{tv:?}")))
            }
            NoirType::NamedGeneric(ng) => self.generate_ty_var(
                &ng.type_var,
                EmitContext::quote_name_if_needed(ng.name.as_str()),
            ),
            NoirType::CheckedCast { to, .. } => Type::cast(self.generate_lean_type_value(to).expr),
            NoirType::Function(parameters, returns, captures, _) => {
                let parameters = parameters
                    .iter()
                    .map(|p| self.generate_lean_type_value(p).expr)
                    .collect_vec();
                let returns = self.generate_lean_type_value(returns).expr;
                let captures = self.generate_lean_type_value(captures).expr;
                Type::function(parameters, returns, captures)
            }
            NoirType::Reference(typ, mutable) => {
                let typ = self.generate_lean_type_value(typ).expr;
                if *mutable {
                    Type::mutable_reference(typ)
                } else {
                    Type::immutable_reference(typ)
                }
            }
            NoirType::Constant(felt, kind) => {
                let felt_value = felt.to_string();
                let kind = self.expect_constant_numeric_kind(kind);

                Type::numeric_const(&felt_value, kind)
            }
            NoirType::InfixExpr(left, op, right, _) => {
                let left = self.generate_lean_type_value(left).expr;
                let right = self.generate_lean_type_value(right).expr;
                let op = match op {
                    BinaryTypeOperator::Addition => TypeArithOp::Add,
                    BinaryTypeOperator::Subtraction => TypeArithOp::Sub,
                    BinaryTypeOperator::Multiplication => TypeArithOp::Mul,
                    BinaryTypeOperator::Division => TypeArithOp::Div,
                    BinaryTypeOperator::Modulo => TypeArithOp::Mod,
                };
                Type::infix(left, op, right)
            }
            NoirType::Quoted(quoted) => self.generate_quoted_type_value(quoted),
            NoirType::Forall(..) => panic!("Encountered forall type"),
            NoirType::TraitAsType(..) => {
                panic!("Encountered TraitAsType, but this should be resolved to a type variable")
            }
            NoirType::Error => panic!("Encountered error type"),
        }
    }

    pub fn generate_quoted_type_value(&self, typ: &QuotedType) -> Type {
        let tag = BuiltinTag::Quoted(
            match typ {
                QuotedType::Expr => "Expr",
                QuotedType::Quoted => "Quoted",
                QuotedType::TopLevelItem => "TopLevelItem",
                QuotedType::Type => "Type",
                QuotedType::TypedExpr => "TypedExpr",
                QuotedType::TypeDefinition => "TypeDefinition",
                QuotedType::TraitConstraint => "TraitConstraint",
                QuotedType::TraitDefinition => "TraitDefinition",
                QuotedType::TraitImpl => "TraitImpl",
                QuotedType::UnresolvedType => "UnresolvedType",
                QuotedType::FunctionDefinition => "FunctionDefinition",
                QuotedType::Module => "Module",
                QuotedType::CtString => "CtString",
            }
            .to_string(),
        );

        Type::builtin(
            TypeExpr::Builtin(BuiltinTypeExpr {
                tag,
                generics: Vec::default(),
            }),
            Kind::Type,
        )
    }

    pub fn generate_lean_type_pattern_from_resolved_generic(
        &self,
        rg: &ResolvedGeneric,
    ) -> TypePattern {
        self.generate_lean_type_pattern_from_tyvar(
            &rg.type_var,
            EmitContext::quote_name_if_needed(rg.name.as_str()),
        )
    }

    /// Generates a lean type pattern from the provided type variable `tv`.
    ///
    /// # Panics
    ///
    /// - If the provided `tv` does not contain a real type variable.
    pub fn generate_lean_type_pattern_from_tyvar(
        &self,
        tv: &TypeVariable,
        name: String,
    ) -> TypePattern {
        let typ = self.generate_ty_var(tv, EmitContext::quote_name_if_needed(&name));
        let kind = typ.kind;
        let TypeExpr::TypeVariable(pattern) = typ.expr else {
            panic!("Attempted to build type pattern from tyvar that did not contain a tyvar")
        };

        TypePattern { pattern, kind }
    }

    /// Generates a type pattern from the provided `typ`.
    ///
    /// # Panics
    ///
    /// - If a type pattern cannot be generated from `typ`.
    pub fn generate_lean_type_pattern_from_type(&self, typ: &NoirType) -> TypePattern {
        let (tv, name) = match typ {
            NoirType::TypeVariable(tv) => (tv, format!("TV_{tv:?}")),
            NoirType::NamedGeneric(ng) => (
                &ng.type_var,
                EmitContext::quote_name_if_needed(ng.name.as_str()),
            ),
            _ => panic!("Encountered illegal type {typ:?} to generate a pattern from"),
        };

        self.generate_lean_type_pattern_from_tyvar(tv, name)
    }

    /// Expects that the provided `kind` is a known numeric kind.
    ///
    /// # Panics
    ///
    /// - If a non-concrete numeric kind is encountered.
    pub fn expect_constant_numeric_kind(&self, kind: &NoirKind) -> Kind {
        match kind {
            NoirKind::Numeric(kind) => match self.generate_lean_type_value(kind).expr {
                TypeExpr::Builtin(BuiltinTypeExpr { tag, .. }) => match tag {
                    BuiltinTag::U(i) => Kind::U(i),
                    BuiltinTag::Field => Kind::Field,
                    _ => panic!("Invalid kind {tag:?} encountered for numeric kind"),
                },
                _ => panic!("Invalid kind {kind:?} encountered for numeric kind"),
            },
            _ => panic!("Invalid kind {kind} encountered for constant"),
        }
    }

    /// Generates a type corresponding to the provided Type Variable `tv`.
    ///
    /// # Panics
    ///
    /// - If a non-concrete kind is encountered.
    pub fn generate_ty_var(&self, tv: &TypeVariable, name: String) -> Type {
        match &*tv.borrow() {
            TypeBinding::Bound(b) => {
                let b = b.follow_bindings();
                self.generate_lean_type_value(&b)
            }
            TypeBinding::Unbound(_, kind) => {
                let kind = match kind {
                    NoirKind::Any | NoirKind::Normal => Kind::Type,
                    NoirKind::IntegerOrField | NoirKind::Integer => {
                        panic!("Kinds should be concrete at this stage")
                    }
                    NoirKind::Numeric(_) => self.expect_constant_numeric_kind(kind),
                };
                Type::variable(name, kind)
            }
        }
    }

    pub fn generate_alias(&self, id: TypeAliasId) -> TypeAlias {
        let alias_data = self.context.def_interner.get_type_alias(id);
        let alias_data = alias_data.borrow();
        let name = EmitContext::quote_name_if_needed(alias_data.name.as_str());
        let generics = alias_data
            .generics
            .iter()
            .map(|g| self.generate_lean_type_pattern_from_resolved_generic(g))
            .unique()
            .collect_vec();
        let aliased_type = self.generate_lean_type_value(&alias_data.typ);
        TypeAlias {
            name,
            typ: aliased_type,
            generics,
        }
    }

    pub fn generate_trait_definition(&self, id: TraitId) -> TraitDefinition {
        let trait_def = self.context.def_interner.get_trait(id);
        let name = EmitContext::quote_name_if_needed(
            &self.resolve_fq_trait_name_from_crate_id(trait_def.crate_id, id),
        );
        let trait_generics = trait_def
            .generics
            .iter()
            .map(|g| self.generate_lean_type_pattern_from_resolved_generic(g))
            .unique()
            .collect_vec();
        let associated_types = trait_def
            .associated_types
            .iter()
            .map(|t| self.generate_lean_type_pattern_from_resolved_generic(t))
            .unique()
            .collect_vec();

        let methods = trait_def
            .methods
            .iter()
            .map(|method| {
                let method_name = method.name.to_string();
                let method_generics = method
                    .direct_generics
                    .iter()
                    .map(|g| self.generate_lean_type_pattern_from_resolved_generic(g))
                    .filter(|g| !trait_generics.contains(g))
                    .unique()
                    .collect_vec();
                let parameters = method
                    .arguments()
                    .iter()
                    .map(|t| self.generate_lean_type_value(t))
                    .collect_vec();
                let out_type = self.generate_lean_type_value(method.return_type());

                TraitMethodDeclaration {
                    name: method_name,
                    generics: method_generics,
                    parameters,
                    return_type: Box::new(out_type),
                }
            })
            .collect_vec();

        TraitDefinition {
            name,
            generics: trait_generics,
            associated_types,
            methods,
        }
    }

    /// Generates the contents of the module contained in the file given by
    /// `id`.
    ///
    /// # Panics
    ///
    /// - If the root crate of the compilation context cannot be found.
    /// - If the file given by `id` has no module in the compilation context.
    pub fn generate_module_contents(&self, id: FileId) -> Module {
        let module_data = self
            .context
            .def_map(&self.root_crate)
            .expect("Root crate was missing in compilation context")
            .modules()
            .iter()
            .find(|(_, mod_data)| mod_data.location.file == id)
            .expect("File {id:?} had no module in the compilation context")
            .1;

        let trait_impls = self.generate_module_trait_impls(id);
        let ModuleDefs {
            func_defs: functions,
            global_defs: globals,
        } = self.generate_module_definitions(module_data);

        let trait_impls = trait_impls
            .into_iter()
            .sorted_by(|(loc_l, imp_l), (loc_r, imp_r)| {
                loc_l.cmp(loc_r).then_with(|| imp_l.cmp(imp_r))
            })
            .map(|(_, a)| a)
            .collect_vec();
        let functions = functions
            .into_iter()
            .sorted_by(|(loc_l, imp_l), (loc_r, imp_r)| {
                loc_l.cmp(loc_r).then_with(|| imp_l.cmp(imp_r))
            })
            .map(|(_, a)| a)
            .collect_vec();
        let globals = globals
            .into_iter()
            .sorted_by(|(loc_l, glob_l), (loc_r, glob_r)| {
                loc_l.cmp(loc_r).then_with(|| glob_l.cmp(glob_r))
            })
            .map(|(_, a)| a)
            .collect_vec();

        Module {
            id,
            globals,
            functions,
            trait_impls,
        }
    }

    pub fn generate_module_definitions(&self, module: &ModuleData) -> ModuleDefs {
        let mut globals = HashSet::new();
        let mut functions = HashSet::new();
        let module_defs = module.type_definitions().chain(module.value_definitions());

        for def in module_defs {
            match def {
                ModuleDefId::FunctionId(id) => {
                    let function_meta = self.context.function_meta(&id);

                    // Skip trait functions in the module scope that do not have bodies.
                    if function_meta.kind == FunctionKind::TraitFunctionWithoutBody {
                        continue;
                    }

                    // Skip trait methods as these are handled elsewhere.
                    if function_meta.trait_impl.is_some() {
                        continue;
                    }

                    // We cannot handle comptime functions ever, so we panic if we see one.
                    if self.context.def_interner.function_modifiers(&id).is_comptime {
                        continue;
                    }

                    let location = self.context.def_interner.function_modifiers(&id).name_location;

                    // We can now emit the function definition itself.
                    functions.insert((location, self.generate_free_function_def(&id)));
                }
                ModuleDefId::GlobalId(id) => {
                    let location = self.context.def_interner.get_global(id).location;
                    if let Some(def) = self.generate_global_definition(&id) {
                        globals.insert((location, def));
                    } else {
                        continue;
                    }
                }
                _ => continue,
            }
        }

        // Sort them for consistency
        let globals = globals.into_iter().sorted().collect_vec();
        let functions = functions.into_iter().sorted().collect_vec();

        ModuleDefs {
            func_defs:   functions,
            global_defs: globals,
        }
    }

    /// Generates the free function definition for the function given by `id`.
    ///
    /// # Panics
    ///
    /// - If an unsupported function kind is found for a builtin function.
    pub fn generate_free_function_def(&self, id: &FuncId) -> FunctionDefinition {
        let function_meta = self.context.function_meta(id);
        let generics = self.gather_function_generic_patterns(function_meta);
        let parameters = self.generate_function_parameters(function_meta);
        let return_type = self.generate_lean_type_value(function_meta.return_type());
        let is_unconstrained = self.is_function_unconstrained(&function_meta.typ);

        let body = if is_unconstrained {
            let call = self.generate_builtin_call("fresh", Vec::default(), return_type.clone());
            Expression::Block(Block {
                statements: Vec::default(),
                expression: Some(Box::new(call)),
            })
        } else if matches!(
            function_meta.kind,
            FunctionKind::Builtin | FunctionKind::LowLevel
        ) {
            let params = function_meta.parameters.iter().collect_vec();
            let func_kind = self
                .context
                .def_interner
                .function_attributes(id)
                .clone()
                .function
                .expect("Builtins must have attributes")
                .0
                .kind;
            let name = match func_kind {
                FunctionAttributeKind::Builtin(b) => b.to_string(),
                FunctionAttributeKind::Foreign(f) => f.to_string(),
                _ => panic!("Unsupported function kind {func_kind:?} encountered for builtin"),
            };
            let call = self.generate_builtin_call(&name, params, return_type.clone());
            Expression::Block(Block {
                statements: Vec::default(),
                expression: Some(Box::new(call)),
            })
        } else if function_meta.is_stub() {
            Expression::Block(Block {
                statements: Vec::default(),
                expression: None,
            })
        } else {
            self.generate_expr(self.context.def_interner.function(id).as_expr())
        };

        let name = EmitContext::quote_name_if_needed(
            &self
                .context
                .fully_qualified_function_name(&function_meta.source_crate, id),
        );

        FunctionDefinition {
            name,
            generics,
            parameters,
            return_type,
            body,
        }
    }

    /// Generates a call to the builtin function given by `name` with the
    /// provided `params`.
    ///
    /// # Panics
    ///
    /// - If the parameters are an invalid pattern type.
    pub fn generate_builtin_call(
        &self,
        name: &str,
        params: Vec<&Param>,
        return_type: Type,
    ) -> Expression {
        let call_identifier = Expression::BuiltinCallRef(name.to_string());
        let params = params
            .into_iter()
            .map(|p| match &p.0 {
                HirPattern::Identifier(ident) => {
                    let name = EmitContext::quote_name_if_needed(
                        &self.context.def_interner.definition_name(ident.id).to_string(),
                    );
                    let typ = self.generate_lean_type_value(
                        &self.context.def_interner.definition_type(ident.id),
                    );
                    Expression::Ident(Identifier { name, typ })
                }
                _ => panic!("Encountered unsupported pattern in the params of a builtin call"),
            })
            .collect_vec();
        let call_expr = Call {
            function: Box::new(call_identifier),
            params,
            return_type,
        };
        Expression::Call(call_expr)
    }

    pub fn gather_function_generic_values(&self, data: &FuncMeta) -> Vec<Type> {
        let all_generics_on_func = data
            .all_generics
            .iter()
            .map(|g| self.generate_lean_type_value(&NoirType::TypeVariable(g.type_var.clone())));

        let trait_gens =
            self.gather_trait_constraint_generics_values(data.trait_constraints.as_slice());

        all_generics_on_func
            .chain(trait_gens)
            .collect::<HashSet<_>>()
            .into_iter()
            .collect_vec()
    }

    pub fn gather_function_generic_patterns(&self, data: &FuncMeta) -> Vec<TypePattern> {
        let all_generics_on_func = data
            .all_generics
            .iter()
            .map(|g| self.generate_lean_type_pattern_from_resolved_generic(g))
            .unique();

        let trait_gens =
            self.gather_trait_constraint_generics_patterns(data.trait_constraints.as_slice());

        all_generics_on_func
            .chain(trait_gens)
            .collect::<HashSet<_>>()
            .into_iter()
            .collect_vec()
    }

    pub fn gather_trait_constraint_generics_values(
        &self,
        constraints: &[TraitConstraint],
    ) -> Vec<Type> {
        let mut generics = Vec::new();
        let mut seen = HashSet::<TypeVariableId>::new();
        for constraint in constraints {
            generics.extend(self.gather_unbound_vars_values(&constraint.typ, &mut seen));

            for gen in &constraint.trait_bound.trait_generics.ordered {
                generics.extend(self.gather_unbound_vars_values(gen, &mut seen));
            }

            for gen in &constraint.trait_bound.trait_generics.named {
                generics.extend(self.gather_unbound_vars_values(&gen.typ, &mut seen));
            }
        }

        generics
    }

    pub fn gather_trait_constraint_generics_patterns(
        &self,
        constraints: &[TraitConstraint],
    ) -> Vec<TypePattern> {
        let mut generics = Vec::new();
        let mut seen = HashSet::<TypeVariableId>::new();
        for constraint in constraints {
            generics.extend(self.gather_unbound_vars_patterns(&constraint.typ, &mut seen));

            for gen in &constraint.trait_bound.trait_generics.ordered {
                generics.extend(self.gather_unbound_vars_patterns(gen, &mut seen));
            }

            for gen in &constraint.trait_bound.trait_generics.named {
                generics.extend(self.gather_unbound_vars_patterns(&gen.typ, &mut seen));
            }
        }

        generics
    }

    pub fn gather_unbound_vars_values(
        &self,
        typ: &NoirType,
        seen: &mut HashSet<TypeVariableId>,
    ) -> Vec<Type> {
        match typ {
            NoirType::String(a) | NoirType::Slice(a) | NoirType::Reference(a, _) => {
                self.gather_unbound_vars_values(a, seen)
            }
            NoirType::Array(a, b) | NoirType::FmtString(a, b) => self
                .gather_unbound_vars_values(a, seen)
                .into_iter()
                .chain(self.gather_unbound_vars_values(b, seen))
                .collect_vec(),
            NoirType::DataType(_, generics) => generics
                .iter()
                .flat_map(|g| self.gather_unbound_vars_values(g, seen))
                .collect_vec(),
            NoirType::TypeVariable(tv) => match &*tv.borrow() {
                TypeBinding::Bound(tp) => self.gather_unbound_vars_values(tp, seen),
                TypeBinding::Unbound(id, _) => {
                    if seen.contains(id) {
                        Vec::default()
                    } else {
                        seen.insert(*id);
                        vec![self.generate_lean_type_value(&NoirType::TypeVariable(tv.clone()))]
                    }
                }
            },
            NoirType::NamedGeneric(ng) => match &*ng.type_var.borrow() {
                TypeBinding::Bound(tp) => self.gather_unbound_vars_values(tp, seen),
                TypeBinding::Unbound(id, _) => {
                    if seen.contains(id) {
                        Vec::default()
                    } else {
                        seen.insert(*id);
                        vec![self
                            .generate_lean_type_value(&NoirType::TypeVariable(ng.type_var.clone()))]
                    }
                }
            },
            _ => Vec::default(),
        }
    }

    pub fn gather_unbound_vars_patterns(
        &self,
        typ: &NoirType,
        seen: &mut HashSet<TypeVariableId>,
    ) -> Vec<TypePattern> {
        match typ {
            NoirType::String(a) | NoirType::Slice(a) | NoirType::Reference(a, _) => {
                self.gather_unbound_vars_patterns(a, seen)
            }
            NoirType::Array(a, b) | NoirType::FmtString(a, b) => self
                .gather_unbound_vars_patterns(a, seen)
                .into_iter()
                .chain(self.gather_unbound_vars_patterns(b, seen))
                .collect_vec(),
            NoirType::DataType(_, generics) => generics
                .iter()
                .flat_map(|g| self.gather_unbound_vars_patterns(g, seen))
                .collect_vec(),
            NoirType::TypeVariable(tv) => match &*tv.borrow() {
                TypeBinding::Bound(tp) => self.gather_unbound_vars_patterns(tp, seen),
                TypeBinding::Unbound(id, _) => {
                    if seen.contains(id) {
                        Vec::default()
                    } else {
                        seen.insert(*id);
                        vec![self.generate_lean_type_pattern_from_tyvar(
                            tv,
                            EmitContext::quote_name_if_needed(&format!("TV_{id}")),
                        )]
                    }
                }
            },
            NoirType::NamedGeneric(ng) => match &*ng.type_var.borrow() {
                TypeBinding::Bound(tp) => self.gather_unbound_vars_patterns(tp, seen),
                TypeBinding::Unbound(id, _) => {
                    if seen.contains(id) {
                        Vec::default()
                    } else {
                        seen.insert(*id);
                        vec![self.generate_lean_type_pattern_from_tyvar(
                            &ng.type_var,
                            EmitContext::quote_name_if_needed(ng.name.as_str()),
                        )]
                    }
                }
            },
            _ => Vec::default(),
        }
    }

    /// Generates parameters for the free function described by `data`.
    ///
    /// # Panics
    ///
    /// - If a malformed function parameter is encountered.
    pub fn generate_function_parameters(&self, data: &FuncMeta) -> Vec<ParamDef> {
        data.parameters
            .iter()
            .map(|(pattern, typ, ..)| {
                let typ = self.generate_lean_type_value(typ);
                match pattern {
                    HirPattern::Identifier(ident) => ParamDef {
                        name: EmitContext::quote_name_if_needed(
                            self.context.def_interner.definition_name(ident.id),
                        ),
                        typ,
                        is_mut: false,
                    },
                    HirPattern::Mutable(ident, _) => match ident.as_ref() {
                        HirPattern::Identifier(ident) => ParamDef {
                            name: EmitContext::quote_name_if_needed(
                                self.context.def_interner.definition_name(ident.id),
                            ),
                            typ,
                            is_mut: true,
                        },
                        _ => panic!("Missing identifier in function parameter"),
                    },
                    _ => panic!("Missing identifier in function parameter"),
                }
            })
            .collect_vec()
    }

    /// Generates the AST for a global definition corresponding to the Noir IR.
    ///
    /// # Panics
    ///
    /// - If the global definition pointed to by `id` is malformed.
    /// - If an invalid statement is found in a global binding.
    pub fn generate_global_definition(&self, id: &GlobalId) -> Option<GlobalDefinition> {
        let global_data = self.context.def_interner.get_global(*id);
        let statement = self.context.def_interner.statement(&global_data.let_statement);
        let def_info = self.context.def_interner.definition(global_data.definition_id);
        if def_info.comptime {
            return None;
        }

        match statement {
            HirStatement::Let(binding) => {
                let name = match binding.pattern {
                    HirPattern::Identifier(hir_ident) => EmitContext::quote_name_if_needed(
                        self.context.def_interner.definition_name(hir_ident.id),
                    ),
                    _ => panic!("Encountered a malformed global"),
                };

                let typ = self.generate_lean_type_value(&binding.r#type);
                let expr = self.generate_expr(binding.expression);

                Some(GlobalDefinition { name, typ, expr })
            }
            _ => panic!("Encountered invalid statement {statement:?} in global binding"),
        }
    }

    pub fn generate_module_trait_impls(
        &self,
        file: FileId,
    ) -> Vec<(Location, TraitImplementation)> {
        self.context
            .def_interner
            .trait_implementations()
            .iter()
            .filter_map(|(id, trait_impl)| {
                if trait_impl.borrow().file != file {
                    return None;
                }

                if matches!(trait_impl.borrow().typ, NoirType::Quoted(_)) {
                    return None;
                }

                let name = format!("impl_{:?}", id.0);
                let location = trait_impl.borrow().location;
                Some((
                    location,
                    self.generate_trait_impl(name, trait_impl.borrow()),
                ))
            })
            .collect_vec()
    }

    #[expect(clippy::similar_names, clippy::needless_pass_by_value)] // Makes the API better
    pub fn generate_trait_impl(
        &self,
        name: String,
        trait_impl: Ref<TraitImpl>,
    ) -> TraitImplementation {
        let trait_def_id = trait_impl.trait_id;
        let trait_def_data = self.context.def_interner.get_trait(trait_def_id);
        let trait_name = EmitContext::quote_name_if_needed(
            &self.resolve_fq_trait_name_from_crate_id(trait_def_data.crate_id, trait_def_id),
        );
        let self_type = self.generate_lean_type_value(&trait_impl.typ);

        let where_clauses = trait_impl
            .where_clause
            .iter()
            .map(|cons| {
                let var = self.generate_lean_type_value(&cons.typ);
                let trait_name = EmitContext::quote_name_if_needed(
                    self.context
                        .def_interner
                        .get_trait(cons.trait_bound.trait_id)
                        .name
                        .as_str(),
                );
                let bound = TypePattern {
                    pattern: trait_name,
                    kind:    Kind::Type,
                };
                let generics = &cons.trait_bound.trait_generics;
                let generics = generics
                    .ordered
                    .iter()
                    .chain(generics.named.iter().map(|g| &g.typ))
                    .map(|g| self.generate_lean_type_value(g))
                    .collect_vec();

                WhereClause {
                    var,
                    bound,
                    generics,
                }
            })
            .collect_vec();

        let generic_vals = trait_impl
            .trait_generics
            .iter()
            .map(|g| self.generate_lean_type_value(g))
            .collect_vec();

        let generic_vars = self
            .gather_trait_impl_generics(&trait_impl)
            .into_iter()
            .unique()
            .collect_vec();

        let methods = trait_impl
            .methods
            .iter()
            .map(|m| self.generate_trait_function_def(*m, &generic_vars))
            .collect_vec();

        TraitImplementation {
            name,
            trait_name,
            self_type,
            where_clauses,
            generic_vars,
            generic_vals,
            methods,
        }
    }

    pub fn gather_trait_impl_generics(&self, trait_impl: &TraitImpl) -> Vec<TypePattern> {
        let mut seen = HashSet::<TypeVariableId>::new();
        let mut patterns = Vec::default();

        for typ in &trait_impl.trait_generics {
            patterns.extend(self.gather_unbound_vars_patterns(typ, &mut seen));
        }

        patterns.extend(self.gather_unbound_vars_patterns(&trait_impl.typ, &mut seen));
        patterns.extend(
            self.gather_trait_constraint_generics_patterns(trait_impl.where_clause.as_slice()),
        );

        patterns
    }

    pub fn generate_trait_function_def(
        &self,
        id: FuncId,
        trait_generics: &[TypePattern],
    ) -> FunctionDefinition {
        // Note that we NEVER want to qualify the name of the trait function.
        let function_meta = self.context.function_meta(&id);
        let name = self.context.function_name(&id).to_string();

        let parameters = self.generate_function_parameters(function_meta);
        let return_type = self.generate_lean_type_value(function_meta.return_type());
        let generics = self
            .gather_function_generic_patterns(function_meta)
            .into_iter()
            .filter(|g| !trait_generics.contains(g))
            .unique()
            .collect_vec();
        let body = self.generate_expr(self.context.def_interner.function(&id).as_expr());

        FunctionDefinition {
            name,
            generics,
            parameters,
            return_type,
            body,
        }
    }

    /// Generates an arbitrary AST corresponding to an expression from Noir's
    /// IR.
    ///
    /// # Panics
    ///
    /// - If it encounters an enum construction expression, which is
    ///   unsupported.
    /// - If it encounters a match expression, which is unsupported.
    /// - If it encounters metaprogramming expressions, as these should have
    ///   been eliminated by this point.
    /// - If it encounters an error expression.
    pub fn generate_expr(&self, id: ExprId) -> Expression {
        let expression_data = self.context.def_interner.expression(&id);
        let output_type = self.generate_lean_type_value(&self.resolve_bound_type(id));

        match expression_data {
            HirExpression::Unsafe(block) | HirExpression::Block(block) => {
                self.generate_block_expression(&block)
            }
            HirExpression::Ident(ident, _) => {
                self.generate_ident_expression(id, &ident, &output_type)
            }
            HirExpression::Literal(literal) => self.generate_literal(&literal, &output_type),
            HirExpression::Prefix(prefix) => self.generate_prefix(&prefix, &output_type),
            HirExpression::Infix(infix) => self.generate_infix(&infix, &output_type),
            HirExpression::Index(index) => self.generate_index(&index, &output_type),
            HirExpression::Constructor(constructor) => self.generate_constructor(&constructor),
            HirExpression::MemberAccess(member) => self.generate_member_access(&member),
            HirExpression::Call(call) => self.generate_call(&call, &output_type),
            HirExpression::Constrain(constrain) => {
                self.generate_constrain(&constrain, &output_type)
            }
            HirExpression::Cast(cast) => self.generate_cast(&cast),
            HirExpression::If(cond) => self.generate_if(&cond),
            HirExpression::Tuple(tuple) => self.generate_tuple(tuple.as_slice()),
            HirExpression::Lambda(lambda) => self.generate_lambda(id, &lambda),
            HirExpression::EnumConstructor(_) => unimplemented!("Enum construction support"),
            HirExpression::Match(_) => unimplemented!("Match expression support"),
            HirExpression::Quote(_) | HirExpression::Unquote(_) => {
                panic!("Encountered metaprogramming expressions when these should be eliminated")
            }
            HirExpression::Error => panic!("Encountered error expression"),
        }
    }

    pub fn generate_lambda(&self, expr_id: ExprId, lambda: &HirLambda) -> Expression {
        let return_type = self.generate_lean_type_value(&lambda.return_type);
        let params = lambda
            .parameters
            .iter()
            .map(|(p, t)| {
                let pat = self.generate_pattern(p);
                let typ = self.generate_lean_type_value(t);
                (pat, typ)
            })
            .collect_vec();
        let captures = lambda
            .captures
            .iter()
            .map(|v| {
                let noir_type = self.context.def_interner.definition_type(v.ident.id);
                let ident_type = self.generate_lean_type_value(&noir_type);
                self.generate_ident_expression(expr_id, &v.ident, &ident_type)
            })
            .collect_vec();

        let body = Box::new(self.generate_expr(lambda.body));

        let lambda = Lambda {
            params,
            return_type,
            body,
            captures,
        };

        Expression::Lambda(lambda)
    }

    pub fn generate_pattern(&self, pattern: &HirPattern) -> Pattern {
        match pattern {
            HirPattern::Identifier(ident) => {
                let def_id = ident.id;
                let typ = self
                    .generate_lean_type_value(&self.context.def_interner.definition_type(def_id));
                let name = self.context.def_interner.definition_name(def_id).to_string();

                let ident = Identifier { name, typ };

                Pattern::Identifier(ident)
            }
            HirPattern::Mutable(pat, _) => {
                Pattern::Mutable(Box::new(self.generate_pattern(pat.as_ref())))
            }
            HirPattern::Tuple(pats, _) => {
                Pattern::Tuple(pats.iter().map(|p| self.generate_pattern(p)).collect())
            }
            HirPattern::Struct(typ, fields, _) => {
                let typ = self.generate_lean_type_value(typ);
                let fields = fields
                    .iter()
                    .map(|(i, p)| (i.to_string(), self.generate_pattern(p)))
                    .collect_vec();

                let struct_pat = StructPattern { typ, fields };
                Pattern::Struct(struct_pat)
            }
        }
    }

    pub fn generate_tuple(&self, elems: &[ExprId]) -> Expression {
        let fields = elems.iter().map(|e| self.generate_expr(*e)).collect_vec();
        let tuple = Constructor {
            name: TUPLE_BUILTIN_NAME.to_string(),
            generic_args: Vec::default(),
            fields,
        };

        Expression::Constructor(tuple)
    }

    pub fn generate_if(&self, cond: &HirIfExpression) -> Expression {
        let if_cond = self.generate_expr(cond.condition);
        let then_expr = self.generate_expr(cond.consequence);
        let else_expr = cond.alternative.map(|e| Box::new(self.generate_expr(e)));

        let ite = IfThenElse {
            condition:   Box::new(if_cond),
            then_branch: Box::new(then_expr),
            else_branch: else_expr,
        };

        Expression::IfThenElse(ite)
    }

    pub fn generate_constrain(
        &self,
        constrain: &HirConstrainExpression,
        output_type: &Type,
    ) -> Expression {
        let constraint_expr = self.generate_expr(constrain.0);
        let builtin_ref = Expression::BuiltinCallRef(ASSERT_BUILTIN_NAME.to_string());
        let call = Call {
            function:    Box::new(builtin_ref),
            params:      vec![constraint_expr],
            return_type: output_type.clone(),
        };

        Expression::Call(call)
    }

    /// Generates a call expression.
    ///
    /// # Panics
    ///
    /// - If the call is a macro, which should have been resolved before this
    ///   tool executes.
    pub fn generate_call(&self, call: &HirCallExpression, output_type: &Type) -> Expression {
        assert!(
            !call.is_macro_call,
            "Macros should be resolved before running this tool"
        );
        let params = call.arguments.iter().map(|a| self.generate_expr(*a)).collect_vec();
        let function_expr = self.generate_expr(call.func);

        let call = Call {
            function: Box::new(function_expr),
            params,
            return_type: output_type.clone(),
        };

        Expression::Call(call)
    }

    pub fn generate_cast(&self, cast: &HirCastExpression) -> Expression {
        let source_expr = self.generate_expr(cast.lhs);
        let target = self.generate_lean_type_value(&cast.r#type);

        let cast = Cast {
            lhs: Box::new(source_expr),
            target,
        };

        Expression::Cast(cast)
    }

    /// Generates a member access expression.
    ///
    /// # Panics
    ///
    /// - If the member access is attempted on a non-struct type.
    /// - If the provided field name is not a field of the target struct.
    pub fn generate_member_access(&self, member: &HirMemberAccess) -> Expression {
        let value_type = self.resolve_bound_type(member.lhs);
        let index = match value_type {
            NoirType::DataType(struct_def, _) => {
                let field_order = self.get_field_index_map(&struct_def);
                field_order
                    .get(&member.rhs)
                    .copied()
                    .unwrap_or_else(|| panic!("No index found for field with name {}", member.rhs))
            }
            NoirType::Tuple(_) => {
                let name = &member.rhs;
                usize::from_str(name.as_str()).expect("Could not parse tuple index to number")
            }
            _ => {
                panic!("Attempted to access member on non-struct or non-tuple type {value_type:?}")
            }
        };

        let value = Box::new(self.generate_expr(member.lhs));
        let member_access = MemberAccess { value, index };

        Expression::MemberAccess(member_access)
    }

    pub fn generate_constructor(&self, constructor: &HirConstructorExpression) -> Expression {
        let struct_def = &constructor.r#type;
        let struct_def = struct_def.borrow();
        let crate_id = self.root_crate;
        let name = EmitContext::quote_name_if_needed(
            &self.context.fully_qualified_struct_path(&crate_id, struct_def.id),
        );
        let fields = &constructor.fields;

        // We work with fields in _order_, so we need to turn these into orders.
        let field_orders = self.get_field_index_map(&constructor.r#type);

        // We then need to reorder the constructor fields before building the AST, so
        // that they correspond to the order in the original definition
        let fields = fields
            .iter()
            .sorted_by_key(|(i, _)| field_orders.get(i).copied().unwrap_or_default())
            .map(|(_, expr)| self.generate_expr(*expr))
            .collect_vec();

        let generic_args = constructor
            .struct_generics
            .iter()
            .map(|t| self.generate_lean_type_value(t))
            .collect_vec();

        let constructor = Constructor {
            name,
            generic_args,
            fields,
        };

        Expression::Constructor(constructor)
    }

    /// Generates an expression corresponding to indexing into a sequence.
    ///
    /// # Panics
    ///
    /// - If the index expression is not on a collection type.
    pub fn generate_index(&self, index: &HirIndexExpression, output_type: &Type) -> Expression {
        let collection_type = self.resolve_bound_type(index.collection);
        let collection_builtin_type: BuiltinType = self
            .unfold_alias(collection_type.clone())
            .try_into()
            .expect("Unable to resolve collection type in an index expression");

        let index_builtin_name = builtin::get_index_builtin_name(collection_builtin_type)
            .unwrap_or_else(|| panic!("Cannot index {collection_builtin_type:?}"));

        let call_target = Expression::BuiltinCallRef(index_builtin_name);
        let collection_expr = self.generate_expr(index.collection);
        let index_expr = self.generate_expr(index.index);
        let index_with_cast = Expression::Cast(Cast {
            lhs:    Box::new(index_expr),
            target: Type::integer(32, false),
        });

        let call = Call {
            function:    Box::new(call_target),
            params:      vec![collection_expr, index_with_cast],
            return_type: output_type.clone(),
        };

        Expression::Call(call)
    }

    pub fn generate_infix(&self, infix: &HirInfixExpression, output_type: &Type) -> Expression {
        let lhs = self.generate_expr(infix.lhs);
        let rhs = self.generate_expr(infix.rhs);
        let lhs_ty_noir = self.resolve_bound_type(infix.lhs);
        let rhs_ty_noir = self.resolve_bound_type(infix.rhs);

        let lhs_unfolded = self.unfold_alias(lhs_ty_noir.clone()).try_into().ok();
        let rhs_unfolded = self.unfold_alias(rhs_ty_noir.clone()).try_into().ok();

        let maybe_builtin = match (lhs_unfolded, rhs_unfolded) {
            (Some(lhs), Some(rhs)) => {
                builtin::try_infix_into_builtin_name(infix.operator.kind, lhs, rhs)
            }
            _ => None,
        };

        if let Some(builtin_name) = maybe_builtin {
            let builtin_target = Expression::BuiltinCallRef(builtin_name);
            let call = Call {
                function:    Box::new(builtin_target),
                params:      vec![lhs, rhs],
                return_type: output_type.clone(),
            };
            Expression::Call(call)
        } else {
            // If it doesn't correspond to a builtin call we need to convert it
            // into a trait call.
            let lhs_ty_lean = self.generate_lean_type_value(&lhs_ty_noir);
            let rhs_ty_lean = self.generate_lean_type_value(&lhs_ty_noir);
            let param_types = vec![rhs_ty_lean];
            let params = vec![lhs, rhs];
            let trait_method_id = self
                .context
                .def_interner
                .get_operator_trait_method(infix.operator.kind);
            let function_name = EmitContext::quote_name_if_needed(
                self.context
                    .def_interner
                    .definition_name(self.context.def_interner.trait_method_id(trait_method_id)),
            );
            let trait_name = EmitContext::quote_name_if_needed(
                self.context
                    .def_interner
                    .get_trait(trait_method_id.trait_id)
                    .name
                    .as_str(),
            );

            let call_target = TraitCallRef {
                trait_name,
                function_name,
                self_type: lhs_ty_lean,
                trait_generics: Vec::default(),
                fun_generics: Vec::default(),
                param_types,
                return_type: output_type.clone(),
            };

            let call = Call {
                function: Box::new(Expression::TraitCallRef(call_target)),
                params,
                return_type: output_type.clone(),
            };

            Expression::Call(call)
        }
    }

    /// Generates a prefix expression.
    ///
    /// # Panics
    ///
    /// - If no trait is found corresponding to the prefix operator.
    pub fn generate_prefix(&self, prefix: &HirPrefixExpression, output_type: &Type) -> Expression {
        let rhs = self.generate_expr(prefix.rhs);
        let rhs_ty = self.resolve_bound_type(prefix.rhs);
        let rhs_unfolded = self.unfold_alias(rhs_ty.clone()).try_into().ok();
        if let Some(builtin_name) =
            builtin::try_prefix_into_builtin_name(prefix.operator, rhs_unfolded)
        {
            let builtin_target = Expression::BuiltinCallRef(builtin_name);
            let call = Call {
                function:    Box::new(builtin_target),
                params:      vec![rhs],
                return_type: output_type.clone(),
            };
            Expression::Call(call)
        } else {
            // If the prefix call does not correspond to a builtin call, then we have to
            // treat it as a trait method call.
            let trait_method_id = self
                .context
                .def_interner
                .get_prefix_operator_trait_method(&prefix.operator)
                .unwrap_or_else(|| panic!("Found no trait corresponding to {:?}", prefix.operator));
            let function_name = EmitContext::quote_name_if_needed(
                self.context
                    .def_interner
                    .definition_name(self.context.def_interner.trait_method_id(trait_method_id)),
            );
            let corresponding_trait = self.context.def_interner.get_trait(trait_method_id.trait_id);
            let trait_name = EmitContext::quote_name_if_needed(corresponding_trait.name.as_str());

            let call_target = TraitCallRef {
                trait_name,
                function_name,
                self_type: self.generate_lean_type_value(&rhs_ty),
                trait_generics: Vec::default(),
                fun_generics: Vec::default(),
                param_types: vec![self.generate_lean_type_value(&rhs_ty)],
                return_type: output_type.clone(),
            };

            let call = Call {
                function:    Box::new(Expression::TraitCallRef(call_target)),
                params:      vec![rhs],
                return_type: output_type.clone(),
            };

            Expression::Call(call)
        }
    }

    pub fn generate_literal(&self, literal: &HirLiteral, output_type: &Type) -> Expression {
        match literal {
            HirLiteral::Array(arr) => match arr {
                HirArrayLiteral::Standard(elems) => {
                    let elems = elems.iter().map(|e| self.generate_expr(*e)).collect_vec();
                    let call = Call {
                        function:    Box::new(Expression::BuiltinCallRef("mkArray".to_string())),
                        params:      elems,
                        return_type: output_type.clone(),
                    };
                    Expression::Call(call)
                }
                HirArrayLiteral::Repeated {
                    repeated_element, ..
                } => {
                    let elem_expr = self.generate_expr(*repeated_element);
                    let call = Call {
                        function:    Box::new(Expression::BuiltinCallRef(
                            "mkRepeatedArray".to_string(),
                        )),
                        params:      vec![elem_expr],
                        return_type: output_type.clone(),
                    };
                    Expression::Call(call)
                }
            },
            HirLiteral::Slice(arr) => match arr {
                HirArrayLiteral::Standard(elems) => {
                    let elems = elems.iter().map(|e| self.generate_expr(*e)).collect_vec();
                    let call = Call {
                        function:    Box::new(Expression::BuiltinCallRef("mkSlice".to_string())),
                        params:      elems,
                        return_type: output_type.clone(),
                    };
                    Expression::Call(call)
                }
                HirArrayLiteral::Repeated {
                    repeated_element, ..
                } => {
                    let elem_expr = self.generate_expr(*repeated_element);
                    let call = Call {
                        function:    Box::new(Expression::BuiltinCallRef(
                            "mkRepeatedSlice".to_string(),
                        )),
                        params:      vec![elem_expr],
                        return_type: output_type.clone(),
                    };
                    Expression::Call(call)
                }
            },
            HirLiteral::Bool(bool) => Expression::Literal(Literal::Bool(*bool)),
            HirLiteral::Integer(signed_field) => {
                let value = format!(
                    "{}{}",
                    if signed_field.is_negative() { "-" } else { "" },
                    signed_field.absolute_value()
                );

                let literal = NumericLiteral {
                    value,
                    typ: output_type.clone(),
                };

                Expression::Literal(Literal::NumericLiteral(literal))
            }
            HirLiteral::Str(value) => Expression::Literal(Literal::String(value.clone())),
            HirLiteral::FmtStr(parts, vars, _) => {
                let template = Expression::Literal(Literal::String(
                    parts.iter().map(std::string::ToString::to_string).join("{}"),
                ));
                let vars = vars.iter().map(|e| self.generate_expr(*e));
                let all_vars = vec![template].into_iter().chain(vars).collect_vec();

                let call = Call {
                    function:    Box::new(Expression::BuiltinCallRef("mkFormatString".to_string())),
                    params:      all_vars,
                    return_type: output_type.clone(),
                };
                Expression::Call(call)
            }
            HirLiteral::Unit => Expression::Literal(Literal::Unit),
        }
    }

    /// Generates an expression corresponding to the provided `ident` in the
    /// context of `expr`.
    ///
    /// # Panics
    ///
    /// - A trait function is missing its self type.
    /// - A non-struct type is used as the receiver for a non-trait function.
    /// - A malformed global is encountered.
    /// - An associated constant is encountered, as it is currently unsupported.
    #[expect(clippy::too_many_lines)] // No reasonable way to split this up.
    pub fn generate_ident_expression(
        &self,
        expr: ExprId,
        ident: &HirIdent,
        output_type: &Type,
    ) -> Expression {
        let name =
            EmitContext::quote_name_if_needed(self.context.def_interner.definition_name(ident.id));
        let ident_def = self.context.def_interner.definition(ident.id);
        let default: TypeBindings = HashMap::default();
        let bindings = self
            .context
            .def_interner
            .try_get_instantiation_bindings(expr)
            .unwrap_or(&default);

        match &ident_def.kind {
            DefinitionKind::Function(id) => {
                let func_meta = self.context.def_interner.function_meta(id);
                let fun_generics = self.gather_function_generic_values(func_meta);

                if let Some(trait_impl_id) = func_meta.trait_impl {
                    let trait_impl =
                        self.context.def_interner.get_trait_implementation(trait_impl_id);
                    let trait_impl = trait_impl.borrow();
                    let self_type =
                        self.generate_lean_type_value(&func_meta.self_type.as_ref().map_or_else(
                            || panic!("Trait function {name} missing Self type"),
                            |t| self.substitute_bindings(t, bindings),
                        ));
                    let trait_name = EmitContext::quote_name_if_needed(
                        &self.resolve_fq_trait_name_from_crate_id(
                            trait_impl.crate_id,
                            trait_impl.trait_id,
                        ),
                    );
                    let trait_generics = trait_impl
                        .trait_generics
                        .iter()
                        .map(|t| self.substitute_bindings(t, bindings))
                        .map(|t| self.generate_lean_type_value(&t))
                        .collect_vec();
                    let param_types = self
                        .generate_function_parameters(func_meta)
                        .into_iter()
                        .map(|p| p.typ)
                        .collect_vec();
                    let return_type = self.generate_lean_type_value(&self.resolve_bound_type(expr));

                    let call_ref = TraitCallRef {
                        trait_name,
                        function_name: name,
                        self_type,
                        trait_generics,
                        fun_generics,
                        param_types,
                        return_type,
                    };
                    Expression::TraitCallRef(call_ref)
                } else if let Some(trait_id) = func_meta.trait_id {
                    let trait_data = self.context.def_interner.get_trait(trait_id);
                    let trait_name = EmitContext::quote_name_if_needed(
                        &self.resolve_fq_trait_name_from_crate_id(
                            trait_data.crate_id,
                            trait_data.id,
                        ),
                    );
                    let trait_generics = trait_data
                        .generics
                        .iter()
                        .map(|rg| NoirType::TypeVariable(rg.type_var.clone()))
                        .map(|g| self.substitute_bindings(&g, bindings))
                        .map(|t| self.generate_lean_type_value(&t))
                        .collect_vec();
                    let self_type = func_meta
                        .self_type
                        .as_ref()
                        .map(|t| self.substitute_bindings(t, bindings))
                        .map_or_else(
                            || panic!("Trait function {name} missing Self type"),
                            |t| self.generate_lean_type_value(&t),
                        );
                    let param_types = self
                        .generate_function_parameters(func_meta)
                        .into_iter()
                        .map(|p| p.typ)
                        .collect_vec();
                    let return_type = self.generate_lean_type_value(&self.resolve_bound_type(expr));

                    let call_ref = TraitCallRef {
                        trait_name,
                        function_name: name,
                        self_type,
                        trait_generics,
                        fun_generics,
                        param_types,
                        return_type,
                    };
                    Expression::TraitCallRef(call_ref)
                } else {
                    let func_name =
                        EmitContext::quote_name_if_needed(&match &func_meta.self_type {
                            Some(self_type) => {
                                let maybe_self_type = self.generate_lean_type_value(self_type);
                                if let TypeExpr::Struct(s) = maybe_self_type.expr {
                                    let struct_path = s.name;
                                    format!("{struct_path}::{name}")
                                } else {
                                    name
                                }
                            }
                            None => name,
                        });
                    let param_types = self
                        .generate_function_parameters(func_meta)
                        .into_iter()
                        .map(|p| p.typ)
                        .collect_vec();
                    let return_type = self.generate_lean_type_value(&self.resolve_bound_type(expr));

                    let call_ref = DeclCallRef {
                        function: func_name,
                        generics: fun_generics,
                        param_types,
                        return_type,
                    };

                    Expression::DeclCallRef(call_ref)
                }
            }
            DefinitionKind::Global(id) => {
                let global_info = self.context.def_interner.get_global(*id);
                let let_stmt = self.context.def_interner.statement(&global_info.let_statement);
                let (global_name, global_type) = match let_stmt {
                    HirStatement::Let(let_stmt) => {
                        let ident = match &let_stmt.pattern {
                            HirPattern::Identifier(hir_ident) => EmitContext::quote_name_if_needed(
                                self.context.def_interner.definition_name(hir_ident.id),
                            ),
                            _ => panic!("Encountered a malformed global"),
                        };
                        let typ = self.generate_lean_type_value(&let_stmt.r#type);
                        (ident, typ)
                    }
                    _ => panic!("Encountered a global that was not defined with a let binding"),
                };

                let ident = Identifier {
                    name: global_name,
                    typ:  global_type,
                };

                Expression::Ident(ident)
            }
            DefinitionKind::Local(_) => {
                let identifier = Identifier {
                    name,
                    typ: output_type.clone(),
                };

                Expression::Ident(identifier)
            }
            DefinitionKind::NumericGeneric(_, typ) => {
                let typ = self.generate_lean_type_value(typ);
                let literal = Literal::NumericLiteral(NumericLiteral { value: name, typ });

                Expression::Literal(literal)
            }
            DefinitionKind::AssociatedConstant(..) => {
                unimplemented!("Support for associated constants")
            }
        }
    }

    pub fn generate_block_expression(&self, block: &HirBlockExpression) -> Expression {
        let statements = block
            .statements
            .iter()
            .dropping_back(1)
            .map(|stmt| self.generate_statement(*stmt))
            .collect_vec();

        let return_expr = if let Some(stmt) = block.statements.last() {
            if let HirStatement::Expression(expr) = self.context.def_interner.statement(stmt) {
                Some(Box::new(self.generate_expr(expr)))
            } else {
                Some(Box::new(Expression::Skip))
            }
        } else {
            None
        };

        let block = Block {
            statements,
            expression: return_expr,
        };

        Expression::Block(block)
    }

    /// Generates an arbitrary statement in the AST from the Noir IR.
    ///
    /// # Panics
    ///
    /// - If passed a `loop` or `while` construct as these are unsupported.
    /// - If it encounters a compile-time evaluated statement which should have
    ///   been eliminated at this point.
    /// - If it encounters an error-marked statement.
    pub fn generate_statement(&self, stmt: StmtId) -> Statement {
        let statement_data = self.context.def_interner.statement(&stmt);
        match statement_data {
            HirStatement::Let(lets) => self.generate_let_statement(&lets),
            HirStatement::Assign(assign) => self.generate_assign_statement(&assign),
            HirStatement::For(fors) => self.generate_for(&fors),
            HirStatement::Break => panic!("Encountered break statement in constrained code"),
            HirStatement::Continue => panic!("Encountered continue statement in constrained code"),
            HirStatement::Expression(expr) | HirStatement::Semi(expr) => {
                Statement::Expression(self.generate_expr(expr))
            }
            HirStatement::Loop(_) => unimplemented!("Unbounded loops are not currently supported"),
            HirStatement::While(..) => unimplemented!("While loops are currently not supported"),
            HirStatement::Comptime(_) => {
                panic!("Encountered comptime statement during compilation when none should exist")
            }
            HirStatement::Error => panic!("Encountered error statement during compilation"),
        }
    }

    pub fn generate_for(&self, fors: &HirForStatement) -> Statement {
        let loop_variable = self
            .context
            .def_interner
            .definition_name(fors.identifier.id)
            .to_string();

        let start_range = Box::new(self.generate_expr(fors.start_range));
        let end_range = Box::new(self.generate_expr(fors.end_range));
        let body = Box::new(self.generate_expr(fors.block));

        let fors = ForStatement {
            loop_variable,
            start_range,
            end_range,
            body,
        };

        Statement::For(fors)
    }

    pub fn generate_assign_statement(&self, assign: &HirAssignStatement) -> Statement {
        let rhs_expr = self.generate_expr(assign.expression);
        let typ = self.generate_lean_type_value(&self.resolve_bound_type(assign.expression));
        let name = self.generate_lvalue(&assign.lvalue);

        let assign = AssignStatement {
            name,
            typ,
            expression: rhs_expr,
        };

        Statement::Assign(assign)
    }

    /// Generates an `LValue` from the corresponding Noir IR.
    ///
    /// # Panics
    ///
    /// - If it encounters by-name member access for a non-struct target value.
    /// - If no member with the provided name exists in the struct of the
    ///   provided type.
    pub fn generate_lvalue(&self, lvalue: &HirLValue) -> LValue {
        match lvalue {
            HirLValue::Ident(ident, typ) => LValue::Ident(Identifier {
                name: EmitContext::quote_name_if_needed(
                    self.context.def_interner.definition_name(ident.id),
                ),
                typ:  self.generate_lean_type_value(typ),
            }),
            HirLValue::MemberAccess {
                object,
                field_name,
                field_index,
                typ,
                ..
            } => {
                let object = Box::new(self.generate_lvalue(object.as_ref()));
                let index = field_index.unwrap_or_else(|| {
                    let field_indices = match typ {
                        NoirType::DataType(dt, _) => self.get_field_index_map(dt),
                        _ => panic!("Encountered by-name member access for non-struct target"),
                    };

                    field_indices.get(field_name).copied().unwrap_or_else(|| {
                        panic!("No index found for field with name {field_name}")
                    })
                });
                let typ = self.generate_lean_type_value(typ);

                LValue::MemberAccess { object, index, typ }
            }
            HirLValue::Index {
                array, index, typ, ..
            } => {
                let array = Box::new(self.generate_lvalue(array));
                let index = self.generate_expr(*index);
                let typ = self.generate_lean_type_value(typ);
                LValue::Index { array, index, typ }
            }
            HirLValue::Dereference {
                lvalue,
                element_type,
                ..
            } => {
                let object = Box::new(self.generate_lvalue(lvalue));
                let element_type = self.generate_lean_type_value(element_type);
                LValue::Dereference {
                    object,
                    element_type,
                }
            }
        }
    }

    pub fn get_field_index_map(&self, dt: &Shared<DataType>) -> HashMap<Ident, usize> {
        let struct_def = dt.borrow();
        let num_fields = struct_def
            .get_fields_as_written()
            .map(|f| f.len())
            .unwrap_or_default();
        (0..num_fields)
            .map(|i| {
                let StructField { name, .. } = struct_def.field_at(i);
                (name.clone(), i)
            })
            .collect::<HashMap<_, usize>>()
    }

    pub fn generate_let_statement(&self, lets: &HirLetStatement) -> Statement {
        let bound_expr = self.generate_expr(lets.expression);
        let pattern = self.generate_pattern(&lets.pattern);
        let typ = self.generate_lean_type_value(&lets.r#type);

        let stmt = LetStatement {
            pattern,
            typ,
            expression: Box::new(bound_expr),
        };

        Statement::Let(stmt)
    }
}

/// Functionality for basic resolution of names and other utility functions.
impl LeanGenerator<'_, '_> {
    /// Substitutes all bindings recursively in the provided `typ`.
    #[expect(clippy::only_used_in_recursion)] // The self parameter is for uniformity.
    pub fn substitute_bindings(&self, typ: &NoirType, bindings: &TypeBindings) -> NoirType {
        match typ {
            NoirType::TypeVariable(tv)
            | NoirType::NamedGeneric(NamedGeneric { type_var: tv, .. }) => bindings
                .get(&tv.id())
                .map(|(_, _, t)| t)
                .cloned()
                .unwrap_or(typ.clone()),
            NoirType::Array(n, e) => NoirType::Array(
                Box::new(self.substitute_bindings(n.as_ref(), bindings)),
                Box::new(self.substitute_bindings(e.as_ref(), bindings)),
            ),
            NoirType::Slice(e) => {
                NoirType::Slice(Box::new(self.substitute_bindings(e.as_ref(), bindings)))
            }
            NoirType::String(n) => {
                NoirType::String(Box::new(self.substitute_bindings(n, bindings)))
            }
            NoirType::FmtString(n, vec) => NoirType::FmtString(
                Box::new(self.substitute_bindings(n, bindings)),
                Box::new(self.substitute_bindings(vec, bindings)),
            ),
            NoirType::Tuple(vec) => {
                NoirType::Tuple(vec.iter().map(|t| self.substitute_bindings(t, bindings)).collect())
            }
            NoirType::DataType(definition, generics) => NoirType::DataType(
                definition.clone(),
                generics
                    .iter()
                    .map(|t| self.substitute_bindings(t, bindings))
                    .collect(),
            ),
            NoirType::Alias(def, generics) => NoirType::Alias(
                def.clone(),
                generics
                    .iter()
                    .map(|t| self.substitute_bindings(t, bindings))
                    .collect(),
            ),
            NoirType::Function(params, ret, env, unconstrained) => NoirType::Function(
                params.iter().map(|t| self.substitute_bindings(t, bindings)).collect(),
                Box::new(self.substitute_bindings(ret, bindings)),
                Box::new(self.substitute_bindings(env, bindings)),
                *unconstrained,
            ),
            NoirType::TraitAsType(id, name, generics) => NoirType::TraitAsType(
                *id,
                name.clone(),
                TraitGenerics {
                    ordered: generics
                        .ordered
                        .iter()
                        .map(|t| self.substitute_bindings(t, bindings))
                        .collect(),
                    named:   generics
                        .named
                        .iter()
                        .map(|t| NamedType {
                            name: t.name.clone(),
                            typ:  self.substitute_bindings(&t.typ, bindings),
                        })
                        .collect(),
                },
            ),
            NoirType::Reference(t, is_const) => {
                NoirType::Reference(Box::new(self.substitute_bindings(t, bindings)), *is_const)
            }
            NoirType::Forall(tvs, t) => {
                NoirType::Forall(tvs.clone(), Box::new(self.substitute_bindings(t, bindings)))
            }
            _ => typ.clone(),
        }
    }

    pub fn resolve_bound_type(&self, id: ExprId) -> NoirType {
        let identified_ty = self.context.def_interner.id_type(id);
        let expr_bindings = self.context.def_interner.try_get_instantiation_bindings(id);

        // Get the instantiated type of the expression.
        let expr_ty = match (identified_ty, expr_bindings) {
            (NoirType::TypeVariable(tv), Some(expr_bindings))
                if expr_bindings.contains_key(&tv.id()) =>
            {
                expr_bindings[&tv.id()].2.clone()
            }
            (ty, _) => ty,
        };

        match &expr_ty {
            NoirType::TypeVariable(tv) => {
                if let TypeBinding::Bound(bound_ty) = &*tv.borrow() {
                    bound_ty.clone()
                } else {
                    expr_ty.clone()
                }
            }
            _ => expr_ty,
        }
    }

    /// Resolves a fully-qualified trait name given the crate and trait.
    ///
    /// # Panics
    ///
    /// - If the provided module does not exist in the compilation context.
    pub fn resolve_fq_trait_name_from_crate_id(
        &self,
        crate_id: CrateId,
        trait_id: TraitId,
    ) -> String {
        let krate = self
            .context
            .def_map(&crate_id)
            .expect("Module should exist in context");
        let trait_def = self.context.def_interner.get_trait(trait_id);
        let name = trait_def.name.to_string();
        let path = if let Some((ix, data)) = krate.modules().iter().find(|(_, m)| {
            let mut type_defs = m.type_definitions();
            type_defs.any(|item| match item {
                ModuleDefId::TraitId(trait_id_inner) => trait_id == trait_id_inner,
                _ => false,
            })
        }) {
            let module_path =
                krate.get_module_path_with_separator(LocalModuleId::new(ix), data.parent, "::");

            if crate_id.is_stdlib() {
                format!("std::{module_path}")
            } else {
                module_path
            }
        } else {
            String::default()
        };

        if path.is_empty() {
            name
        } else {
            format!("{path}::{name}")
        }
    }

    #[must_use]
    #[expect(clippy::only_used_in_recursion)] // The self parameter is for uniformity
    pub fn is_function_unconstrained(&self, tp: &NoirType) -> bool {
        match tp {
            NoirType::Function(_, _, _, is_unconstrained) => *is_unconstrained,
            NoirType::Forall(_, tp) => self.is_function_unconstrained(tp),
            _ => false,
        }
    }

    #[must_use]
    #[expect(clippy::only_used_in_recursion)] // The self parameter is for uniformity
    pub fn unfold_alias(&self, typ: NoirType) -> NoirType {
        match typ {
            NoirType::Alias(alias, generics) => {
                let unfolded_typ = alias.borrow().get_type(&generics);
                self.unfold_alias(unfolded_typ)
            }
            typ => typ,
        }
    }
}

/// A container for top-level non-type definitions in a module.
pub struct ModuleDefs {
    /// All free function definitions in the module.
    pub func_defs: Vec<(Location, FunctionDefinition)>,

    /// All global definitions in the module.
    pub global_defs: Vec<(Location, GlobalDefinition)>,
}
