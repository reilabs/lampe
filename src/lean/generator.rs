//! This module contains the logic for analyzing the Noir source code and
//! generating the Lean AST from it.

use std::{cell::Ref, cmp::Ordering, collections::HashSet};

use fm::FileId;
use itertools::Itertools;
use noirc_errors::Location;
use noirc_frontend::{
    ast::FunctionKind,
    graph::CrateId,
    hir::{
        def_map::{LocalModuleId, ModuleData, ModuleDefId},
        Context,
    },
    hir_def::{
        function::{FuncMeta, Param},
        stmt::{HirPattern, HirStatement},
        traits::{TraitConstraint, TraitImpl},
    },
    node_interner::{DependencyId, ExprId, FuncId, GlobalId, TraitId, TypeAliasId, TypeId},
    shared::Signedness,
    token::FunctionAttributeKind,
    BinaryTypeOperator,
    Kind as NoirKind,
    ResolvedGeneric,
    Type as NoirType,
    TypeBinding,
    TypeVariable,
    TypeVariableId,
};
use petgraph::data::DataMap;

use crate::lean::ast::{
    Block,
    BuiltinTag,
    BuiltinTypeExpr,
    Call,
    Crate,
    Expression,
    FunctionDefinition,
    GlobalDefinition,
    Identifier,
    Kind,
    Module,
    ParamDef,
    StructDefinition,
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

impl<'file_manager, 'parsed_files> LeanGenerator<'file_manager, 'parsed_files> {
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
                        // TODO: [#112] Is this the right way to handle this?
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
            .map(|f| {
                let name = f.name.to_string();
                let typ = self.generate_lean_type_value(&f.typ);
                ParamDef {
                    name,
                    typ,
                    is_mut: false,
                }
            })
            .collect_vec();

        StructDefinition {
            name: qualified_path,
            generics,
            members,
        }
    }

    pub fn generate_lean_type_value(&self, typ: &NoirType) -> Type {
        match typ {
            NoirType::FieldElement => Type {
                expr: TypeExpr::builtin(BuiltinTag::Field, vec![]),
                kind: Kind::Type,
            },
            NoirType::Array(count, typ) => Type::array(
                self.generate_lean_type_value(typ).expr,
                self.generate_lean_type_value(count).expr,
            ),
            NoirType::Slice(typ) => Type::slice(self.generate_lean_type_value(typ).expr),
            NoirType::Integer(signedness, bit_size) => Type::integer(
                bit_size.bit_size() as u64,
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
                Type::tuple(elems)
            }
            NoirType::DataType(struct_type, generics) => {
                let type_def = struct_type.borrow();
                let module_id = type_def.id.module_id();
                let name = self
                    .context
                    .fully_qualified_struct_path(&module_id.krate, type_def.id);
                let generics = generics
                    .iter()
                    .map(|g| self.generate_lean_type_value(g).expr)
                    .collect_vec();
                Type::data_type(&name, generics)
            }
            NoirType::Alias(alias, generics) => {
                let alias = alias.borrow();
                let name = alias.name.to_string();
                let generics = generics
                    .iter()
                    .map(|g| self.generate_lean_type_value(g).expr)
                    .collect_vec();
                Type::alias(&name, generics)
            }
            NoirType::TypeVariable(tv) => self.generate_ty_var(tv, format!("TV_{tv:?}")),
            NoirType::NamedGeneric(ng) => self.generate_ty_var(&ng.type_var, ng.name.to_string()),
            NoirType::CheckedCast { to, .. } => Type::cast(self.generate_lean_type_value(to).expr),
            NoirType::Function(parameters, returns, captures, unconstrained) => {
                assert!(!unconstrained, "Unconstrained function type encountered");
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
            NoirType::Forall(..) => panic!("Encountered forall type"),
            NoirType::Quoted(_) => panic!("Encountered quoted type"),
            NoirType::TraitAsType(..) => {
                panic!("Encountered TraitAsType, but this should be resolved to a type variable")
            }
            NoirType::Error => panic!("Encountered error type"),
        }
    }

    pub fn generate_lean_type_pattern_from_resolved_generic(
        &self,
        rg: &ResolvedGeneric,
    ) -> TypePattern {
        self.generate_lean_type_pattern_from_tyvar(&rg.type_var, rg.name.to_string())
    }

    pub fn generate_lean_type_pattern_from_tyvar(
        &self,
        tv: &TypeVariable,
        name: String,
    ) -> TypePattern {
        let typ = self.generate_ty_var(&tv, name);
        let kind = typ.kind;
        let pattern = match typ.expr {
            TypeExpr::TypeVariable(n) => n,
            _ => panic!("Built type pattern from type variable without containing type variable"),
        };

        TypePattern { pattern, kind }
    }

    pub fn generate_lean_type_pattern_from_type(&self, typ: &NoirType) -> TypePattern {
        let (tv, name) = match typ {
            NoirType::TypeVariable(tv) => (tv, format!("TV_{tv:?}")),
            NoirType::NamedGeneric(ng) => (&ng.type_var, ng.name.to_string()),
            _ => panic!("Encountered illegal type {typ:?} to generate a pattern from"),
        };

        self.generate_lean_type_pattern_from_tyvar(tv, name)
    }

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
        let name = alias_data.name.to_string();
        let generics = alias_data
            .generics
            .iter()
            .map(|g| self.generate_lean_type_pattern_from_resolved_generic(g))
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
        let name = self.resolve_fq_trait_name_from_crate_id(trait_def.crate_id, id);
        let generics = trait_def
            .generics
            .iter()
            .map(|g| self.generate_lean_type_pattern_from_resolved_generic(g))
            .collect_vec();
        let associated_types = trait_def
            .associated_types
            .iter()
            .map(|t| self.generate_lean_type_pattern_from_resolved_generic(t))
            .collect_vec();

        let methods = trait_def
            .methods
            .iter()
            .map(|method| {
                let method_name = method.name.to_string();
                let generics = method
                    .direct_generics
                    .iter()
                    .map(|g| self.generate_lean_type_pattern_from_resolved_generic(g))
                    .collect_vec();
                let parameters = method
                    .arguments()
                    .iter()
                    .map(|t| self.generate_lean_type_value(t))
                    .collect_vec();
                let out_type = self.generate_lean_type_value(method.return_type());

                TraitMethodDeclaration {
                    name: method_name,
                    generics,
                    parameters,
                    return_type: Box::new(out_type),
                }
            })
            .collect_vec();

        TraitDefinition {
            name,
            generics,
            associated_types,
            methods,
        }
    }

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
        let (functions, globals) = self.generate_module_definitions(&module_data);

        let trait_impls = trait_impls
            .into_iter()
            .sorted_by(|(loc_l, imp_l), (loc_r, imp_r)| {
                loc_l.cmp(&loc_r).then_with(|| imp_l.cmp(&imp_r))
            })
            .map(|(_, a)| a)
            .collect_vec();
        let functions = functions
            .into_iter()
            .sorted_by(|(loc_l, imp_l), (loc_r, imp_r)| {
                loc_l.cmp(&loc_r).then_with(|| imp_l.cmp(&imp_r))
            })
            .map(|(_, a)| a)
            .collect_vec();
        let globals = globals
            .into_iter()
            .sorted_by(|(loc_l, glob_l), (loc_r, glob_r)| {
                loc_l.cmp(&loc_r).then_with(|| glob_l.cmp(&glob_r))
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

    pub fn generate_module_definitions(
        &self,
        module: &ModuleData,
    ) -> (
        Vec<(Location, FunctionDefinition)>,
        Vec<(Location, GlobalDefinition)>,
    ) {
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

        (functions, globals)
    }

    pub fn generate_free_function_def(&self, id: &FuncId) -> FunctionDefinition {
        let function_meta = self.context.function_meta(id);
        let generics = self.gather_function_generics(&function_meta);
        let parameters = self.generate_function_parameters(&function_meta);
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
            self.generate_expr(self.context.def_interner.function(&id).as_expr())
        };

        let name = self
            .context
            .fully_qualified_function_name(&function_meta.source_crate, id);

        FunctionDefinition {
            name,
            generics,
            parameters,
            return_type,
            body,
        }
    }

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
                    let name = self.context.def_interner.definition_name(ident.id).to_string();
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

    pub fn gather_function_generics(&self, data: &FuncMeta) -> Vec<TypePattern> {
        let all_generics_on_func = data
            .all_generics
            .iter()
            .map(|g| self.generate_lean_type_pattern_from_resolved_generic(g));

        let trait_gens = self.gather_trait_constraint_generics(data.trait_constraints.as_slice());

        all_generics_on_func
            .chain(trait_gens)
            .collect::<HashSet<_>>()
            .into_iter()
            .collect_vec()
    }

    pub fn gather_trait_constraint_generics(
        &self,
        constraints: &[TraitConstraint],
    ) -> Vec<TypePattern> {
        let mut generics = Vec::new();
        let mut seen = HashSet::<TypeVariableId>::new();
        for constraint in constraints {
            generics.extend(self.gather_unbound_vars(&constraint.typ, &mut seen));

            for gen in &constraint.trait_bound.trait_generics.ordered {
                generics.extend(self.gather_unbound_vars(gen, &mut seen));
            }

            for gen in &constraint.trait_bound.trait_generics.named {
                generics.extend(self.gather_unbound_vars(&gen.typ, &mut seen))
            }
        }

        generics
    }

    pub fn gather_unbound_vars(
        &self,
        typ: &NoirType,
        seen: &mut HashSet<TypeVariableId>,
    ) -> Vec<TypePattern> {
        match typ {
            NoirType::String(a) | NoirType::Slice(a) | NoirType::Reference(a, _) => {
                self.gather_unbound_vars(a, seen)
            }
            NoirType::Array(a, b) | NoirType::FmtString(a, b) => self
                .gather_unbound_vars(a, seen)
                .into_iter()
                .chain(self.gather_unbound_vars(b, seen))
                .collect_vec(),
            NoirType::DataType(_, generics) => generics
                .iter()
                .flat_map(|g| self.gather_unbound_vars(g, seen))
                .collect_vec(),
            NoirType::TypeVariable(tv) => match &*tv.borrow() {
                TypeBinding::Bound(tp) => self.gather_unbound_vars(tp, seen),
                TypeBinding::Unbound(id, _) => {
                    if seen.contains(&id) {
                        Vec::default()
                    } else {
                        seen.insert(id.clone());
                        vec![self.generate_lean_type_pattern_from_tyvar(tv, format!("V_{id}"))]
                    }
                }
            },
            NoirType::NamedGeneric(ng) => match &*ng.type_var.borrow() {
                TypeBinding::Bound(tp) => self.gather_unbound_vars(tp, seen),
                TypeBinding::Unbound(id, _) => {
                    if seen.contains(&id) {
                        Vec::default()
                    } else {
                        seen.insert(id.clone());
                        vec![self.generate_lean_type_pattern_from_tyvar(
                            &ng.type_var,
                            ng.name.to_string(),
                        )]
                    }
                }
            },
            _ => Vec::default(),
        }
    }

    pub fn generate_function_parameters(&self, data: &FuncMeta) -> Vec<ParamDef> {
        data.parameters
            .iter()
            .map(|(pattern, typ, ..)| {
                let typ = self.generate_lean_type_value(typ);
                match pattern {
                    HirPattern::Identifier(ident) => ParamDef {
                        name: self.context.def_interner.definition_name(ident.id).to_string(),
                        typ,
                        is_mut: false,
                    },
                    HirPattern::Mutable(ident, _) => match ident.as_ref() {
                        HirPattern::Identifier(ident) => ParamDef {
                            name: self.context.def_interner.definition_name(ident.id).to_string(),
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
                    HirPattern::Identifier(hir_ident) => {
                        self.context.def_interner.definition_name(hir_ident.id).to_string()
                    }
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
            .filter(|(_, t)| t.borrow().file == file)
            .flat_map(|(id, trait_impl)| {
                if matches!(trait_impl.borrow().typ, NoirType::Quoted(_)) {
                    return None;
                }

                let name = format!("impl_{id:?}");
                let location = trait_impl.borrow().location.clone();
                Some((
                    location,
                    self.generate_trait_impl(name, trait_impl.borrow()),
                ))
            })
            .collect_vec()
    }

    pub fn generate_trait_impl(
        &self,
        name: String,
        trait_impl: Ref<TraitImpl>,
    ) -> TraitImplementation {
        let trait_def_id = trait_impl.trait_id;
        let trait_def_data = self.context.def_interner.get_trait(trait_def_id);
        let trait_name =
            self.resolve_fq_trait_name_from_crate_id(trait_def_data.crate_id, trait_def_id);
        let self_type = self.generate_lean_type_value(&trait_impl.typ);

        let where_clauses = trait_impl
            .where_clause
            .iter()
            .map(|cons| {
                let var = self.generate_lean_type_value(&cons.typ);
                let trait_name = self
                    .context
                    .def_interner
                    .get_trait(cons.trait_bound.trait_id)
                    .name
                    .to_string();
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

        let generic_vars = self.gather_trait_impl_generics(&trait_impl);

        let methods = trait_impl
            .methods
            .iter()
            .map(|m| self.generate_trait_function_def(*m))
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
            patterns.extend(self.gather_unbound_vars(typ, &mut seen));
        }

        patterns.extend(self.gather_unbound_vars(&trait_impl.typ, &mut seen));
        patterns.extend(self.gather_trait_constraint_generics(trait_impl.where_clause.as_slice()));

        patterns
    }

    pub fn generate_trait_function_def(&self, id: FuncId) -> FunctionDefinition {
        // Note that we NEVER want to qualify the name of the trait function.
        let function_meta = self.context.function_meta(&id);
        let name = self.context.function_name(&id).to_string();

        let parameters = self.generate_function_parameters(&function_meta);
        let return_type = self.generate_lean_type_value(function_meta.return_type());
        let generics = self.gather_function_generics(&function_meta);
        let body = self.generate_expr(self.context.def_interner.function(&id).as_expr());

        FunctionDefinition {
            name,
            generics,
            parameters,
            return_type,
            body,
        }
    }

    pub fn generate_expr(&self, _id: ExprId) -> Expression {
        unimplemented!()
    }
}

/// Functionality for basic resolution of names and other utility functions.
impl<'file_manager, 'parsed_files> LeanGenerator<'file_manager, 'parsed_files> {
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

    pub fn is_function_unconstrained(&self, tp: &NoirType) -> bool {
        match tp {
            NoirType::Function(_, _, _, is_unconstrained) => *is_unconstrained,
            NoirType::Forall(_, tp) => self.is_function_unconstrained(tp),
            _ => false,
        }
    }
}
