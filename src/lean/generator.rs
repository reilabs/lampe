//! This module contains the logic for analyzing the Noir source code and
//! generating the Lean AST from it.

use std::{
    cell::Ref,
    cmp::Ordering,
    collections::{HashMap, HashSet},
    rc::Rc,
    str::FromStr,
};

use fm::FileId;
use itertools::Itertools;
use noirc_errors::Location;
use noirc_frontend::{
    ast::{FunctionKind, Ident, IntegerBitSize},
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

use crate::{
    file_generator::to_import_from_noir_path,
    lean::{
        ast::{
            AssignStatement,
            Block,
            BuiltinCallRef,
            BuiltinTag,
            BuiltinTypeExpr,
            Call,
            Cast,
            ConstGenericLiteral,
            Crate,
            DeclCallRef,
            Expression,
            ForStatement,
            FunctionDefinition,
            GlobalCallRef,
            GlobalDefinition,
            IdentCallRef,
            Identifier,
            IfThenElse,
            Kind,
            LValue,
            Lambda,
            LetStatement,
            Literal,
            MemberAccess,
            Module,
            ModuleDefinition,
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
        builtin::{
            BuiltinType,
            ASSERT_BUILTIN_NAME,
            MAKE_ARRAY_BUILTIN_NAME,
            MAKE_REPEATED_ARRAY_BUILTIN_NAME,
            MAKE_REPEATED_SLICE_BUILTIN_NAME,
            MAKE_SLICE_BUILTIN_NAME,
            MAKE_STRUCT_BUILTIN_NAME,
            UNIT_TYPE_NAME,
        },
        conflicts_with_lean_keyword,
        LEAN_QUOTE_END,
        LEAN_QUOTE_START,
    },
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

    /// Returns `true` if the root crate in the standard library.
    pub fn root_crate_is_stdlib(&self) -> bool {
        &self.root_crate == self.context.stdlib_crate_id()
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
                    *dep_id,
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
                        let struct_def = self.generate_struct_def(id);
                        let name = quote_lean_keywords(&struct_def.name);
                        let def = TypeDefinition::Struct(struct_def);

                        vec![(def_order, name, def)]
                    }
                    ModuleDefId::TypeAliasId(id) => {
                        if id.0 == usize::MAX {
                            return vec![];
                        }

                        let def_order = dep_weights
                            .clone()
                            .into_iter()
                            .position(|item| *item == DependencyId::Alias(id));
                        let alias_def = self.generate_alias(id);
                        let name = quote_lean_keywords(&alias_def.name);
                        let def = TypeDefinition::Alias(alias_def);

                        vec![(def_order, name, def)]
                    }
                    ModuleDefId::TraitId(id) => {
                        let def_order = dep_weights
                            .clone()
                            .into_iter()
                            .position(|item| *item == DependencyId::Trait(id));
                        let trait_def = self.generate_trait_definition(id);
                        let name = quote_lean_keywords(&trait_def.name);
                        let def = TypeDefinition::Trait(trait_def);

                        vec![(def_order, name, def)]
                    }
                    _ => vec![],
                })
                .collect::<HashSet<_>>();

            all_defs.extend(module_definitions.into_iter());
        }

        all_defs
            .into_iter()
            .sorted_by(|(l_ord, l_name, l_def), (r_ord, r_name, r_def)| {
                #[allow(clippy::enum_glob_use)]
                use TypeDefinition::*;
                match (l_def, r_def) {
                    // We push traits towards the end of the file by force, because they are not
                    // correctly tracked in the dependency graph, and we know there are no
                    // structs and aliases depending on traits.
                    (Alias(_) | Struct(_), Trait(_)) => Ordering::Greater,
                    (Trait(_), Struct(_) | Alias(_)) => Ordering::Less,
                    _ => match (l_ord, r_ord) {
                        (Some(ord1), Some(ord2)) => ord1.cmp(ord2),
                        // If one of the definitions is not ordered, we push it towards the end,
                        // to increase the probability of it working in the absence of
                        // dependency info.
                        (None, Some(_)) => Ordering::Less,
                        (Some(_), None) => Ordering::Greater,
                        (None, None) => r_name.cmp(l_name),
                    },
                }
            })
            .rev()
            .map(|(_, _, def)| def)
            .collect_vec()
    }

    /// Generates the definition of a `struct` that is describeed by the
    /// provided `id`.
    pub fn generate_struct_def(&self, id: TypeId) -> StructDefinition {
        let struct_data = self.context.def_interner.get_type(id);
        let struct_data = struct_data.borrow();
        let qualified_path =
            self.fully_qualified_struct_path(&struct_data.id.module_id().krate, &id);

        let name = quote_lean_keywords(&qualified_path);

        // We always need the generics to be in a consistent order, otherwise we would
        // potentially break user code. Unfortunately, they do not _come_ in a
        // consistent order as iteration order seems to be determined by id.
        let generics = struct_data
            .generics
            .iter()
            .map(|g| self.generate_lean_type_pattern_from_resolved_generic(g))
            .collect_vec();

        let fields = struct_data.get_fields_as_written().unwrap_or_default();
        let members = fields
            .into_iter()
            .map(|f| self.generate_lean_type_value(&f.typ, None))
            .collect_vec();

        StructDefinition {
            name,
            generics,
            members,
        }
    }

    /// Generates a type _value_ from the provided `typ`.
    ///
    /// If `bindings` are provided, it will then perform binding substitution
    /// during the generation process.
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
    #[expect(clippy::too_many_lines)] // It does not make sense to split it up.
    pub fn generate_lean_type_value(
        &self,
        typ: &NoirType,
        bindings: Option<&TypeBindings>,
    ) -> Type {
        #[allow(clippy::match_same_arms)] // The similarity is incidental
        match typ {
            NoirType::FieldElement => Type {
                expr: TypeExpr::builtin(BuiltinTag::Field, &[]),
                kind: Kind::Type,
            },
            NoirType::Array(count, typ) => Type::array(
                self.generate_lean_type_value(typ, bindings),
                self.generate_lean_type_value(count, bindings),
            ),
            NoirType::Slice(typ) => Type::slice(self.generate_lean_type_value(typ, bindings)),
            NoirType::Integer(signedness, bit_size) => Type::integer(
                u64::from(bit_size.bit_size()),
                *signedness == Signedness::Signed,
            ),
            NoirType::Bool => Type::bool(),
            NoirType::String(count) => Type::string(self.generate_lean_type_value(count, bindings)),
            NoirType::FmtString(len, args) => Type::fmt_string(
                self.generate_lean_type_value(len, bindings),
                self.generate_lean_type_value(args, bindings),
            ),
            NoirType::Unit => Type::unit(),
            NoirType::Tuple(elems) => {
                let elems = elems
                    .iter()
                    .map(|e| self.generate_lean_type_value(e, bindings))
                    .collect_vec();
                Type::tuple(elems.as_slice())
            }
            NoirType::DataType(struct_type, generics) => {
                let type_def = struct_type.borrow();
                let module_id = type_def.id.module_id();
                let name = &self.fully_qualified_struct_path(&module_id.krate, &type_def.id);
                let name = &quote_lean_keywords(name);
                let generics = generics
                    .iter()
                    .map(|g| self.generate_lean_type_value(g, bindings))
                    .collect_vec();
                Type::data_type(name, generics)
            }
            NoirType::Alias(alias, generics) => {
                let alias = alias.borrow();
                let name = alias.name.as_str();
                let name = &quote_lean_keywords(name);
                let generics = generics
                    .iter()
                    .map(|g| self.generate_lean_type_value(g, bindings))
                    .collect_vec();
                Type::alias(name, generics)
            }
            NoirType::TypeVariable(tv) => {
                if let Some(bindings) = bindings {
                    bindings.get(&tv.id()).map_or_else(
                        || self.generate_ty_var(tv, None),
                        |(_, kind, typ)| match kind {
                            NoirKind::Numeric(n) => match n.as_ref() {
                                NoirType::Constant(..) => {
                                    self.generate_lean_type_value(n.as_ref(), Some(bindings))
                                }
                                _ => self.generate_lean_type_value(typ, Some(bindings)),
                            },
                            _ => self.generate_lean_type_value(typ, Some(bindings)),
                        },
                    )
                } else {
                    self.generate_ty_var(tv, None)
                }
            }
            NoirType::NamedGeneric(ng) => {
                if let Some(bindings) = bindings {
                    bindings.get(&ng.type_var.id()).map_or_else(
                        || {
                            self.generate_ty_var(
                                &ng.type_var,
                                Some(sanitize_generic_name(&ng.name)),
                            )
                        },
                        |(_, kind, typ)| match kind {
                            NoirKind::Numeric(n) => match n.as_ref() {
                                NoirType::Constant(..) => {
                                    self.generate_lean_type_value(n.as_ref(), Some(bindings))
                                }
                                _ => self.generate_lean_type_value(typ, Some(bindings)),
                            },
                            _ => self.generate_lean_type_value(typ, Some(bindings)),
                        },
                    )
                } else {
                    self.generate_ty_var(&ng.type_var, Some(sanitize_generic_name(&ng.name)))
                }
            }
            NoirType::CheckedCast { to, .. } => {
                Type::cast(self.generate_lean_type_value(to, bindings))
            }
            NoirType::Function(parameters, returns, captures, _) => {
                let parameters = parameters
                    .iter()
                    .map(|p| self.generate_lean_type_value(p, bindings))
                    .collect_vec();
                let returns = self.generate_lean_type_value(returns, bindings);
                let captures = self.generate_lean_type_value(captures, bindings);
                Type::function(parameters, returns, captures)
            }
            NoirType::Reference(typ, mutable) => {
                let typ = self.generate_lean_type_value(typ, bindings);
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
                let left = self.generate_lean_type_value(left, bindings);
                let right = self.generate_lean_type_value(right, bindings);

                assert_eq!(
                    left.kind, right.kind,
                    "Type-level infix expression had operands with differing kinds"
                );

                let kind = left.kind;

                let op = match op {
                    BinaryTypeOperator::Addition => TypeArithOp::Add,
                    BinaryTypeOperator::Subtraction => TypeArithOp::Sub,
                    BinaryTypeOperator::Multiplication => TypeArithOp::Mul,
                    BinaryTypeOperator::Division => TypeArithOp::Div,
                    BinaryTypeOperator::Modulo => TypeArithOp::Mod,
                };
                Type::infix(left.expr, op, right.expr, kind)
            }
            NoirType::Quoted(quoted) => self.generate_quoted_type_value(quoted),
            NoirType::Forall(..) => panic!("Encountered forall type"),
            NoirType::TraitAsType(..) => {
                panic!("Encountered TraitAsType, but this should be resolved to a type variable")
            }
            // FIXME We should probably extract an "Error" type and then blackhole it.
            NoirType::Error => Type::unit(),
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
        self.generate_lean_type_pattern_from_tyvar(&rg.type_var, Some(rg.name.to_string()))
    }

    /// Generates a lean type pattern from the provided type variable `tv`.
    ///
    /// # Panics
    ///
    /// - If the provided `tv` does not contain a real type variable.
    pub fn generate_lean_type_pattern_from_tyvar(
        &self,
        tv: &TypeVariable,
        name: Option<String>,
    ) -> TypePattern {
        let typ = self.generate_ty_var(tv, name.map(|s| sanitize_generic_name(&s)));
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
        match typ {
            NoirType::NamedGeneric(ng) => {
                self.generate_lean_type_pattern_from_tyvar(&ng.type_var, Some(ng.name.to_string()))
            }
            _ => panic!("Encountered illegal type {typ:?} to generate a pattern from"),
        }
    }

    /// Expects that the provided `kind` is a known numeric kind.
    ///
    /// # Panics
    ///
    /// - If a non-concrete numeric kind is encountered.
    pub fn expect_constant_numeric_kind(&self, kind: &NoirKind) -> Kind {
        match kind {
            NoirKind::Numeric(kind) => match self.generate_lean_type_value(kind, None).expr {
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
    pub fn generate_ty_var(&self, tv: &TypeVariable, name: Option<String>) -> Type {
        match &*tv.borrow() {
            TypeBinding::Bound(b) => {
                let b = b.follow_bindings();
                self.generate_lean_type_value(&b, None)
            }
            TypeBinding::Unbound(id, kind) => {
                let kind = match kind {
                    NoirKind::Any | NoirKind::Normal => Kind::Type,
                    NoirKind::IntegerOrField | NoirKind::Integer => {
                        panic!("Kinds should be concrete at this stage")
                    }
                    NoirKind::Numeric(_) => self.expect_constant_numeric_kind(kind),
                };
                let name = name.unwrap_or_else(|| {
                    panic!("Type variable {id:?} had no name but is required to")
                });
                Type::variable(name, kind)
            }
        }
    }

    pub fn generate_alias(&self, id: TypeAliasId) -> TypeAlias {
        let alias_data = self.context.def_interner.get_type_alias(id);
        let alias_data = alias_data.borrow();
        let name = &alias_data.to_string();
        let name = quote_lean_keywords(name);
        let generics = self.gather_lean_type_patterns_from_resolved_generics(&alias_data.generics);
        let aliased_type = self.generate_lean_type_value(&alias_data.typ, None);
        TypeAlias {
            name,
            typ: aliased_type,
            generics,
        }
    }

    pub fn generate_trait_definition(&self, id: TraitId) -> TraitDefinition {
        let trait_def = self.context.def_interner.get_trait(id);
        let name = self.resolve_fq_trait_name_from_crate_id(trait_def.crate_id, id);
        let name = quote_lean_keywords(&name);
        let trait_generics =
            self.gather_lean_type_patterns_from_resolved_generics(&trait_def.generics);
        let associated_types =
            self.gather_lean_type_patterns_from_resolved_generics(&trait_def.associated_types);

        let methods = trait_def
            .methods
            .iter()
            .map(|method| {
                let method_name = method.name.to_string();
                let method_name = quote_lean_keywords(&method_name);
                let method_generics = self
                    .gather_lean_type_patterns_from_resolved_generics(&method.direct_generics)
                    .into_iter()
                    .filter(|g| !trait_generics.contains(g))
                    .collect_vec();
                let parameters = method
                    .arguments()
                    .iter()
                    .map(|t| self.generate_lean_type_value(t, None))
                    .collect_vec();
                let out_type = self.generate_lean_type_value(method.return_type(), None);

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
        // We gather all modules that are defined in the file, but skip any that are
        // acting as impl blocks as we handle methods on types elsewhere.
        let modules_data = self
            .context
            .def_map(&self.root_crate)
            .expect("Root crate was missing in compilation context")
            .modules()
            .iter()
            .filter(|(_, mod_data)| mod_data.location.file == id && !mod_data.is_type);

        let mut definitions = self
            .generate_module_trait_impls(id)
            .into_iter()
            .map(|(l, i)| (l, ModuleDefinition::TraitImpl(i)))
            .collect_vec();

        for (_, module_data) in modules_data {
            let ModuleDefs {
                func_defs: functions,
                global_defs: globals,
            } = self.generate_module_definitions(module_data);

            definitions = definitions
                .into_iter()
                .chain(functions.into_iter().map(|(l, f)| (l, ModuleDefinition::Function(f))))
                .collect_vec();

            definitions = definitions
                .into_iter()
                .chain(globals.into_iter().map(|(l, g)| (l, ModuleDefinition::Global(g))))
                .collect_vec();
        }

        // We sort them based on locations to retain the same definition order.
        let all_definitions = definitions
            .into_iter()
            .sorted_by(|(l_loc, _), (r_loc, _)| l_loc.span.cmp(&r_loc.span))
            .map(|(_, def)| def)
            .unique()
            .collect_vec();

        // FIXME: unwrap here is a bit scary, but all the files we're extracting should
        // have a path?
        let name = to_import_from_noir_path(self.context.file_manager.path(id).unwrap());

        Module {
            name,
            id,
            entries: all_definitions,
        }
    }

    /// Looks up methods defined on builtin types in the current module, and
    /// returns their definition identifiers.
    pub fn lookup_builtin_methods_in_module(&self, module: &ModuleData) -> Vec<ModuleDefId> {
        if !self.root_crate_is_stdlib() {
            return vec![];
        }

        // This is a dummy generic that we can use for querying builtin types that have
        // generics.
        let dummy_tv = TypeVariable::unbound(
            self.context.def_interner.next_type_variable_id(),
            NoirKind::Any,
        );
        let dummy_generic = NoirType::NamedGeneric(NamedGeneric {
            type_var: dummy_tv.clone(),
            name:     Rc::new("LOOKUP_DUMMY".to_string()),
            implicit: false,
        });

        // We then create the "method keys" for the builtin types; these are NoirType
        // values that are passed to the method discovery logic.
        let method_keys = vec![
            NoirType::Array(
                Box::new(dummy_generic.clone()),
                Box::new(dummy_generic.clone()),
            ),
            NoirType::Bool,
            NoirType::FieldElement,
            NoirType::FmtString(
                Box::new(dummy_generic.clone()),
                Box::new(dummy_generic.clone()),
            ),
            NoirType::Function(
                vec![],
                Box::new(NoirType::Unit),
                Box::new(NoirType::Unit),
                false,
            ),
            NoirType::Integer(Signedness::Unsigned, IntegerBitSize::One),
            NoirType::Slice(Box::new(dummy_generic.clone())),
            NoirType::String(Box::new(dummy_generic.clone())),
            NoirType::Tuple(vec![dummy_generic; 0]),
            NoirType::Unit,
        ];

        let mut extra_defs = Vec::default();

        // We then query the direct methods of each builtin type, and add them to the
        // output ONLY if they were defined in the same file as the module in question.
        // This way we ensure they are output in the right place.
        for key in method_keys {
            let all_methods = self.context.def_interner.get_type_methods(&key);

            if let Some(all_methods) = all_methods {
                let direct_methods = all_methods.values().flat_map(|m| {
                    m.direct.iter().filter_map(|m| {
                        let func_data = self.context.def_interner.function_meta(&m.method);
                        if func_data.location.file == module.location.file {
                            Some(ModuleDefId::FunctionId(m.method))
                        } else {
                            None
                        }
                    })
                });

                extra_defs.extend(direct_methods);
            }
        }

        extra_defs
    }

    pub fn generate_module_definitions(&self, module: &ModuleData) -> ModuleDefs {
        let mut globals = HashSet::new();
        let mut functions = HashSet::new();

        // We start by grabbing the definitions in the module, doing a lookup for
        // methods defined on types in this module.
        let module_defs = module
            .definitions()
            .definitions()
            .into_iter()
            .flat_map(|def| match def {
                ModuleDefId::TypeId(id) => {
                    let type_data_ref = self.context.def_interner.get_type(id);
                    let struct_data = type_data_ref.borrow();
                    let generics = struct_data
                        .generics
                        .iter()
                        .map(|g| {
                            NoirType::NamedGeneric(NamedGeneric {
                                type_var: g.type_var.clone(),
                                name:     g.name.clone(),
                                implicit: false,
                            })
                        })
                        .collect_vec();

                    let data_type = NoirType::DataType(type_data_ref.clone(), generics);

                    if let Some(meths) = self.context.def_interner.get_type_methods(&data_type) {
                        meths
                            .values()
                            .flat_map(|methods| {
                                methods.direct.iter().filter_map(|m| {
                                    let func_data =
                                        self.context.def_interner.function_meta(&m.method);
                                    if func_data.location.file == module.location.file {
                                        Some(ModuleDefId::FunctionId(m.method))
                                    } else {
                                        None
                                    }
                                })
                            })
                            .collect_vec()
                    } else {
                        vec![]
                    }
                }
                _ => vec![def],
            })
            .collect_vec();

        // We then handle the special cases of methods defined on builtin types in this
        // module and add them.
        let module_defs = module_defs
            .into_iter()
            .chain(self.lookup_builtin_methods_in_module(module))
            .collect_vec();

        for def in module_defs {
            match def {
                ModuleDefId::FunctionId(id) => {
                    let function_meta = self.context.function_meta(&id);

                    // Skip trait functions in the module scope that do not have bodies.
                    if function_meta.kind == FunctionKind::TraitFunctionWithoutBody {
                        continue;
                    }

                    // Skip trait method default implementations as well, as they are handled when
                    // generating the trait impl in question.
                    if function_meta.trait_id.is_some() {
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
                    if let Some(function) = self.generate_free_function_def(&id) {
                        functions.insert((location, function));
                    }
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

    /// Generates the free function definition for the function given by `id`,
    /// or returns [`None`] if a function should not be generated.
    ///
    /// # Panics
    ///
    /// - If an unsupported function kind is found for a builtin function.
    pub fn generate_free_function_def(&self, id: &FuncId) -> Option<FunctionDefinition> {
        let function_meta = self.context.function_meta(id);

        let name = if let Some(ty) = &function_meta.self_type {
            let func_name_bare = self.context.function_name(id);

            // Safe to pull the expr as we know the kind here must always be "Type"
            let ty = self.generate_lean_type_value(ty, None).expr;
            let self_ty_name = match ty {
                TypeExpr::Struct(s) => s.name,
                TypeExpr::Builtin(e) => match e.tag {
                    BuiltinTag::Array => "std::array".to_string(),
                    BuiltinTag::Bool => "std::bool".to_string(),
                    BuiltinTag::Field => "std::field".to_string(),
                    BuiltinTag::FmtString => "std::fmt_string".to_string(),
                    BuiltinTag::I(w) => format!("i{w}"),
                    BuiltinTag::Slice => "std::slice".to_string(),
                    BuiltinTag::String => "std::string".to_string(),
                    BuiltinTag::Tuple => "std::tuple".to_string(),
                    BuiltinTag::U(w) => format!("u{w}").to_string(),
                    BuiltinTag::Unit => UNIT_TYPE_NAME.to_string(),
                    _ => panic!(
                        "Invalid builtin {:?} used as `Self` type in function",
                        e.tag
                    ),
                },
                _ => panic!("Invalid `Self` type {ty:?} for function"),
            };

            format!("{self_ty_name}::{func_name_bare}")
        } else {
            self.fully_qualified_function_name(&function_meta.source_crate, id)
        };
        let name = quote_lean_keywords(&name);

        let generics = self.gather_function_generic_patterns(function_meta);
        let parameters = self.generate_function_parameters(function_meta);
        let return_type = self.generate_lean_type_value(function_meta.return_type(), None);
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
            return None;
        } else if function_meta.is_stub() {
            Expression::Block(Block {
                statements: Vec::default(),
                expression: None,
            })
        } else {
            self.generate_expr(self.context.def_interner.function(id).as_expr())
        };

        Some(FunctionDefinition {
            name,
            generics,
            parameters,
            return_type,
            body,
        })
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
        let call_identifier = Expression::BuiltinCallRef(BuiltinCallRef {
            name:        name.to_string(),
            return_type: return_type.clone(),
        });
        let params = params
            .into_iter()
            .map(|p| match &p.0 {
                HirPattern::Identifier(ident) => {
                    let name = self.context.def_interner.definition_name(ident.id).to_string();
                    let typ = self.generate_lean_type_value(
                        &self.context.def_interner.definition_type(ident.id),
                        None,
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

    /// Gathers the generic _values_ that are being passed at the call site.
    ///
    /// These must be fully instantiated at this point, even if that
    /// instantiation is with another type variable.
    pub fn gather_function_call_site_generic_values(
        &self,
        func_expr: ExprId,
        data: &FuncMeta,
    ) -> Vec<Type> {
        let default: TypeBindings = HashMap::default();

        let bindings = self
            .context
            .def_interner
            .try_get_instantiation_bindings(func_expr)
            .unwrap_or(&default);

        // If it is a trait function we only want to gather direct generics, but if it
        // is a free function def we need to gather the generics from the impl scope as
        // well.
        if data.trait_impl.is_some() || data.trait_id.is_some() {
            &data.direct_generics
        } else {
            &data.all_generics
        }
        .iter()
        .map(|rg| {
            self.generate_lean_type_value(
                &NoirType::TypeVariable(rg.type_var.clone()),
                Some(bindings),
            )
        })
        .unique()
        .collect()
    }

    pub fn gather_lean_type_patterns_from_resolved_generics(
        &self,
        data: &[ResolvedGeneric],
    ) -> Vec<TypePattern> {
        // If type patterns have the same name and kind, they are the same variable at
        // the definition site, so we can correctly unique them.
        data.iter()
            .map(|g| self.generate_lean_type_pattern_from_resolved_generic(g))
            .unique()
            .collect_vec()
    }

    pub fn gather_function_generic_patterns(&self, data: &FuncMeta) -> Vec<TypePattern> {
        let all_generics_on_func =
            self.gather_lean_type_patterns_from_resolved_generics(&data.all_generics);

        let trait_constraints_generics =
            self.gather_trait_constraint_generics_patterns(&data.trait_constraints);

        all_generics_on_func
            .into_iter()
            .chain(trait_constraints_generics)
            .unique()
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

    /// Gathers all unbound variables in the provided `typ` as type values.
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
                        vec![self
                            .generate_lean_type_value(&NoirType::TypeVariable(tv.clone()), None)]
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
                        vec![self.generate_lean_type_value(
                            &NoirType::TypeVariable(ng.type_var.clone()),
                            None,
                        )]
                    }
                }
            },
            _ => Vec::default(),
        }
    }

    /// Gathers all unbound variables in the provided `typ` as type patterns.
    ///
    /// # Panics
    ///
    /// - If there is an unbound type pattern in the generic values of a type.
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
                TypeBinding::Unbound(..) => {
                    panic!(
                        "Encountered unbound type variable {:?} in generic values",
                        tv.id()
                    );
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
                            Some(sanitize_generic_name(&ng.name)),
                        )]
                    }
                }
            },
            _ => Vec::default(),
        }
    }

    /// If `typ` is a type variable binding to `Self`, it is replaced with the
    /// provided `self_resolved`.
    pub fn replace_self_type_with(&self, typ: &Type, self_resolved: Type) -> Type {
        match &typ.expr {
            TypeExpr::TypeVariable(name) => {
                if name == "Self" {
                    self_resolved
                } else {
                    typ.clone()
                }
            }
            _ => typ.clone(),
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
                let typ = self.generate_lean_type_value(typ, None);
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

    /// Generates the AST for a global definition corresponding to the Noir IR.
    //
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
                let name = self.fully_qualified_global_name(id);
                let typ = self.generate_lean_type_value(&binding.r#type, None);
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
        let trait_name =
            self.resolve_fq_trait_name_from_crate_id(trait_def_data.crate_id, trait_def_id);
        let trait_name = quote_lean_keywords(&trait_name);
        let self_type = self.generate_lean_type_value(&trait_impl.typ, None);

        let where_clauses = trait_impl
            .where_clause
            .iter()
            .map(|cons| {
                let var = self.generate_lean_type_value(&cons.typ, None);
                let trait_data = self.context.def_interner.get_trait(cons.trait_bound.trait_id);
                let trait_name =
                    &self.resolve_fq_trait_name_from_crate_id(trait_data.crate_id, trait_data.id);
                let trait_name = &quote_lean_keywords(trait_name);
                let generics = &cons.trait_bound.trait_generics;
                let generics = generics
                    .ordered
                    .iter()
                    .chain(generics.named.iter().map(|g| &g.typ))
                    .map(|g| self.generate_lean_type_value(g, None))
                    .collect_vec();
                let bound = Type::data_type(trait_name, generics.clone());

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
            .map(|g| self.generate_lean_type_value(g, None))
            .collect_vec();

        // If type patterns have the same name and kind, they are the same variable at
        // the definition site, so we can correctly unique them.
        let generic_vars = self.gather_trait_impl_generics(&trait_impl);

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

        for typ in &trait_impl.trait_generics {
            patterns.extend(self.gather_unbound_vars_patterns(typ, &mut seen));
        }

        patterns.extend(self.gather_trait_constraint_generics_patterns(&trait_impl.where_clause));

        patterns.into_iter().unique().collect_vec()
    }

    pub fn generate_trait_function_def(
        &self,
        id: FuncId,
        trait_generics: &[TypePattern],
    ) -> FunctionDefinition {
        // Note that we NEVER want to qualify the name of the trait function.
        let function_meta = self.context.function_meta(&id);
        let name = self.context.function_name(&id).to_string();
        let name = quote_lean_keywords(&name);

        let parameters = self.generate_function_parameters(function_meta);
        let return_type = self.generate_lean_type_value(function_meta.return_type(), None);

        // If type patterns have the same name and kind, they are the same variable at
        // the definition site, so we can correctly unique them.
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
        let output_type = self.generate_lean_type_value(&self.resolve_bound_type(id), None);

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
        let return_type = self.generate_lean_type_value(&lambda.return_type, None);
        let params = lambda
            .parameters
            .iter()
            .map(|(p, t)| {
                let pat = self.generate_pattern(p);
                let typ = self.generate_lean_type_value(t, None);
                (pat, typ)
            })
            .collect_vec();
        let captures = lambda
            .captures
            .iter()
            .map(|v| {
                let noir_type = self.context.def_interner.definition_type(v.ident.id);
                let ident_type = self.generate_lean_type_value(&noir_type, None);
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
                let typ = self.generate_lean_type_value(
                    &self.context.def_interner.definition_type(def_id),
                    None,
                );
                let name =
                    sanitize_variable_name(self.context.def_interner.definition_name(def_id));

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
                let typ = self.generate_lean_type_value(typ, None);
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
        let elem_types = elems
            .iter()
            .map(|e| self.generate_lean_type_value(&self.resolve_bound_type(*e), None))
            .collect_vec();
        let return_type = Type::tuple(&elem_types);

        let call_ref = Expression::BuiltinCallRef(BuiltinCallRef {
            name:        MAKE_STRUCT_BUILTIN_NAME.to_string(),
            return_type: return_type.clone(),
        });

        let fields = elems.iter().map(|e| self.generate_expr(*e)).collect_vec();

        let call_expr = Call {
            function: Box::new(call_ref),
            params: fields,
            return_type,
        };

        Expression::Call(call_expr)
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
        let builtin_ref = Expression::builtin_call_ref(ASSERT_BUILTIN_NAME, output_type);
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
        let target = self.generate_lean_type_value(&cast.r#type, None);

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
        let name = self.fully_qualified_struct_path(&crate_id, &struct_def.id);
        let name = quote_lean_keywords(&name);
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
            .map(|t| self.generate_lean_type_value(t, None))
            .collect_vec();

        let return_type = Type::data_type(&name, generic_args);

        let call_ref = Expression::BuiltinCallRef(BuiltinCallRef {
            name:        MAKE_STRUCT_BUILTIN_NAME.to_string(),
            return_type: return_type.clone(),
        });

        let call_expr = Call {
            function: Box::new(call_ref),
            params: fields,
            return_type,
        };

        Expression::Call(call_expr)
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

        let call_target = Expression::builtin_call_ref(index_builtin_name.as_str(), output_type);
        let collection_expr = self.generate_expr(index.collection);
        let index_expr = self.generate_expr(index.index);
        // We don't want to cast if we already have a numeric literal of the right type,
        // but if we have a literal of the wrong type or a non-literal we need to cast
        // for correctness.
        let index_expr = match &index_expr {
            Expression::Literal(lit) => match lit {
                Literal::Numeric(NumericLiteral { typ, .. }) => match &typ.expr {
                    TypeExpr::Builtin(builtin) => match builtin.tag {
                        BuiltinTag::U(width) => {
                            if width == 32 {
                                index_expr
                            } else {
                                Expression::Cast(Cast {
                                    lhs:    Box::new(index_expr),
                                    target: Type::integer(32, false),
                                })
                            }
                        }
                        _ => Expression::Cast(Cast {
                            lhs:    Box::new(index_expr),
                            target: Type::integer(32, false),
                        }),
                    },
                    _ => Expression::Cast(Cast {
                        lhs:    Box::new(index_expr),
                        target: Type::integer(32, false),
                    }),
                },
                _ => panic!("Non numeric literal {lit:?} encountered as index in index expression"),
            },
            _ => Expression::Cast(Cast {
                lhs:    Box::new(index_expr),
                target: Type::integer(32, false),
            }),
        };

        let call = Call {
            function:    Box::new(call_target),
            params:      vec![collection_expr, index_expr],
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
            let builtin_target = Expression::builtin_call_ref(builtin_name.as_str(), output_type);
            let call = Call {
                function:    Box::new(builtin_target),
                params:      vec![lhs, rhs],
                return_type: output_type.clone(),
            };
            Expression::Call(call)
        } else {
            // If it doesn't correspond to a builtin call we need to convert it
            // into a trait call.
            let lhs_ty_lean = self.generate_lean_type_value(&lhs_ty_noir, None);
            let rhs_ty_lean = self.generate_lean_type_value(&rhs_ty_noir, None);
            let param_types = vec![lhs_ty_lean.clone(), rhs_ty_lean];
            let params = vec![lhs, rhs];
            let trait_method_id = self
                .context
                .def_interner
                .get_operator_trait_method(infix.operator.kind);

            let function_name = self
                .context
                .def_interner
                .definition_name(trait_method_id.item_id)
                .to_string();
            let trait_name = self
                .context
                .def_interner
                .get_trait(trait_method_id.trait_id)
                .name
                .to_string();

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
            let builtin_target = Expression::builtin_call_ref(builtin_name.as_str(), output_type);
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
            let function_name = self
                .context
                .def_interner
                .definition_name(trait_method_id.item_id)
                .to_string();
            let corresponding_trait = self.context.def_interner.get_trait(trait_method_id.trait_id);
            let trait_name = corresponding_trait.name.to_string();

            let call_target = TraitCallRef {
                trait_name,
                function_name,
                self_type: self.generate_lean_type_value(&rhs_ty, None),
                trait_generics: Vec::default(),
                fun_generics: Vec::default(),
                param_types: vec![self.generate_lean_type_value(&rhs_ty, None)],
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

    /// Generates the code corresponding to a literal.
    ///
    /// # Panics
    ///
    /// - When encountering a malformed literal that should have been validated
    ///   by the Noir compiler.
    #[expect(clippy::too_many_lines)] // It does not make sense to split it up.
    pub fn generate_literal(&self, literal: &HirLiteral, output_type: &Type) -> Expression {
        match literal {
            HirLiteral::Array(arr) => match arr {
                HirArrayLiteral::Standard(elems) => {
                    let elems = elems.iter().map(|e| self.generate_expr(*e)).collect_vec();
                    let call = Call {
                        function:    Box::new(Expression::builtin_call_ref(
                            MAKE_ARRAY_BUILTIN_NAME,
                            output_type,
                        )),
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
                        function:    Box::new(Expression::builtin_call_ref(
                            MAKE_REPEATED_ARRAY_BUILTIN_NAME,
                            output_type,
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
                        function:    Box::new(Expression::builtin_call_ref(
                            MAKE_SLICE_BUILTIN_NAME,
                            output_type,
                        )),
                        params:      elems,
                        return_type: output_type.clone(),
                    };
                    Expression::Call(call)
                }
                HirArrayLiteral::Repeated {
                    repeated_element,
                    length,
                } => {
                    let repeated_elem = self.generate_expr(*repeated_element);

                    // The length is a type, but we fundamentally want to treat it as a value in all
                    // cases, so we perform the conversion up-front.
                    let length = self.generate_lean_type_value(length, None);
                    let length_lit = match length.expr {
                        TypeExpr::NumericConst(n) => Literal::Numeric(NumericLiteral {
                            value: n,
                            typ:   length.kind.into_type(),
                        }),
                        TypeExpr::TypeVariable(name) => {
                            Literal::ConstGeneric(ConstGenericLiteral {
                                name,
                                kind: length.kind,
                            })
                        }
                        _ => panic!(
                            "Encountered invalid numeric generic type {length:?} for repeated \
                             slice length"
                        ),
                    };

                    let length = Expression::Literal(length_lit);
                    let params = vec![repeated_elem, length];
                    let call = Call {
                        function: Box::new(Expression::builtin_call_ref(
                            MAKE_REPEATED_SLICE_BUILTIN_NAME,
                            output_type,
                        )),
                        params,
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

                Expression::Literal(Literal::Numeric(literal))
            }
            HirLiteral::Str(value) => Expression::Literal(Literal::String(value.clone())),
            HirLiteral::FmtStr(parts, vars, _) => {
                let template = Expression::Literal(Literal::String(
                    parts.iter().map(std::string::ToString::to_string).join("{}"),
                ));
                let vars = vars.iter().map(|e| self.generate_expr(*e));
                let all_vars = vec![template].into_iter().chain(vars).collect_vec();

                let call = Call {
                    function:    Box::new(Expression::builtin_call_ref(
                        "mkFormatString",
                        output_type,
                    )),
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
        let name = self.context.def_interner.definition_name(ident.id).to_string();
        let name = quote_lean_keywords(&name);
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
                let fun_generics = self.gather_function_call_site_generic_values(expr, func_meta);

                if func_meta.trait_impl.is_some() || func_meta.trait_id.is_some() {
                    let trait_id = if let Some(trait_impl_id) = func_meta.trait_impl {
                        self.context
                            .def_interner
                            .get_trait_implementation(trait_impl_id)
                            .borrow()
                            .trait_id
                    } else if let Some(trait_id) = func_meta.trait_id {
                        trait_id
                    } else {
                        unreachable!("Invalid case of traits for function discovered")
                    };

                    let trait_data = self.context.def_interner.get_trait(trait_id);
                    let trait_name = self
                        .resolve_fq_trait_name_from_crate_id(trait_data.crate_id, trait_data.id);
                    let self_type = func_meta.self_type.as_ref().map_or_else(
                        || panic!("Trait function {name} missing Self type"),
                        |t| self.generate_lean_type_value(t, Some(bindings)),
                    );
                    let trait_generics = if func_meta.trait_impl.is_some() {
                        let trait_impl = self
                            .context
                            .def_interner
                            .get_trait_implementation(func_meta.trait_impl.unwrap());
                        let trait_impl = trait_impl.borrow();
                        trait_impl
                            .trait_generics
                            .iter()
                            .map(|t| self.generate_lean_type_value(t, Some(bindings)))
                            .collect_vec()
                    } else {
                        trait_data
                            .generics
                            .iter()
                            .map(|rg| NoirType::TypeVariable(rg.type_var.clone()))
                            .map(|t| self.generate_lean_type_value(&t, Some(bindings)))
                            .collect_vec()
                    };
                    let param_types = func_meta
                        .parameters
                        .iter()
                        .map(|(_, t, _)| self.generate_lean_type_value(t, Some(bindings)))
                        .map(|t| self.replace_self_type_with(&t, self_type.clone()))
                        .collect_vec();
                    let return_type = self.replace_self_type_with(
                        &self.generate_lean_type_value(func_meta.return_type(), Some(bindings)),
                        self_type.clone(),
                    );

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
                    let return_type =
                        self.generate_lean_type_value(func_meta.return_type(), Some(bindings));

                    match func_meta.kind {
                        FunctionKind::LowLevel | FunctionKind::Builtin => {
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
                                _ => panic!(
                                    "Unsupported function kind {func_kind:?} encountered for \
                                     builtin"
                                ),
                            };

                            Expression::BuiltinCallRef(BuiltinCallRef { name, return_type })
                        }
                        FunctionKind::Normal => {
                            let func_name = match &func_meta.self_type {
                                Some(self_type) => {
                                    let maybe_self_type =
                                        self.generate_lean_type_value(self_type, None);
                                    if let TypeExpr::Struct(s) = maybe_self_type.expr {
                                        let struct_path = s.name;
                                        format!("{struct_path}::{name}")
                                    } else {
                                        self.fully_qualified_function_name(
                                            &func_meta.source_crate,
                                            id,
                                        )
                                    }
                                }
                                None => {
                                    self.fully_qualified_function_name(&func_meta.source_crate, id)
                                }
                            };

                            let param_types = func_meta
                                .parameters
                                .iter()
                                .map(|(_, t, _)| self.generate_lean_type_value(t, Some(bindings)))
                                .collect_vec();

                            Expression::DeclCallRef(DeclCallRef {
                                function: func_name,
                                generics: fun_generics,
                                param_types,
                                return_type,
                            })
                        }
                        _ => panic!(
                            "Encountered a call to a function with kind {:?} where none should \
                             occur",
                            func_meta.kind
                        ),
                    }
                }
            }
            DefinitionKind::Global(id) => {
                let global_info = self.context.def_interner.get_global(*id);
                let let_stmt = self.context.def_interner.statement(&global_info.let_statement);
                let (global_name, global_type) = match let_stmt {
                    HirStatement::Let(let_stmt) => {
                        let name = self.fully_qualified_global_name(id);
                        let name = quote_lean_keywords(&name);
                        let typ = self.generate_lean_type_value(&let_stmt.r#type, None);
                        (name, typ)
                    }
                    _ => panic!("Encountered a global that was not defined with a let binding"),
                };

                let global_call = GlobalCallRef {
                    name: global_name,
                    typ:  global_type,
                };

                Expression::GlobalCallRef(global_call)
            }
            DefinitionKind::Local(_) => {
                let typ = output_type.clone();

                if let TypeExpr::Function(_) = &typ.expr {
                    let ident = IdentCallRef {
                        name:      sanitize_variable_name(&name),
                        func_type: typ.expr,
                    };

                    Expression::IdentCallRef(ident)
                } else {
                    let identifier = Identifier {
                        name: sanitize_variable_name(&name),
                        typ:  output_type.clone(),
                    };

                    Expression::Ident(identifier)
                }
            }
            DefinitionKind::NumericGeneric(_, kind) => {
                let kind = match self.generate_lean_type_value(kind, None).expr {
                    TypeExpr::Builtin(b) => match b.tag {
                        BuiltinTag::Field => Kind::Field,
                        BuiltinTag::U(w) => Kind::U(w),
                        _ => panic!("Invalid kind for const generic"),
                    },
                    _ => panic!("Invalid kind for const generic"),
                };

                let literal = Literal::ConstGeneric(ConstGenericLiteral { name, kind });

                Expression::Literal(literal)
            }
            DefinitionKind::AssociatedConstant(..) => {
                unimplemented!("Support for associated constants")
            }
        }
    }

    pub fn generate_block_expression(&self, block: &HirBlockExpression) -> Expression {
        let num_to_drop = usize::from(matches!(
            block
                .statements
                .last()
                .map(|id| self.context.def_interner.statement(id)),
            Some(HirStatement::Expression(_))
        ));

        let statements = block
            .statements
            .iter()
            .dropping_back(num_to_drop)
            .map(|stmt| self.generate_statement(*stmt))
            .collect_vec();

        let return_expr = if let Some(stmt) = block.statements.last() {
            if let HirStatement::Expression(expr) = self.context.def_interner.statement(stmt) {
                Some(Box::new(self.generate_expr(expr)))
            } else {
                Some(Box::new(Expression::Skip))
            }
        } else {
            Some(Box::new(Expression::Skip))
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
        let loop_variable =
            sanitize_variable_name(self.context.def_interner.definition_name(fors.identifier.id));

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
        let typ = self.generate_lean_type_value(&self.resolve_bound_type(assign.expression), None);
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
                name: self.context.def_interner.definition_name(ident.id).to_string(),
                typ:  self.generate_lean_type_value(typ, None),
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
                let typ = self.generate_lean_type_value(typ, None);

                LValue::MemberAccess { object, index, typ }
            }
            HirLValue::Index {
                array, index, typ, ..
            } => {
                let lhs_type = match array.as_ref() {
                    HirLValue::Ident(_, typ)
                    | HirLValue::MemberAccess { typ, .. }
                    | HirLValue::Index { typ, .. }
                    | HirLValue::Dereference {
                        element_type: typ, ..
                    } => typ,
                };
                let array = Box::new(self.generate_lvalue(array));
                let index = self.generate_expr(*index);
                let typ = self.generate_lean_type_value(typ, None);

                match lhs_type {
                    NoirType::Array(..) => LValue::ArrayIndex { array, index, typ },
                    NoirType::Slice(_) => LValue::SliceIndex {
                        slice: array,
                        index,
                        typ,
                    },
                    _ => panic!("Encountered non-indexable type {lhs_type:?} in lvalue"),
                }
            }
            HirLValue::Dereference {
                lvalue,
                element_type,
                ..
            } => {
                let object = Box::new(self.generate_lvalue(lvalue));
                let element_type = self.generate_lean_type_value(element_type, None);
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
        let typ = self.generate_lean_type_value(&lets.r#type, None);

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

    /// Returns the fully-qualified struct path for the described struct.
    pub fn fully_qualified_struct_path(
        &self,
        source_crate: &CrateId,
        struct_id: &TypeId,
    ) -> String {
        let fq_name = self.context.fully_qualified_struct_path(source_crate, *struct_id);
        if source_crate.is_stdlib() {
            format!("std::{fq_name}")
        } else {
            fq_name
        }
    }

    /// Returns the fully-qualified function name for the described function.
    pub fn fully_qualified_function_name(
        &self,
        source_crate: &CrateId,
        func_id: &FuncId,
    ) -> String {
        let fq_name = self.context.fully_qualified_function_name(source_crate, func_id);
        if source_crate.is_stdlib() {
            format!("std::{fq_name}")
        } else {
            fq_name
        }
    }

    /// Returns the fully-qualified global name for the described global.
    ///
    /// # Panics
    ///
    /// - If the global definition is not a let binding.
    pub fn fully_qualified_global_name(&self, id: &GlobalId) -> String {
        let global_data = self.context.def_interner.get_global(*id);
        let statement = self.context.def_interner.statement(&global_data.let_statement);

        match statement {
            HirStatement::Let(binding) => match binding.pattern {
                HirPattern::Identifier(hir_ident) => {
                    let def_name =
                        self.context.def_interner.definition_name(hir_ident.id).to_string();

                    let krate = self
                        .context
                        .def_map(&global_data.crate_id)
                        .expect("module should exist in context");
                    if let Some((id, mod_data)) = krate.modules().iter().find(|(_, m)| {
                        m.value_definitions()
                            .any(|i| matches!(i, ModuleDefId::GlobalId(inner) if *id == inner))
                    }) {
                        let module_path = krate.get_module_path_with_separator(
                            LocalModuleId::new(id),
                            mod_data.parent,
                            "::",
                        );

                        if self.root_crate_is_stdlib() {
                            if module_path.is_empty() {
                                format!("std::{def_name}")
                            } else {
                                format!("std::{module_path}::{def_name}")
                            }
                        } else if module_path.is_empty() {
                            def_name.to_string()
                        } else {
                            format!("{module_path}::{def_name}")
                        }
                    } else {
                        def_name.to_string()
                    }
                }
                _ => panic!("Encountered a malformed global"),
            },
            _ => panic!("Encountered a malformed global"),
        }
    }
}

/// Replaces invalid characters within a generic name to create a recognizable
/// but valid generic name.
#[must_use]
pub fn sanitize_generic_name(name: &str) -> String {
    name.replace("::", "_").replace(' ', "_").replace(['<', '>'], "")
}

/// Replaces invalid characters in a variable name to create a recognizable but
/// valid variable name.
#[must_use]
pub fn sanitize_variable_name(name: &str) -> String {
    name.replace('$', "ζ")
}

/// Quotes the Lean keywords in the fully qualified name to avoid conflicts with
/// the Lean parser
fn quote_lean_keywords(text: &str) -> String {
    text.split("::")
        .map(|part| {
            if conflicts_with_lean_keyword(part) {
                format!("{LEAN_QUOTE_START}{part}{LEAN_QUOTE_END}")
            } else {
                part.to_string()
            }
        })
        .join("::")
}

/// A container for top-level non-type definitions in a module.
pub struct ModuleDefs {
    /// All free function definitions in the module.
    pub func_defs: Vec<(Location, FunctionDefinition)>,

    /// All global definitions in the module.
    pub global_defs: Vec<(Location, GlobalDefinition)>,
}
