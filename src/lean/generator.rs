//! This module contains the logic for analyzing the Noir source code and
//! generating the Lean AST from it.

use std::{cmp::Ordering, collections::HashSet};

use fm::FileId;
use itertools::Itertools;
use noirc_frontend::{
    graph::CrateId,
    hir::{def_map::ModuleDefId, Context},
    node_interner::{DependencyId, TraitId, TypeAliasId, TypeId},
    shared::Signedness,
    Kind as NoirKind,
    ResolvedGeneric,
    Type as NoirType,
};
use noirc_frontend::QuotedType::TypedExpr;
use petgraph::data::DataMap;

use crate::lean::ast::{ArrayTypeExpr, Crate, DataTypeTypeExpr, FormatStringTypeExpr, IntegerTypeExpr, Kind, NamedGeneric, ParamDef, SliceTypeExpr, StructDefinition, TraitDefinition, TupleTypeExpr, Type, TypeAlias, TypeDefinition, TypeExpr};

/// A generator for Lean definitions that correspond to the Noir project in
/// question.
pub struct LeanGenerator<'file_manager, 'parsed_files> {
    /// The compilation context for the Noir project.
    pub context: Context<'file_manager, 'parsed_files>,

    /// The identifier for the root crate in the Noir compilation context.
    root_crate: CrateId,

    /// The files contained in the root crate, used to filter out `std` and
    /// other crate files during generation.
    _known_files: HashSet<FileId>,
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
            _known_files: known_files,
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

        Crate {
            types,
            modules: vec![],
        }
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
            .map(|g| self.generate_named_generic(g))
            .collect_vec();

        let fields = struct_data.get_fields_as_written().unwrap_or_default();
        let members = fields
            .into_iter()
            .map(|f| {
                let name = f.name.to_string();
                let typ = self.generate_lean_type(&f.typ);
                ParamDef { name, typ }
            })
            .collect_vec();

        StructDefinition {
            name: qualified_path,
            generics,
            members,
        }
    }

    pub fn generate_lean_type(&self, typ: &NoirType) -> Type {
        match typ {
            NoirType::FieldElement => Type { expr: TypeExpr::Field, kind: Kind::Type },
            NoirType::Array(count, typ) => {
            },
            NoirType::Slice(typ) => {
                let expr = TypeExpr::Slice(SliceTypeExpr {
                    elem_type: Box::new(self.generate_lean_type(&typ)),
                });
                Type { expr, kind: Kind::Type}
            },
            NoirType::Integer(signedness, bit_size) => {
                let expr = TypeExpr::Integer(IntegerTypeExpr {
                    signed: match signedness {
                        Signedness::Unsigned => false,
                        Signedness::Signed => true,
                    },
                    size:   bit_size.bit_size(),
                });
                Type { expr, kind: Kind::Type }
            },
            NoirType::Bool => Type { expr: TypeExpr::Bool, kind: Kind::Type },
            NoirType::String(count) => {
                let expr = TypeExpr::Array(ArrayTypeExpr {
                    elem_type: Box::new(Type {
                        expr: TypeExpr::Char,
                        kind: Kind::Type,
                    }),
                    len:       Box::new(self.generate_lean_type(&count)),
                });
                Type { expr, kind: Kind::Type }
            },
            NoirType::FmtString(length, args) => {
                let length = Box::new(self.generate_lean_type(&length));
                let argument_types = Box::new(self.generate_lean_type(&args));
                let expr = TypeExpr::FormatString(FormatStringTypeExpr { length, argument_types });

                Type { expr, kind: Kind::Type }
            }
            NoirType::Unit => Type { expr: TypeExpr::Unit, kind: Kind::Type },
            NoirType::Tuple(elems) => {
                let elements = elems.iter().map(|e| self.generate_lean_type(e)).collect_vec();
                let expr = TypeExpr::Tuple(TupleTypeExpr { elements});
                Type { expr, kind: Kind::Type }
            }
            NoirType::DataType(struct_type, generics) => {
                let type_def = struct_type.borrow();
                let module_id = type_def.id.module_id();
                let name = self.context.fully_qualified_struct_path(&module_id.krate, type_def.id);
                let generics = generics.iter().map(|g| self.generate_lean_type(g)).collect_vec();
                let expr = TypeExpr::DataType(DataTypeTypeExpr { name, generics });

                Type { expr, kind: Kind::Type }
            }
            NoirType::Alias(alias, generics) => {
                let alias = alias.borrow();
                let underlying_type = self.generate_lean_type(&alias.typ);

                unimplemented!();
            }
            NoirType::TypeVariable(_) => unimplemented!(),
            NoirType::TraitAsType(..) => unimplemented!(),
            NoirType::NamedGeneric(_) => unimplemented!(),
            NoirType::CheckedCast { .. } => unimplemented!(),
            NoirType::Function(..) => unimplemented!(),
            NoirType::Reference(..) => unimplemented!(),
            NoirType::Forall(..) => unimplemented!(),
            NoirType::Constant(..) => unimplemented!(),
            NoirType::Quoted(_) => unimplemented!(),
            NoirType::InfixExpr(..) => unimplemented!(),
            NoirType::Error => panic!("Encountered error type"),
        }
    }

    pub fn generate_named_generic(&self, generic: &ResolvedGeneric) -> NamedGeneric {
        let name = generic.name.to_string();
        let kind = match generic.kind() {
            NoirKind::Any => Kind::Type,
            NoirKind::Normal => Kind::Type,
            NoirKind::IntegerOrField => Kind::IntegerOrField,
            NoirKind::Integer => Kind::Integer,
            NoirKind::Numeric(a) => {
                dbg!(a.as_monotype());
                unimplemented!("No idea what to do here, waiting for an example to cause a crash")
            }
        };

        NamedGeneric { name, kind }
    }

    pub fn generate_alias(&self, id: TypeAliasId) -> TypeAlias {
        let alias_data = self.context.def_interner.get_type_alias(id);
        let alias_data = alias_data.borrow();
        let name = alias_data.name.to_string();
        let generics =
        unimplemented!()
    }

    pub fn generate_trait_definition(&self, _id: TraitId) -> TraitDefinition {
        // TODO
        TraitDefinition {
            name:     "Bar".into(),
            generics: Vec::default(),
            methods:  Vec::default(),
        }
    }
}
