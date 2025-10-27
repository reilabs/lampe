//! This file contains the definition of the AST used for compiling the Noir
//! program to the Lean DSL.

use fm::FileId;

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Crate {
    pub types:   Vec<TypeDefinition>,
    pub modules: Vec<Module>,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Module {
    pub name:    String,
    pub id:      FileId,
    pub entries: Vec<ModuleDefinition>,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ModuleDefinition {
    Global(GlobalDefinition),
    Function(FunctionDefinition),
    TraitImpl(TraitImplementation),
}

impl ModuleDefinition {
    #[must_use]
    pub fn name(&self) -> &str {
        match self {
            ModuleDefinition::Global(g) => &g.name,
            ModuleDefinition::Function(f) => &f.name,
            ModuleDefinition::TraitImpl(t) => &t.name,
        }
    }
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct GlobalDefinition {
    pub name: String,
    pub typ:  Type,
    pub expr: Expression,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum TypeDefinition {
    Alias(TypeAlias),
    Struct(StructDefinition),
    Trait(TraitDefinition),
}

impl TypeDefinition {
    #[must_use]
    pub fn name(&self) -> &str {
        match self {
            TypeDefinition::Alias(a) => &a.name,
            TypeDefinition::Struct(s) => &s.name,
            TypeDefinition::Trait(t) => &t.name,
        }
    }
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TypeAlias {
    pub name:     String,
    pub typ:      Type,
    pub generics: Vec<TypePattern>,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TraitDefinition {
    pub name:             String,
    pub generics:         Vec<TypePattern>,
    pub associated_types: Vec<TypePattern>,
    pub methods:          Vec<TraitMethodDeclaration>,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TraitMethodDeclaration {
    pub name:        String,
    pub generics:    Vec<TypePattern>,
    pub parameters:  Vec<Type>,
    pub return_type: Box<Type>,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TraitImplementation {
    pub name:          String,
    pub trait_name:    String,
    pub self_type:     Type,
    pub where_clauses: Vec<WhereClause>,
    pub generic_vars:  Vec<TypePattern>,
    pub generic_vals:  Vec<Type>,
    pub methods:       Vec<FunctionDefinition>,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct WhereClause {
    pub var:      Type,
    pub bound:    Type,
    pub generics: Vec<Type>,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Deprecation {
    pub is_deprecated: bool,
    pub message:       Option<String>,
}
impl Deprecation {
    /// Something that is not deprecated.
    #[must_use]
    pub fn undeprecated() -> Self {
        Self {
            is_deprecated: false,
            message:       None,
        }
    }

    /// Returns not deprecated if the outer `Option` is `None`, otherwise
    /// returns deprecated with the optional message.
    #[must_use]
    pub fn from_noir(depr_note: Option<Option<String>>) -> Self {
        match depr_note {
            None => Self::undeprecated(),
            Some(message) => Self {
                is_deprecated: true,
                message,
            },
        }
    }
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct FunctionDefinition {
    pub name:        String,
    pub generics:    Vec<TypePattern>,
    pub parameters:  Vec<ParamDef>,
    pub return_type: Type,
    pub body:        Expression,
    pub deprecation: Deprecation,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct StructDefinition {
    pub name:        String,
    pub generics:    Vec<TypePattern>,
    pub members:     Vec<Type>,
    pub deprecation: Deprecation,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ParamDef {
    pub name:   String,
    pub typ:    Type,
    pub is_mut: bool,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ParamVal {
    pub name:  String,
    pub value: Box<Expression>,
}

#[expect(clippy::large_enum_variant)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Statement {
    Assign(AssignStatement),
    Expression(Expression),
    For(ForStatement),
    Let(LetStatement),
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LetStatement {
    pub pattern:    Pattern,
    pub typ:        Type,
    pub expression: Box<Expression>,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct AssignStatement {
    pub name:       LValue,
    pub typ:        Type,
    pub expression: Expression,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum LValue {
    Ident(Identifier),
    MemberAccess { object: Box<LValue>, index: usize, typ: Type },
    ArrayIndex { array: Box<LValue>, index: Expression, typ: Type },
    SliceIndex { slice: Box<LValue>, index: Expression, typ: Type },
    Dereference { object: Box<LValue>, element_type: Type },
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ForStatement {
    pub loop_variable: String,
    pub start_range:   Box<Expression>,
    pub end_range:     Box<Expression>,
    pub body:          Box<Expression>,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Expression {
    Block(Block),
    BuiltinCallRef(BuiltinCallRef),
    Call(Call),
    Cast(Cast),
    DeclCallRef(DeclCallRef),
    Ident(Identifier),
    IdentCallRef(IdentCallRef),
    IfThenElse(IfThenElse),
    Index(Index),
    Lambda(Lambda),
    Literal(Literal),
    MemberAccess(MemberAccess),
    Skip,
    TraitCallRef(TraitCallRef),
    GlobalCallRef(GlobalCallRef),
}

impl Expression {
    #[must_use]
    pub fn builtin_call_ref(name: &str, typ: &Type) -> Self {
        Self::BuiltinCallRef(BuiltinCallRef {
            name:        name.to_string(),
            return_type: typ.clone(),
        })
    }
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct IdentCallRef {
    pub name:      String,
    pub func_type: TypeExpr,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct MemberAccess {
    pub value: Box<Expression>,
    pub index: usize,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Pattern {
    Identifier(Identifier),
    Mutable(Box<Pattern>),
    Tuple(Vec<Pattern>),
    Struct(StructPattern),
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TuplePattern {
    pub typ:    Type,
    pub fields: Vec<Pattern>,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct StructPattern {
    pub typ:    Type,
    pub fields: Vec<(String, Pattern)>,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Lambda {
    pub params:      Vec<(Pattern, Type)>,
    pub return_type: Type,
    pub body:        Box<Expression>,
    pub captures:    Vec<Expression>,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Index {
    pub value: Box<Expression>,
    pub index: Box<Expression>,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Cast {
    pub lhs:    Box<Expression>,
    pub target: Type,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Literal {
    Bool(bool),
    ConstGeneric(ConstGenericLiteral),
    Numeric(NumericLiteral),
    String(String),
    Unit,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ConstGenericLiteral {
    pub name: String,
    pub kind: Kind,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct NumericLiteral {
    pub value: String,
    pub typ:   Type,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Identifier {
    pub name: String,
    pub typ:  Type,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Block {
    pub statements: Vec<Statement>,
    pub expression: Option<Box<Expression>>,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct IfThenElse {
    pub condition:   Box<Expression>,
    pub then_branch: Box<Expression>,
    pub else_branch: Option<Box<Expression>>,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BuiltinCallRef {
    pub name:        String,
    pub return_type: Type,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DeclCallRef {
    pub function:    String,
    pub generics:    Vec<Type>,
    pub param_types: Vec<Type>,
    pub return_type: Type,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct GlobalCallRef {
    pub name: String,
    pub typ:  Type,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TraitCallRef {
    pub trait_name:     String,
    pub function_name:  String,
    pub self_type:      Type,
    pub trait_generics: Vec<Type>,
    pub fun_generics:   Vec<Type>,
    pub param_types:    Vec<Type>,
    pub return_type:    Type,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Call {
    pub function:    Box<Expression>,
    pub params:      Vec<Expression>,
    pub return_type: Type,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Type {
    pub expr: TypeExpr,
    pub kind: Kind,
}
impl Type {
    #[must_use]
    pub fn builtin(expr: TypeExpr, kind: Kind) -> Self {
        Type { expr, kind }
    }

    #[must_use]
    pub fn array(elem: Type, len: Type) -> Self {
        Type {
            expr: TypeExpr::builtin(BuiltinTag::Array, &[elem, len]),
            kind: Kind::Type,
        }
    }

    #[must_use]
    pub fn slice(elem: Type) -> Self {
        Type {
            expr: TypeExpr::builtin(BuiltinTag::Slice, &[elem]),
            kind: Kind::Type,
        }
    }

    #[must_use]
    pub fn field() -> Self {
        Type {
            expr: TypeExpr::builtin(BuiltinTag::Field, &[]),
            kind: Kind::Type,
        }
    }

    #[must_use]
    pub fn integer(size: u64, signed: bool) -> Self {
        let tag = if signed {
            BuiltinTag::I(size)
        } else {
            BuiltinTag::U(size)
        };
        Type {
            expr: TypeExpr::builtin(tag, &[]),
            kind: Kind::Type,
        }
    }

    #[must_use]
    pub fn bool() -> Self {
        Type {
            expr: TypeExpr::builtin(BuiltinTag::Bool, &[]),
            kind: Kind::Type,
        }
    }

    #[must_use]
    pub fn string(size: Type) -> Self {
        Type {
            expr: TypeExpr::builtin(BuiltinTag::String, &[size]),
            kind: Kind::Type,
        }
    }

    #[must_use]
    pub fn fmt_string(length: Type, args: Type) -> Self {
        Type {
            expr: TypeExpr::builtin(BuiltinTag::FmtString, &[length, args]),
            kind: Kind::Type,
        }
    }

    #[must_use]
    pub fn variable(name: String, kind: Kind) -> Self {
        Type {
            expr: TypeExpr::TypeVariable(name),
            kind,
        }
    }

    #[must_use]
    pub fn unit() -> Self {
        Type {
            expr: TypeExpr::builtin(BuiltinTag::Unit, &[]),
            kind: Kind::Type,
        }
    }

    #[must_use]
    pub fn tuple(elems: &[Type]) -> Self {
        Type {
            expr: TypeExpr::builtin(BuiltinTag::Tuple, elems),
            kind: Kind::Type,
        }
    }

    #[must_use]
    pub fn data_type(name: &str, generics: Vec<Type>) -> Self {
        Type {
            expr: TypeExpr::Struct(DataTypeExpr {
                name: name.to_string(),
                generics,
            }),
            kind: Kind::Type,
        }
    }

    #[must_use]
    pub fn alias(name: &str, generics: Vec<Type>) -> Self {
        Type {
            expr: TypeExpr::Alias(DataTypeExpr {
                name: name.to_string(),
                generics,
            }),
            kind: Kind::Type,
        }
    }

    #[must_use]
    pub fn cast(target: Type) -> Self {
        Type {
            expr: TypeExpr::Cast(CastTypeExpr {
                target: Box::new(target),
            }),
            kind: Kind::Type,
        }
    }

    #[must_use]
    pub fn function(params: Vec<Type>, ret: Type, captures: Type) -> Self {
        Type {
            expr: TypeExpr::Function(FunctionTypeExpr {
                arguments:   params,
                return_type: Box::new(ret),
                captures:    Box::new(captures),
            }),
            kind: Kind::Type,
        }
    }

    #[must_use]
    pub fn immutable_reference(typ: Type) -> Self {
        Type {
            expr: TypeExpr::builtin(BuiltinTag::Reference(Mutability::Immutable), &[typ]),
            kind: Kind::Type,
        }
    }

    #[must_use]
    pub fn mutable_reference(typ: Type) -> Self {
        Type {
            expr: TypeExpr::builtin(BuiltinTag::Reference(Mutability::Mutable), &[typ]),
            kind: Kind::Type,
        }
    }

    #[must_use]
    pub fn numeric_const(value: &str, kind: Kind) -> Self {
        Type {
            expr: TypeExpr::NumericConst(value.to_string()),
            kind,
        }
    }

    #[must_use]
    pub fn infix(left: TypeExpr, op: TypeArithOp, right: TypeExpr, kind: Kind) -> Self {
        Type {
            expr: TypeExpr::Arith(TypeArithExpr {
                op,
                left: Box::new(left),
                right: Box::new(right),
            }),
            kind,
        }
    }
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Mutability {
    Immutable,
    Mutable,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum BuiltinTag {
    Array,
    Bool,
    Field,
    FmtString,
    I(u64),
    Quoted(String),
    Reference(Mutability),
    Slice,
    String,
    Tuple,
    U(u64),
    Unit,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum TypeArithOp {
    Add,
    Div,
    Mod,
    Mul,
    Sub,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum TypeExpr {
    Alias(DataTypeExpr),
    Arith(TypeArithExpr),
    Builtin(BuiltinTypeExpr),
    Cast(CastTypeExpr),
    Function(FunctionTypeExpr),
    NumericConst(String),
    Struct(DataTypeExpr),
    TypeVariable(String),
}
impl TypeExpr {
    #[must_use]
    pub fn builtin(tag: BuiltinTag, generics: &[Type]) -> Self {
        Self::Builtin(BuiltinTypeExpr {
            tag,
            generics: generics.to_owned(),
        })
    }
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BuiltinTypeExpr {
    pub tag:      BuiltinTag,
    pub generics: Vec<Type>,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CastTypeExpr {
    pub target: Box<Type>,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DataTypeExpr {
    pub name:     String,
    pub generics: Vec<Type>,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct FunctionTypeExpr {
    pub arguments:   Vec<Type>,
    pub return_type: Box<Type>,
    pub captures:    Box<Type>,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TypeArithExpr {
    pub op:    TypeArithOp,
    pub left:  Box<TypeExpr>,
    pub right: Box<TypeExpr>,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Kind {
    Field,
    Type,
    U(u64),
}

impl Kind {
    /// Converts `self` into a type if it corresponds to one.
    ///
    /// # Panics
    ///
    /// If `self` is a kind that does not have a corresponding type.
    #[must_use]
    pub fn into_type(self) -> Type {
        match self {
            Kind::Field => Type::field(),
            Kind::Type => panic!("Type is not supported for conversion to type"),
            Kind::U(n) => Type::integer(n, false),
        }
    }
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TypePattern {
    pub pattern: String,
    pub kind:    Kind,
}
