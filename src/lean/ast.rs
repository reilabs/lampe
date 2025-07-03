//! This file contains the definition of the AST used for compiling the Noir
//! program to the Lean DSL.

use fm::FileId;
use noirc_frontend::signed_field::SignedField;

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Crate {
    pub types:   Vec<TypeDefinition>,
    pub modules: Vec<Module>,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Module {
    pub id:          FileId,
    pub globals:     Vec<GlobalDefinition>,
    pub functions:   Vec<FunctionDefinition>,
    pub trait_impls: Vec<TraitImplementation>,
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
    pub bound:    TypePattern,
    pub generics: Vec<Type>,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct FunctionDefinition {
    pub name:        String,
    pub generics:    Vec<TypePattern>,
    pub parameters:  Vec<ParamDef>,
    pub return_type: Type,
    pub body:        Expression,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct NamedGeneric {
    pub name: String,
    pub kind: Kind,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct StructDefinition {
    pub name:     String,
    pub generics: Vec<TypePattern>,
    pub members:  Vec<ParamDef>,
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

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Statement {
    Assign(AssignStatement),
    Break,
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
    pub name:       String,
    pub typ:        Type,
    pub expression: Expression,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ForStatement {
    pub identifier:  String,
    pub start_range: Box<Expression>,
    pub end_range:   Box<Expression>,
    pub body:        Box<Expression>,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Expression {
    Block(Block),
    BuiltinCallRef(String),
    Call(Call),
    Cast(Cast),
    Constructor(Constructor),
    DeclCallRef(DeclCallRef),
    Ident(Identifier),
    IfThenElse(IfThenElse),
    Index(Index),
    Lambda(Lambda),
    Literal(Literal),
    TraitCallRef(TraitCallRef),
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Pattern {
    Identifier(Identifier),
    Mutable(Box<Pattern>),
    Tuple(Vec<Pattern>),
    Struct(StructPattern),
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct StructPattern {
    pub fields: Vec<Pattern>,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Lambda {
    pub params:      Vec<(Pattern, Type)>,
    pub return_type: Type,
    pub body:        Box<Expression>,
    pub captures:    Vec<Identifier>,
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
pub struct Constructor {
    pub typ:          Type,
    pub generic_args: Vec<TypeExpr>,
    pub fields:       Vec<ParamVal>,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Literal {
    Bool(bool),
    Integer(SignedField),
    String(String),
    Unit,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ArrayLiteral {
    pub elements: Vec<Expression>,
}
impl ArrayLiteral {
    pub fn len(&self) -> usize {
        self.elements.len()
    }
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct FormatString {
    pub template:  String,
    pub fragments: Vec<Expression>,
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
pub struct DeclCallRef {
    pub function:    String,
    pub generics:    Vec<Type>,
    pub param_types: Vec<TypeExpr>,
    pub return_type: TypeExpr,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TraitCallRef {
    pub trait_name:     String,
    pub function:       String,
    pub trait_generics: Vec<Type>,
    pub fun_generics:   Vec<Type>,
    pub param_types:    Vec<TypeExpr>,
    pub return_type:    TypeExpr,
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
    pub fn builtin(expr: TypeExpr, kind: Kind) -> Self {
        Type { expr, kind }
    }

    pub fn array(elem: TypeExpr, len: TypeExpr) -> Self {
        Type {
            expr: TypeExpr::builtin(BuiltinTag::Array, vec![elem, len]),
            kind: Kind::Type,
        }
    }

    pub fn slice(elem: TypeExpr) -> Self {
        Type {
            expr: TypeExpr::builtin(BuiltinTag::Slice, vec![elem]),
            kind: Kind::Type,
        }
    }

    pub fn field() -> Self {
        Type {
            expr: TypeExpr::builtin(BuiltinTag::Field, vec![]),
            kind: Kind::Type,
        }
    }

    pub fn integer(size: u64, signed: bool) -> Self {
        let tag = if signed {
            BuiltinTag::I(size)
        } else {
            BuiltinTag::U(size)
        };
        Type {
            expr: TypeExpr::builtin(tag, vec![]),
            kind: Kind::Type,
        }
    }

    pub fn bool() -> Self {
        Type {
            expr: TypeExpr::builtin(BuiltinTag::Bool, vec![]),
            kind: Kind::Type,
        }
    }

    pub fn string(size: TypeExpr) -> Self {
        Type {
            expr: TypeExpr::builtin(BuiltinTag::String, vec![size]),
            kind: Kind::Type,
        }
    }

    pub fn fmt_string(args: TypeExpr) -> Self {
        Type {
            expr: TypeExpr::builtin(BuiltinTag::FmtString, vec![args]),
            kind: Kind::Type,
        }
    }

    pub fn variable(name: String, kind: Kind) -> Self {
        Type {
            expr: TypeExpr::TypeVariable(name),
            kind,
        }
    }

    pub fn unit() -> Self {
        Type {
            expr: TypeExpr::builtin(BuiltinTag::Unit, Vec::default()),
            kind: Kind::Type,
        }
    }

    pub fn tuple(elems: Vec<TypeExpr>) -> Self {
        Type {
            expr: TypeExpr::builtin(BuiltinTag::Tuple, elems),
            kind: Kind::Type,
        }
    }

    pub fn data_type(name: &str, generics: Vec<TypeExpr>) -> Self {
        Type {
            expr: TypeExpr::Struct(DataTypeExpr {
                name: name.to_string(),
                generics,
            }),
            kind: Kind::Type,
        }
    }

    pub fn alias(name: &str, generics: Vec<TypeExpr>) -> Self {
        Type {
            expr: TypeExpr::Alias(DataTypeExpr {
                name: name.to_string(),
                generics,
            }),
            kind: Kind::Type,
        }
    }

    pub fn cast(target: TypeExpr) -> Self {
        Type {
            expr: TypeExpr::Cast(CastTypeExpr {
                target: Box::new(target),
            }),
            kind: Kind::Type,
        }
    }

    pub fn function(params: Vec<TypeExpr>, ret: TypeExpr, captures: TypeExpr) -> Self {
        Type {
            expr: TypeExpr::Function(FunctionTypeExpr {
                arguments:   params,
                return_type: Box::new(ret),
                captures:    Box::new(captures),
            }),
            kind: Kind::Type,
        }
    }

    pub fn immutable_reference(typ: TypeExpr) -> Self {
        Type {
            expr: TypeExpr::builtin(BuiltinTag::Reference(Mutability::Immutable), vec![typ]),
            kind: Kind::Type,
        }
    }

    pub fn mutable_reference(typ: TypeExpr) -> Self {
        Type {
            expr: TypeExpr::builtin(BuiltinTag::Reference(Mutability::Mutable), vec![typ]),
            kind: Kind::Type,
        }
    }

    pub fn numeric_const(value: &str, kind: Kind) -> Self {
        Type {
            expr: TypeExpr::NumericConst(value.to_string()),
            kind,
        }
    }

    pub fn infix(left: TypeExpr, op: TypeArithOp, right: TypeExpr) -> Self {
        Type {
            expr: TypeExpr::Arith(TypeArithExpr {
                op,
                left: Box::new(left),
                right: Box::new(right),
            }),
            kind: Kind::Type,
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
    pub fn builtin(tag: BuiltinTag, generics: Vec<TypeExpr>) -> Self {
        Self::Builtin(BuiltinTypeExpr {
            tag,
            generics: generics.to_vec(),
        })
    }
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BuiltinTypeExpr {
    pub tag:      BuiltinTag,
    pub generics: Vec<TypeExpr>,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CastTypeExpr {
    pub target: Box<TypeExpr>,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DataTypeExpr {
    pub name:     String,
    pub generics: Vec<TypeExpr>,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct FunctionTypeExpr {
    pub arguments:   Vec<TypeExpr>,
    pub return_type: Box<TypeExpr>,
    pub captures:    Box<TypeExpr>,
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

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TypePattern {
    pub pattern: String,
    pub kind:    Kind,
}
