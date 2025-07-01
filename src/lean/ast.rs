//! This file contains the definition of the AST used for compiling the Noir
//! program to the Lean DSL.

use noirc_frontend::signed_field::SignedField;

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Crate {
    pub types:   Vec<TypeDefinition>,
    pub modules: Vec<Module>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Module {
    pub name:        String,
    pub definitions: Vec<ModuleDefinition>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ModuleDefinition {
    Trait(TraitImplementation),
    Function(FunctionDefinition),
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum TypeDefinition {
    Alias(TypeAlias),
    Struct(StructDefinition),
    Trait(TraitDefinition),
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct TypeAlias {
    pub name: String,
    pub typ:  Type,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct TraitDefinition {
    pub name:     String,
    pub generics: Vec<NamedGeneric>,
    pub methods:  Vec<FunctionDefinition>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct TraitImplementation {
    pub name:     String,
    pub generics: Vec<Type>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct FunctionDefinition {
    pub name:        String,
    pub generics:    Vec<NamedGeneric>,
    pub parameters:  Vec<ParamDef>,
    pub return_type: TypeExpr,
    pub body:        Expression,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct NamedGeneric {
    pub name: String,
    pub kind: Kind,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct StructDefinition {
    pub name:     String,
    pub generics: Vec<NamedGeneric>,
    pub members:  Vec<ParamDef>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ParamDef {
    pub name: String,
    pub typ:  Type,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ParamVal {
    pub name:  String,
    pub value: Box<Expression>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Statement {
    Assign(AssignStatement),
    Break,
    Expression(Expression),
    For(ForStatement),
    Let(LetStatement),
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct LetStatement {
    pub pattern:    Pattern,
    pub typ:        Type,
    pub expression: Box<Expression>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct AssignStatement {
    pub name:       String,
    pub typ:        Type,
    pub expression: Expression,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ForStatement {
    pub identifier:  String,
    pub start_range: Box<Expression>,
    pub end_range:   Box<Expression>,
    pub body:        Box<Expression>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
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

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Pattern {
    Identifier(Identifier),
    Mutable(Box<Pattern>),
    Tuple(Vec<Pattern>),
    Struct(StructPattern),
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct StructPattern {
    pub fields: Vec<Pattern>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Lambda {
    pub params:      Vec<(Pattern, Type)>,
    pub return_type: Type,
    pub body:        Box<Expression>,
    pub captures:    Vec<Identifier>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Index {
    pub value: Box<Expression>,
    pub index: Box<Expression>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Cast {
    pub lhs:    Box<Expression>,
    pub target: Type,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Constructor {
    pub typ:          Type,
    pub generic_args: Vec<TypeExpr>,
    pub fields:       Vec<ParamVal>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Literal {
    Bool(bool),
    Integer(SignedField),
    String(String),
    Unit,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ArrayLiteral {
    pub elements: Vec<Expression>,
}
impl ArrayLiteral {
    pub fn len(&self) -> usize {
        self.elements.len()
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct FormatString {
    pub template:  String,
    pub fragments: Vec<Expression>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Identifier {
    pub name: String,
    pub typ:  Type,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Block {
    pub statements: Vec<Statement>,
    pub expression: Option<Box<Expression>>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct IfThenElse {
    pub condition:   Box<Expression>,
    pub then_branch: Box<Expression>,
    pub else_branch: Option<Box<Expression>>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct DeclCallRef {
    pub function:    String,
    pub generics:    Vec<Type>,
    pub param_types: Vec<TypeExpr>,
    pub return_type: TypeExpr,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct TraitCallRef {
    pub trait_name:     String,
    pub function:       String,
    pub trait_generics: Vec<Type>,
    pub fun_generics:   Vec<Type>,
    pub param_types:    Vec<TypeExpr>,
    pub return_type:    TypeExpr,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Call {
    pub function: Box<Expression>,
    pub params:   Vec<Expression>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
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
            expr: TypeExpr::array(len, elem),
            kind: Kind::Type,
        }
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum TypeExpr {
    Bool,
    BuiltinType(BuiltinType),
    Char,
    DataType(DataTypeTypeExpr),
    Field,
    FieldConst(String),
    FormatString(FormatStringTypeExpr),
    Integer(IntegerTypeExpr),
    Slice(SliceTypeExpr),
    Tuple(TupleTypeExpr),
    TypeVariable(String),
    UConst(u128),
    Unit,
}
impl TypeExpr {
    pub fn builtin(name: &str, generics: Vec<Type>) -> Self {
        Self::BuiltinType(BuiltinType {
            name:     name.to_string(),
            generics: generics.to_vec(),
        })
    }

    pub fn array(length: TypeExpr, typ: TypeExpr) -> Self {
        let length = Type {
            expr: length,
            kind: Kind::U(32),
        };
        let typ = Type {
            expr: typ,
            kind: Kind::Type,
        };
        Self::builtin("Array", vec![typ, length])
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct BuiltinType {
    name:     String,
    generics: Vec<Type>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct TupleTypeExpr {
    pub elements: Vec<Type>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct FormatStringTypeExpr {
    pub length:         Box<Type>,
    pub argument_types: Box<Type>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct IntegerTypeExpr {
    pub signed: bool,
    pub size:   u8,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct DataTypeTypeExpr {
    pub name:     String,
    pub generics: Vec<Type>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct SliceTypeExpr {
    pub elem_type: Box<Type>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ArrayTypeExpr {
    pub elem_type: Box<Type>,
    pub len:       Box<Type>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Kind {
    Field,
    Integer,
    IntegerOrField,
    Type,
    U(u64),
}
