//! This file contains the definition of the AST used for compiling the Noir
//! program to the Lean DSL.

use noirc_frontend::signed_field::SignedField;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Crate {
    types:   Vec<TypeDefinition>,
    modules: Vec<Module>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Module {
    name:        String,
    definitions: Vec<ModuleDefinition>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ModuleDefinition {
    Trait(TraitImplementation),
    Function(FunctionDefinition),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TypeDefinition {
    Struct(StructDefinition),
    Trait(TraitDefinition),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TraitDefinition {
    name:     String,
    generics: Vec<Type>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TraitImplementation {
    name:     String,
    generics: Vec<Type>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FunctionDefinition {
    name:        String,
    generics:    Vec<Type>,
    parameters:  Vec<ParamDef>,
    return_type: TypeExpr,
    body:        Expression,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StructDefinition {
    name:     String,
    generics: Vec<Type>,
    members:  Vec<ParamDef>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ParamDef {
    name: String,
    typ:  TypeExpr,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ParamVal {
    name:  String,
    value: Box<Expression>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Statement {
    Assign(AssignStatement),
    Break,
    Expression(Expression),
    For(ForStatement),
    Let(LetStatement),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LetStatement {
    pattern:    Pattern,
    typ:        Type,
    expression: Box<Expression>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AssignStatement {
    name:       String,
    typ:        Type,
    expression: Expression,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ForStatement {
    identifier:  String,
    start_range: Box<Expression>,
    end_range:   Box<Expression>,
    body:        Box<Expression>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Expression {
    Ident(Identifier),
    Literal(Literal),
    Block(Block),
    DeclCallRef(DeclCallRef),
    IfThenElse(IfThenElse),
    TraitCallRef(TraitCallRef),
    Infix(Infix),
    Constructor(Constructor),
    Call(Call),
    Cast(Cast),
    Index(Index),
    Typle(Tuple),
    Lambda(Lambda),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Pattern {
    Identifier(Identifier),
    Mutable(Box<Pattern>),
    Tuple(Vec<Pattern>),
    Struct(StructPattern),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StructPattern {
    typ:    Type,
    fields: Vec<(Identifier, Pattern)>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Lambda {
    params:      Vec<(Pattern, Type)>,
    return_type: Type,
    body:        Box<Expression>,
    captures:    Vec<Identifier>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Tuple {
    elems: Vec<Expression>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Index {
    value: Box<Expression>,
    index: Box<Expression>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Cast {
    lhs:    Box<Expression>,
    target: Type,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Infix {
    lhs:      Box<Expression>,
    operator: String,
    rhs:      Box<Expression>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Constructor {
    typ:          Type,
    generic_args: Vec<TypeExpr>,
    fields:       Vec<ParamVal>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Literal {
    Array(ArrayLiteral),
    Bool(bool),
    FormatString(FormatString),
    Integer(SignedField),
    Slice(ArrayLiteral),
    String(String),
    Unit,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ArrayLiteral {
    elements: Vec<Expression>,
}
impl ArrayLiteral {
    pub fn len(&self) -> usize {
        self.elements.len()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FormatString {
    template:  String,
    fragments: Vec<Expression>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Identifier {
    name:     String,
    typ:      Type,
    generics: Vec<Type>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Block {
    statements: Vec<Statement>,
    expression: Box<Expression>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IfThenElse {
    condition:   Box<Expression>,
    then_branch: Box<Expression>,
    else_branch: Option<Box<Expression>>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DeclCallRef {
    function:    String,
    generics:    Vec<Type>,
    param_types: Vec<TypeExpr>,
    return_type: TypeExpr,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TraitCallRef {
    trait_name:     String,
    function:       String,
    trait_generics: Vec<Type>,
    fun_generics:   Vec<Type>,
    param_types:    Vec<TypeExpr>,
    return_type:    TypeExpr,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Call {
    function: Box<Expression>,
    params:   Vec<Expression>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Type {
    expr: TypeExpr,
    kind: Kind,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TypeExpr {
    Array(ArrayTypeExpr),
    DataType(DataTypeTypeExpr),
    FieldConst(String),
    Slice(SliceTypeExpr),
    TypeVariable(String),
    UConst(u64),
    Unit,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DataTypeTypeExpr {
    name:     String,
    generics: Vec<Type>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SliceTypeExpr {
    elem_type: Box<TypeExpr>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ArrayTypeExpr {
    elem_type: Box<TypeExpr>,
    len:       Box<TypeExpr>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Kind {
    Field,
    Type,
    U(u64),
}
