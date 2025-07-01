enum Expression {
    IfThenElse(IfThenElse),
    For(For),
    TraitCallRef(TraitCallRef),
    DeclCallRef(DeclCallRef),
}
struct IfThenElse {
    condition:   Box<Expression>,
    then_branch: Box<Expression>,
    else_branch: Option<Box<Expression>>,
}

struct For {
    identifier:  String,
    start_range: Box<Expression>,
    end_range:   Box<Expression>,
    body:        Box<Expression>,
}

struct DeclCallRef {
    function:    String,
    generics:    Vec<Type>,
    param_types: Vec<TyExpr>,
    return_type: TyExpr,
}

struct TraitCallRef {
    trait_name:     String,
    function:       String,
    trait_generics: Vec<Type>,
    fun_generics:   Vec<Type>,
    param_types:    Vec<TyExpr>,
    return_type:    TyExpr,
}

struct Call {
    function: Expression,
    params:   Vec<Expression>,
}

struct Type {
    expr: TyExpr,
    kind: Kind,
}

enum TyExpr {
    UConst(u64),
    FieldConst(String),
    TypeVariable(String),
    Array(TyExpr, TyExpr),
    Slice(TyExpr),
    DataType(String, Vec<Type>),
    Unit,
}

enum Kind {
    Type,
    U(u64),
    Field,
}
