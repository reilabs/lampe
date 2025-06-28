use noirc_frontend::{
    ast::{BinaryOpKind, IntegerBitSize, UnaryOp},
    shared::Signedness,
    Type,
    TypeBinding,
};

pub type  BuiltinName = String;

pub const CAST_BUILTIN_NAME: &str = "cast";
pub const ASSERT_BUILTIN_NAME: &str = "assert";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BuiltinType {
    Field,
    Uint(u8),
    Int(u8),
    BigInt,
    Bool,
    Unit,
    Array,
    Slice,
    String,
}

const fn integer_bit_size_to_u8(s: IntegerBitSize) -> u8 {
    match s {
        IntegerBitSize::One => 1,
        IntegerBitSize::Eight => 8,
        IntegerBitSize::Sixteen => 16,
        IntegerBitSize::ThirtyTwo => 32,
        IntegerBitSize::SixtyFour => 64,
        IntegerBitSize::HundredTwentyEight => 128,
    }
}

impl TryInto<BuiltinType> for Type {
    type Error = String;

    fn try_into(self) -> Result<BuiltinType, String> {
        match self {
            Type::FieldElement => Ok(BuiltinType::Field),
            Type::Bool => Ok(BuiltinType::Bool),
            Type::Unit => Ok(BuiltinType::Unit),
            Type::Integer(Signedness::Signed, s) => Ok(BuiltinType::Int(integer_bit_size_to_u8(s))),
            Type::Integer(Signedness::Unsigned, s) => {
                Ok(BuiltinType::Uint(integer_bit_size_to_u8(s)))
            }
            Type::Array(..) => Ok(BuiltinType::Array),
            Type::Slice(_) => Ok(BuiltinType::Slice),
            Type::String(_) => Ok(BuiltinType::String),
            Type::TypeVariable(tv) => match &*tv.borrow() {
                TypeBinding::Bound(ty) => TryInto::<BuiltinType>::try_into(ty.clone()),
                TypeBinding::Unbound(..) => Err(format!("unbound type variable `{tv:?}`")),
            },
            _ => Err(format!("unknown builtin type `{self:?}`")),
        }
    }
}

impl BuiltinType {
    fn is_arithmetic(self) -> bool {
        matches!(
            self,
            BuiltinType::Field | BuiltinType::Uint(_) | BuiltinType::Int(_) | BuiltinType::BigInt
        )
    }

    fn is_bitwise(self) -> bool {
        matches!(
            self,
            BuiltinType::Bool | BuiltinType::Uint(_) | BuiltinType::Int(_)
        )
    }

    fn is_collection(self) -> bool {
        matches!(self, BuiltinType::Array | BuiltinType::Slice)
    }

    fn name_prefix(self) -> String {
        match self {
            BuiltinType::Field => "f".to_string(),
            BuiltinType::Uint(_) => "u".to_string(),
            BuiltinType::Int(_) => "i".to_string(),
            BuiltinType::BigInt => "bigInt".to_string(),
            BuiltinType::Bool => "b".to_string(),
            BuiltinType::Unit => "unit".to_string(),
            BuiltinType::Array => "array".to_string(),
            BuiltinType::Slice => "slice".to_string(),
            BuiltinType::String => "str".to_string(),
        }
    }
}

pub fn try_func_expr_into_builtin_name(func_expr: &str) -> Option<BuiltinName> {
    let builtin_names = [
        ("@std::slice::len", "sliceLen"),
        ("@std::slice::push_back", "slicePushBack"),
        ("@std::slice::push_front", "slicePushFront"),
        ("@std::slice::pop_back", "slicePopBack"),
        ("@std::slice::pop_front", "slicePopFront"),
        ("@std::array::len", "arrayLen"),
        ("@std::array::as_slice", "arrayAsSlice"),
        ("@std::mem::zeroed", "zeroed"),
    ];
    for (prefix, builtin) in builtin_names {
        if func_expr.starts_with(prefix) {
            return Some(builtin.to_string());
        }
    }
    None
}

pub fn get_index_builtin_name(coll_type: BuiltinType) -> Option<BuiltinName> {
    if coll_type.is_collection() {
        let ty_name = coll_type.name_prefix();
        Some(format!("{ty_name}Index"))
    } else {
        None
    }
}

pub fn try_prefix_into_builtin_name(
    op: UnaryOp,
    // `None` if the type is not a builtin type.
    rhs_type: Option<BuiltinType>,
) -> Option<BuiltinName> {
    let rhs_ty_prefix = rhs_type.map(|ty| (ty, ty.name_prefix()));
    match (op, rhs_ty_prefix) {
        (UnaryOp::Minus, Some((rhs_type, prefix))) if rhs_type.is_arithmetic() => {
            Some(format!("{prefix}Neg"))
        }
        (UnaryOp::Not, Some((rhs_type, prefix))) if rhs_type.is_bitwise() => {
            Some(format!("{prefix}Not"))
        }
        (UnaryOp::Reference { .. }, _) => Some("ref".to_string()),
        (UnaryOp::Dereference { .. }, _) => Some("readRef".to_string()),
        _ => None,
    }
}

pub fn try_infix_into_builtin_name(
    op: BinaryOpKind,
    lhs_type: BuiltinType,
    _rhs_type: BuiltinType,
) -> Option<BuiltinName> {
    let ty_name = lhs_type.name_prefix();
    match op {
        // Arithmetic
        BinaryOpKind::Add if lhs_type.is_arithmetic() => Some(format!("{ty_name}Add")),
        BinaryOpKind::Subtract if lhs_type.is_arithmetic() => Some(format!("{ty_name}Sub")),
        BinaryOpKind::Divide if lhs_type.is_arithmetic() => Some(format!("{ty_name}Div")),
        BinaryOpKind::Multiply if lhs_type.is_arithmetic() => Some(format!("{ty_name}Mul")),
        BinaryOpKind::Modulo if lhs_type.is_arithmetic() => Some(format!("{ty_name}Rem")),
        // Cmp
        BinaryOpKind::Equal => Some(format!("{ty_name}Eq")),
        BinaryOpKind::NotEqual => Some(format!("{ty_name}Neq")),
        BinaryOpKind::Greater if lhs_type.is_arithmetic() => Some(format!("{ty_name}Gt")),
        BinaryOpKind::GreaterEqual if lhs_type.is_arithmetic() => Some(format!("{ty_name}Geq")),
        BinaryOpKind::Less if lhs_type.is_arithmetic() => Some(format!("{ty_name}Lt")),
        BinaryOpKind::LessEqual if lhs_type.is_arithmetic() => Some(format!("{ty_name}Leq")),
        // Bit
        BinaryOpKind::And if lhs_type.is_bitwise() => Some(format!("{ty_name}And")),
        BinaryOpKind::Or if lhs_type.is_bitwise() => Some(format!("{ty_name}Or")),
        BinaryOpKind::Xor if lhs_type.is_bitwise() => Some(format!("{ty_name}Xor")),
        BinaryOpKind::ShiftLeft if lhs_type.is_bitwise() => Some(format!("{ty_name}Shl")),
        BinaryOpKind::ShiftRight if lhs_type.is_bitwise() => Some(format!("{ty_name}Shr")),
        _ => None,
    }
}
