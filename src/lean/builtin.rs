use noirc_frontend::{
    ast::BinaryOpKind,
    ast::{IntegerBitSize, UnaryOp},
    macros_api::Signedness,
    Type,
};

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
}

const fn integer_bit_size_to_u8(s: IntegerBitSize) -> u8 {
    match s {
        IntegerBitSize::One => 1,
        IntegerBitSize::Eight => 8,
        IntegerBitSize::Sixteen => 16,
        IntegerBitSize::ThirtyTwo => 32,
        IntegerBitSize::SixtyFour => 64,
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
            Type::Array(_, _) => todo!(),
            Type::Slice(_) => todo!(),
            Type::String(_) => todo!(),
            _ => Err(format!("unknown builtin type {self}")),
        }
    }
}

impl BuiltinType {
    fn as_builtin_prefix(&self) -> String {
        match self {
            BuiltinType::Field => format!("f"),
            BuiltinType::Uint(_) => format!("u"),
            BuiltinType::Int(_) => format!("i"),
            BuiltinType::BigInt => format!("bi"),
            BuiltinType::Bool => format!("b"),
            BuiltinType::Unit => format!("unit"),
            BuiltinType::Array => format!("array"),
            BuiltinType::Slice => format!("slice"),
        }
    }

    fn is_arithmetic(&self) -> bool {
        match self {
            BuiltinType::Field
            | BuiltinType::Uint(_)
            | BuiltinType::Int(_)
            | BuiltinType::BigInt => true,
            _ => false,
        }
    }

    fn is_bitwise(&self) -> bool {
        match self {
            BuiltinType::Bool | BuiltinType::Uint(_) | BuiltinType::Int(_) => true,
            _ => false,
        }
    }
}

pub fn try_func_as_builtin(func_name: &str, _param_types: &[BuiltinType]) -> Option<String> {
    match func_name {
        "zeroed" => Some(format!("zeroed")),
        _ => None,
    }
}

pub fn try_prefix_as_builtin(op: UnaryOp, rhs_type: BuiltinType) -> Option<String> {
    let prefix = rhs_type.as_builtin_prefix();
    match op {
        UnaryOp::Minus if rhs_type.is_arithmetic() => Some(format!("{prefix}Neg")),
        UnaryOp::Not if rhs_type.is_bitwise() => Some(format!("{prefix}Not")),
        UnaryOp::MutableReference => todo!(),
        UnaryOp::Dereference { .. } => todo!(),
        _ => None,
    }
}

pub fn try_infix_as_builtin(
    op: BinaryOpKind,
    lhs_type: BuiltinType,
    rhs_type: BuiltinType,
) -> Option<String> {
    if lhs_type != rhs_type {
        return None;
    }
    let prefix = lhs_type.as_builtin_prefix();
    match op {
        // Arithmetic
        BinaryOpKind::Add if lhs_type.is_arithmetic() => Some(format!("{prefix}Add")),
        BinaryOpKind::Subtract if lhs_type.is_arithmetic() => Some(format!("{prefix}Sub")),
        BinaryOpKind::Divide if lhs_type.is_arithmetic() => Some(format!("{prefix}Div")),
        BinaryOpKind::Multiply if lhs_type.is_arithmetic() => Some(format!("{prefix}Mul")),
        BinaryOpKind::Modulo if lhs_type.is_arithmetic() => Some(format!("{prefix}Rem")),
        // Cmp
        BinaryOpKind::Equal => Some(format!("{prefix}Eq")),
        BinaryOpKind::NotEqual => Some(format!("{prefix}Neq")),
        BinaryOpKind::Greater if lhs_type.is_arithmetic() => Some(format!("{prefix}Gt")),
        BinaryOpKind::GreaterEqual if lhs_type.is_arithmetic() => Some(format!("{prefix}Geq")),
        BinaryOpKind::Less if lhs_type.is_arithmetic() => Some(format!("{prefix}Lt")),
        BinaryOpKind::LessEqual if lhs_type.is_arithmetic() => Some(format!("{prefix}Leq")),
        // Bit
        BinaryOpKind::And if lhs_type.is_bitwise() => Some(format!("{prefix}And")),
        BinaryOpKind::Or if lhs_type.is_bitwise() => Some(format!("{prefix}Or")),
        BinaryOpKind::Xor if lhs_type.is_bitwise() => Some(format!("{prefix}Xor")),
        BinaryOpKind::ShiftLeft if lhs_type.is_bitwise() => Some(format!("{prefix}Shl")),
        BinaryOpKind::ShiftRight if lhs_type.is_bitwise() => Some(format!("{prefix}Shr")),
        _ => None,
    }
}
