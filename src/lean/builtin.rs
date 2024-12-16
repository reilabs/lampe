use noirc_frontend::{
    ast::BinaryOpKind,
    ast::{IntegerBitSize, UnaryOp},
    hir_def::function::FuncMeta,
    macros_api::Signedness,
    Type,
};

use itertools::Itertools;

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

pub fn try_func_as_builtin(func_name: &str, func_meta: &FuncMeta) -> Option<String> {
    let param_types: Result<Vec<BuiltinType>, _> = func_meta
        .parameters
        .0
        .iter()
        .map(|(_, ty, _)| ty.clone().try_into())
        .try_collect();
    let param_types = param_types.ok()?;
    match (func_name, param_types.as_slice()) {
        ("zeroed", _) => Some(format!("zeroed")),
        _ => None,
    }
}

pub fn try_prefix_as_builtin(op: UnaryOp, rhs_type: BuiltinType) -> Option<String> {
    match op {
        UnaryOp::Minus if rhs_type.is_arithmetic() => Some(format!("neg")),
        UnaryOp::Not if rhs_type.is_bitwise() => Some(format!("not")),
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
    match op {
        // Arithmetic
        BinaryOpKind::Add if lhs_type.is_arithmetic() => Some(format!("add")),
        BinaryOpKind::Subtract if lhs_type.is_arithmetic() => Some(format!("sub")),
        BinaryOpKind::Divide if lhs_type.is_arithmetic() => Some(format!("div")),
        BinaryOpKind::Multiply if lhs_type.is_arithmetic() => Some(format!("mul")),
        BinaryOpKind::Modulo if lhs_type.is_arithmetic() => Some(format!("rem")),
        // Cmp
        BinaryOpKind::Equal => Some(format!("eq")),
        BinaryOpKind::NotEqual => Some(format!("neq")),
        BinaryOpKind::Greater if lhs_type.is_arithmetic() => Some(format!("gt")),
        BinaryOpKind::GreaterEqual if lhs_type.is_arithmetic() => Some(format!("geq")),
        BinaryOpKind::Less if lhs_type.is_arithmetic() => Some(format!("lt")),
        BinaryOpKind::LessEqual if lhs_type.is_arithmetic() => Some(format!("leq")),
        // Bit
        BinaryOpKind::And if lhs_type.is_bitwise() => Some(format!("and")),
        BinaryOpKind::Or if lhs_type.is_bitwise() => Some(format!("or")),
        BinaryOpKind::Xor if lhs_type.is_bitwise() => Some(format!("xor")),
        BinaryOpKind::ShiftLeft if lhs_type.is_bitwise() => Some(format!("shl")),
        BinaryOpKind::ShiftRight if lhs_type.is_bitwise() => Some(format!("shr")),
        _ => None,
    }
}
