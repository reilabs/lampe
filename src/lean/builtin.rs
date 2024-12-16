use noirc_frontend::{
    ast::BinaryOpKind,
    ast::{IntegerBitSize, UnaryOp},
    hir_def::function::FuncMeta,
    macros_api::Signedness,
    Type,
};

use itertools::Itertools;

pub const INDEX_BUILTIN_NAME: &str = "index";
pub const ZEROED_BUILTIN_NAME: &str = "zeroed";
pub const NEG_BUILTIN_NAME: &str = "neg";
pub const NOT_BUILTIN_NAME: &str = "not";
pub const ADD_BUILTIN_NAME: &str = "add";
pub const SUB_BUILTIN_NAME: &str = "sub";
pub const MUL_BUILTIN_NAME: &str = "mul";
pub const DIV_BUILTIN_NAME: &str = "div";
pub const MOD_BUILTIN_NAME: &str = "rem";
pub const EQ_BUILTIN_NAME: &str = "eq";
pub const NEQ_BUILTIN_NAME: &str = "neq";
pub const GT_BUILTIN_NAME: &str = "gt";
pub const LT_BUILTIN_NAME: &str = "lt";
pub const GEQ_BUILTIN_NAME: &str = "geq";
pub const LEQ_BUILTIN_NAME: &str = "leq";
pub const AND_BUILTIN_NAME: &str = "and";
pub const OR_BUILTIN_NAME: &str = "or";
pub const XOR_BUILTIN_NAME: &str = "xor";
pub const SHL_BUILTIN_NAME: &str = "shl";
pub const SHR_BUILTIN_NAME: &str = "shr";

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
            _ => Err(format!("unknown builtin type `{:?}`", self)),
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

pub fn try_func_into_builtin(func_name: &str, func_meta: &FuncMeta) -> Option<String> {
    let param_types: Result<Vec<BuiltinType>, _> = func_meta
        .parameters
        .0
        .iter()
        .map(|(_, ty, _)| ty.clone().try_into())
        .try_collect();
    let param_types = param_types.ok()?;
    match (func_name, param_types.as_slice()) {
        ("zeroed", _) => Some(ZEROED_BUILTIN_NAME.into()),
        _ => None,
    }
}

pub fn try_prefix_into_builtin(op: UnaryOp, rhs_type: BuiltinType) -> Option<String> {
    match op {
        UnaryOp::Minus if rhs_type.is_arithmetic() => Some(NEG_BUILTIN_NAME.into()),
        UnaryOp::Not if rhs_type.is_bitwise() => Some(NOT_BUILTIN_NAME.into()),
        UnaryOp::MutableReference => todo!(),
        UnaryOp::Dereference { .. } => todo!(),
        _ => None,
    }
}

pub fn try_infix_into_builtin(
    op: BinaryOpKind,
    lhs_type: BuiltinType,
    rhs_type: BuiltinType,
) -> Option<String> {
    if lhs_type != rhs_type {
        return None;
    }
    match op {
        // Arithmetic
        BinaryOpKind::Add if lhs_type.is_arithmetic() => Some(ADD_BUILTIN_NAME.into()),
        BinaryOpKind::Subtract if lhs_type.is_arithmetic() => Some(SUB_BUILTIN_NAME.into()),
        BinaryOpKind::Divide if lhs_type.is_arithmetic() => Some(DIV_BUILTIN_NAME.into()),
        BinaryOpKind::Multiply if lhs_type.is_arithmetic() => Some(MUL_BUILTIN_NAME.into()),
        BinaryOpKind::Modulo if lhs_type.is_arithmetic() => Some(MOD_BUILTIN_NAME.into()),
        // Cmp
        BinaryOpKind::Equal => Some(EQ_BUILTIN_NAME.into()),
        BinaryOpKind::NotEqual => Some(NEQ_BUILTIN_NAME.into()),
        BinaryOpKind::Greater if lhs_type.is_arithmetic() => Some(GT_BUILTIN_NAME.into()),
        BinaryOpKind::GreaterEqual if lhs_type.is_arithmetic() => Some(GEQ_BUILTIN_NAME.into()),
        BinaryOpKind::Less if lhs_type.is_arithmetic() => Some(LT_BUILTIN_NAME.into()),
        BinaryOpKind::LessEqual if lhs_type.is_arithmetic() => Some(LEQ_BUILTIN_NAME.into()),
        // Bit
        BinaryOpKind::And if lhs_type.is_bitwise() => Some(AND_BUILTIN_NAME.into()),
        BinaryOpKind::Or if lhs_type.is_bitwise() => Some(OR_BUILTIN_NAME.into()),
        BinaryOpKind::Xor if lhs_type.is_bitwise() => Some(XOR_BUILTIN_NAME.into()),
        BinaryOpKind::ShiftLeft if lhs_type.is_bitwise() => Some(SHL_BUILTIN_NAME.into()),
        BinaryOpKind::ShiftRight if lhs_type.is_bitwise() => Some(SHR_BUILTIN_NAME.into()),
        _ => None,
    }
}
