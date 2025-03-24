use std::ops::Deref;

use noirc_frontend::{
    Type, TypeBinding,
    ast::BinaryOpKind,
    ast::{IntegerBitSize, Signedness, UnaryOp},
};

pub type BuiltinName = String;

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
            Type::Array(_, _) => Ok(BuiltinType::Array),
            Type::Slice(_) => Ok(BuiltinType::Slice),
            Type::String(_) => Ok(BuiltinType::String),
            Type::TypeVariable(tv) => match tv.borrow().deref() {
                TypeBinding::Bound(ty) => TryInto::<BuiltinType>::try_into(ty.clone()),
                _ => Err(format!("unbound type variable `{tv:?}`")),
            },
            _ => Err(format!("unknown builtin type `{self:?}`")),
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

    fn is_collection(&self) -> bool {
        match self {
            BuiltinType::Array | BuiltinType::Slice => true,
            _ => false,
        }
    }

    fn name_prefix(&self) -> String {
        match self {
            BuiltinType::Field => format!("f"),
            BuiltinType::Uint(_) => format!("u"),
            BuiltinType::Int(_) => format!("i"),
            BuiltinType::BigInt => format!("bigInt"),
            BuiltinType::Bool => format!("b"),
            BuiltinType::Unit => format!("unit"),
            BuiltinType::Array => format!("array"),
            BuiltinType::Slice => format!("slice"),
            BuiltinType::String => format!("str"),
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
        Some(format!("{}Index", ty_name))
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
            Some(format!("{}Neg", prefix))
        }
        (UnaryOp::Not, Some((rhs_type, prefix))) if rhs_type.is_bitwise() => {
            Some(format!("{}Not", prefix))
        }
        (UnaryOp::MutableReference, _) => Some(format!("ref")),
        (UnaryOp::Dereference { .. }, _) => Some(format!("readRef")),
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
        BinaryOpKind::Add if lhs_type.is_arithmetic() => Some(format!("{}Add", ty_name)),
        BinaryOpKind::Subtract if lhs_type.is_arithmetic() => Some(format!("{}Sub", ty_name)),
        BinaryOpKind::Divide if lhs_type.is_arithmetic() => Some(format!("{}Div", ty_name)),
        BinaryOpKind::Multiply if lhs_type.is_arithmetic() => Some(format!("{}Mul", ty_name)),
        BinaryOpKind::Modulo if lhs_type.is_arithmetic() => Some(format!("{}Rem", ty_name)),
        // Cmp
        BinaryOpKind::Equal => Some(format!("{}Eq", ty_name)),
        BinaryOpKind::NotEqual => Some(format!("{}Neq", ty_name)),
        BinaryOpKind::Greater if lhs_type.is_arithmetic() => Some(format!("{}Gt", ty_name)),
        BinaryOpKind::GreaterEqual if lhs_type.is_arithmetic() => Some(format!("{}Geq", ty_name)),
        BinaryOpKind::Less if lhs_type.is_arithmetic() => Some(format!("{}Lt", ty_name)),
        BinaryOpKind::LessEqual if lhs_type.is_arithmetic() => Some(format!("{}Leq", ty_name)),
        // Bit
        BinaryOpKind::And if lhs_type.is_bitwise() => Some(format!("{}And", ty_name)),
        BinaryOpKind::Or if lhs_type.is_bitwise() => Some(format!("{}Or", ty_name)),
        BinaryOpKind::Xor if lhs_type.is_bitwise() => Some(format!("{}Xor", ty_name)),
        BinaryOpKind::ShiftLeft if lhs_type.is_bitwise() => Some(format!("{}Shl", ty_name)),
        BinaryOpKind::ShiftRight if lhs_type.is_bitwise() => Some(format!("{}Shr", ty_name)),
        _ => None,
    }
}
