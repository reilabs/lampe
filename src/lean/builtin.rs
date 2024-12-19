use std::ops::Deref;

use noirc_frontend::{
    ast::BinaryOpKind,
    ast::{IntegerBitSize, UnaryOp},
    hir_def::function::FuncMeta,
    macros_api::Signedness,
    Type, TypeBinding,
};

use itertools::Itertools;

pub type BuiltinName = String;

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
            Type::TypeVariable(tv, _) => match tv.borrow().deref() {
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

pub fn try_func_into_builtin_name(func_ident: &str, func_meta: &FuncMeta) -> Option<BuiltinName> {
    let param_types: Result<Vec<BuiltinType>, _> = func_meta
        .parameters
        .0
        .iter()
        .map(|(_, ty, _)| ty.clone().try_into())
        .try_collect();
    let param_types = param_types.ok()?;
    match (func_ident, param_types.as_slice()) {
        ("zeroed", _) => Some(format!("zeroed")),
        _ => None,
    }
}

pub fn try_index_into_builtin_name(coll_type: BuiltinType) -> Option<BuiltinName> {
    if coll_type.is_collection() {
        let ty_name = coll_type.name_prefix();
        Some(format!("{}_index", ty_name))
    } else {
        None
    }
}

pub fn try_prefix_into_builtin_name(op: UnaryOp, rhs_type: BuiltinType) -> Option<BuiltinName> {
    let ty_name = rhs_type.name_prefix();
    match op {
        UnaryOp::Minus if rhs_type.is_arithmetic() => Some(format!("{}_neg", ty_name)),
        UnaryOp::Not if rhs_type.is_bitwise() => Some(format!("{}_not", ty_name)),
        UnaryOp::MutableReference => todo!(),
        UnaryOp::Dereference { .. } => todo!(),
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
        BinaryOpKind::Add if lhs_type.is_arithmetic() => Some(format!("{}_add", ty_name)),
        BinaryOpKind::Subtract if lhs_type.is_arithmetic() => Some(format!("{}_sub", ty_name)),
        BinaryOpKind::Divide if lhs_type.is_arithmetic() => Some(format!("{}_div", ty_name)),
        BinaryOpKind::Multiply if lhs_type.is_arithmetic() => Some(format!("{}_mul", ty_name)),
        BinaryOpKind::Modulo if lhs_type.is_arithmetic() => Some(format!("{}_rem", ty_name)),
        // Cmp
        BinaryOpKind::Equal => Some(format!("{}_eq", ty_name)),
        BinaryOpKind::NotEqual => Some(format!("{}_neq", ty_name)),
        BinaryOpKind::Greater if lhs_type.is_arithmetic() => Some(format!("{}_gt", ty_name)),
        BinaryOpKind::GreaterEqual if lhs_type.is_arithmetic() => Some(format!("{}_geq", ty_name)),
        BinaryOpKind::Less if lhs_type.is_arithmetic() => Some(format!("{}_lt", ty_name)),
        BinaryOpKind::LessEqual if lhs_type.is_arithmetic() => Some(format!("{}_leq", ty_name)),
        // Bit
        BinaryOpKind::And if lhs_type.is_bitwise() => Some(format!("{}_and", ty_name)),
        BinaryOpKind::Or if lhs_type.is_bitwise() => Some(format!("{}_or", ty_name)),
        BinaryOpKind::Xor if lhs_type.is_bitwise() => Some(format!("{}_xor", ty_name)),
        BinaryOpKind::ShiftLeft if lhs_type.is_bitwise() => Some(format!("{}_shl", ty_name)),
        BinaryOpKind::ShiftRight if lhs_type.is_bitwise() => Some(format!("{}_shr", ty_name)),
        _ => None,
    }
}
