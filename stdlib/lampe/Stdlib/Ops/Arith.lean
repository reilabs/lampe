import «std-1.0.0-beta.12».Extracted
import Init.Data.BitVec.Lemmas
import Lampe
import Stdlib.Convert
import Stdlib.Field
import Stdlib.Integer
import Stdlib.Tuple

namespace Lampe.Stdlib.Ops.Arith

open «std-1.0.0-beta.12»
open Lampe.Stdlib

set_option Lampe.pp.Expr false
set_option Lampe.pp.STHoare false

/-- A shorthand for a call to the `std::ops::arith::Add::add` method. -/
@[reducible]
def add {p}
    (generics : HList Kind.denote «std-1.0.0-beta.12::ops::arith::Add».«#genericKinds»)
    (Self : Tp)
    (associatedTypes : HList Kind.denote «std-1.0.0-beta.12::ops::arith::Add».«#associatedTypesKinds»)
    (fnGenerics : HList Kind.denote «std-1.0.0-beta.12::ops::arith::Add».add.«#genericKinds»)
  : HList (Tp.denote p)
      («std-1.0.0-beta.12::ops::arith::Add».add.«#inputs» generics Self associatedTypes fnGenerics)
  → Expr (Tp.denote p)
      («std-1.0.0-beta.12::ops::arith::Add».add.«#output» generics Self associatedTypes fnGenerics) :=
  «std-1.0.0-beta.12::ops::arith::Add».add generics Self associatedTypes fnGenerics

set_option maxRecDepth 1050 in
theorem field_add_spec {p a b}
  : STHoare p env ⟦⟧
    (add h![] .field h![] h![] h![a, b])
    (fun r => r = a + b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1050 in
theorem u128_add_spec {p a b}
  : STHoare p env ⟦⟧
    (add h![] (.u 128) h![] h![] h![a, b])
    (fun r => r = a + b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1050 in
theorem u64_add_spec {p a b}
  : STHoare p env ⟦⟧
    (add h![] (.u 64) h![] h![] h![a, b])
    (fun r => r = a + b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1050 in
theorem u32_add_spec {p a b}
  : STHoare p env ⟦⟧
    (add h![] (.u 32) h![] h![] h![a, b])
    (fun r => r = a + b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1050 in
theorem u16_add_spec {p a b}
  : STHoare p env ⟦⟧
    (add h![] (.u 16) h![] h![] h![a, b])
    (fun r => r = a + b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1050 in
theorem u8_add_spec {p a b}
  : STHoare p env ⟦⟧
    (add h![] (.u 8) h![] h![] h![a, b])
    (fun r => r = a + b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1050 in
theorem u1_add_spec {p a b}
  : STHoare p env ⟦⟧
    (add h![] (.u 1) h![] h![] h![a, b])
    (fun r => r = a + b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1050 in
theorem i8_add_spec {p a b}
  : STHoare p env ⟦⟧
    (add h![] (.i 8) h![] h![] h![a, b])
    (fun r => r = a + b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1050 in
theorem i16_add_spec {p a b}
  : STHoare p env ⟦⟧
    (add h![] (.i 16) h![] h![] h![a, b])
    (fun r => r = a + b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1050 in
theorem i32_add_spec {p a b}
  : STHoare p env ⟦⟧
    (add h![] (.i 32) h![] h![] h![a, b])
    (fun r => r = a + b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1050 in
theorem i64_add_spec {p a b}
  : STHoare p env ⟦⟧
    (add h![] (.i 32) h![] h![] h![a, b])
    (fun r => r = a + b) := by
  resolve_trait
  steps
  simp_all

/-- A shorthand for a call to the `std::ops::arith::Sub::sub` method. -/
@[reducible]
def sub {p}
    (generics : HList Kind.denote «std-1.0.0-beta.12::ops::arith::Sub».«#genericKinds»)
    (Self : Tp)
    (associatedTypes : HList Kind.denote «std-1.0.0-beta.12::ops::arith::Sub».«#associatedTypesKinds»)
    (fnGenerics : HList Kind.denote «std-1.0.0-beta.12::ops::arith::Sub».sub.«#genericKinds»)
  : HList (Tp.denote p)
      («std-1.0.0-beta.12::ops::arith::Sub».sub.«#inputs» generics Self associatedTypes fnGenerics)
  → Expr (Tp.denote p)
      («std-1.0.0-beta.12::ops::arith::Sub».sub.«#output» generics Self associatedTypes fnGenerics) :=
  «std-1.0.0-beta.12::ops::arith::Sub».sub generics Self associatedTypes fnGenerics

set_option maxRecDepth 1050 in
theorem field_sub_spec {p a b}
  : STHoare p env ⟦⟧
    (sub h![] .field h![] h![] h![a, b])
    (fun r => r = a - b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1050 in
theorem u128_sub_spec {p a b}
  : STHoare p env ⟦⟧
    (sub h![] (.u 128) h![] h![] h![a, b])
    (fun r => r = a - b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1050 in
theorem u64_sub_spec {p a b}
  : STHoare p env ⟦⟧
    (sub h![] (.u 64) h![] h![] h![a, b])
    (fun r => r = a - b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1050 in
theorem u32_sub_spec {p a b}
  : STHoare p env ⟦⟧
    (sub h![] (.u 32) h![] h![] h![a, b])
    (fun r => r = a - b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1100 in
theorem u16_sub_spec {p a b}
  : STHoare p env ⟦⟧
    (sub h![] (.u 16) h![] h![] h![a, b])
    (fun r => r = a - b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1100 in
theorem u8_sub_spec {p a b}
  : STHoare p env ⟦⟧
    (sub h![] (.u 8) h![] h![] h![a, b])
    (fun r => r = a - b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1100 in
theorem u1_sub_spec {p a b}
  : STHoare p env ⟦⟧
    (sub h![] (.u 1) h![] h![] h![a, b])
    (fun r => r = a - b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1100 in
theorem i8_sub_spec {p a b}
  : STHoare p env ⟦⟧
    (sub h![] (.i 8) h![] h![] h![a, b])
    (fun r => r = a - b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1100 in
theorem i16_sub_spec {p a b}
  : STHoare p env ⟦⟧
    (sub h![] (.i 16) h![] h![] h![a, b])
    (fun r => r = a - b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1100 in
theorem i32_sub_spec {p a b}
  : STHoare p env ⟦⟧
    (sub h![] (.i 32) h![] h![] h![a, b])
    (fun r => r = a - b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1100 in
theorem i64_sub_spec {p a b}
  : STHoare p env ⟦⟧
    (sub h![] (.i 32) h![] h![] h![a, b])
    (fun r => r = a - b) := by
  resolve_trait
  steps
  simp_all

/-- A shorthand for a call to the `std::ops::arith::Mul::mul` method. -/
@[reducible]
def mul {p}
    (generics : HList Kind.denote «std-1.0.0-beta.12::ops::arith::Mul».«#genericKinds»)
    (Self : Tp)
    (associatedTypes : HList Kind.denote «std-1.0.0-beta.12::ops::arith::Mul».«#associatedTypesKinds»)
    (fnGenerics : HList Kind.denote «std-1.0.0-beta.12::ops::arith::Mul».mul.«#genericKinds»)
  : HList (Tp.denote p)
      («std-1.0.0-beta.12::ops::arith::Mul».mul.«#inputs» generics Self associatedTypes fnGenerics)
  → Expr (Tp.denote p)
      («std-1.0.0-beta.12::ops::arith::Mul».mul.«#output» generics Self associatedTypes fnGenerics) :=
  «std-1.0.0-beta.12::ops::arith::Mul».mul generics Self associatedTypes fnGenerics

set_option maxRecDepth 1100 in
theorem field_mul_spec {p a b}
  : STHoare p env ⟦⟧
    (mul h![] .field h![] h![] h![a, b])
    (fun r => r = a * b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1150 in
theorem u128_mul_spec {p a b}
  : STHoare p env ⟦⟧
    (mul h![] (.u 128) h![] h![] h![a, b])
    (fun r => r = a * b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1150 in
theorem u64_mul_spec {p a b}
  : STHoare p env ⟦⟧
    (mul h![] (.u 64) h![] h![] h![a, b])
    (fun r => r = a * b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1150 in
theorem u32_mul_spec {p a b}
  : STHoare p env ⟦⟧
    (mul h![] (.u 32) h![] h![] h![a, b])
    (fun r => r = a * b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1100 in
theorem u16_mul_spec {p a b}
  : STHoare p env ⟦⟧
    (mul h![] (.u 16) h![] h![] h![a, b])
    (fun r => r = a * b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1100 in
theorem u8_mul_spec {p a b}
  : STHoare p env ⟦⟧
    (mul h![] (.u 8) h![] h![] h![a, b])
    (fun r => r = a * b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1100 in
theorem u1_mul_spec {p a b}
  : STHoare p env ⟦⟧
    (mul h![] (.u 1) h![] h![] h![a, b])
    (fun r => r = a * b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1100 in
theorem i8_mul_spec {p a b}
  : STHoare p env ⟦⟧
    (mul h![] (.i 8) h![] h![] h![a, b])
    (fun r => r = a * b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1100 in
theorem i16_mul_spec {p a b}
  : STHoare p env ⟦⟧
    (mul h![] (.i 16) h![] h![] h![a, b])
    (fun r => r = a * b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1150 in
theorem i32_mul_spec {p a b}
  : STHoare p env ⟦⟧
    (mul h![] (.i 32) h![] h![] h![a, b])
    (fun r => r = a * b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1150 in
theorem i64_mul_spec {p a b}
  : STHoare p env ⟦⟧
    (mul h![] (.i 32) h![] h![] h![a, b])
    (fun r => r = a * b) := by
  resolve_trait
  steps
  simp_all

/-- A shorthand for a call to the `std::ops::arith::Div::div` method. -/
@[reducible]
def div {p}
    (generics : HList Kind.denote «std-1.0.0-beta.12::ops::arith::Div».«#genericKinds»)
    (Self : Tp)
    (associatedTypes : HList Kind.denote «std-1.0.0-beta.12::ops::arith::Div».«#associatedTypesKinds»)
    (fnGenerics : HList Kind.denote «std-1.0.0-beta.12::ops::arith::Div».div.«#genericKinds»)
  : HList (Tp.denote p)
      («std-1.0.0-beta.12::ops::arith::Div».div.«#inputs» generics Self associatedTypes fnGenerics)
  → Expr (Tp.denote p)
      («std-1.0.0-beta.12::ops::arith::Div».div.«#output» generics Self associatedTypes fnGenerics) :=
  «std-1.0.0-beta.12::ops::arith::Div».div generics Self associatedTypes fnGenerics

set_option maxRecDepth 1150 in
theorem field_div_spec {p a b}
  : STHoare p env ⟦⟧
    (div h![] .field h![] h![] h![a, b])
    (fun r => r = a / b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1150 in
theorem u128_div_spec {p a b}
  : STHoare p env ⟦⟧
    (div h![] (.u 128) h![] h![] h![a, b])
    (fun r => r = a / b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1150 in
theorem u64_div_spec {p a b}
  : STHoare p env ⟦⟧
    (div h![] (.u 64) h![] h![] h![a, b])
    (fun r => r = a / b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1150 in
theorem u32_div_spec {p a b}
  : STHoare p env ⟦⟧
    (div h![] (.u 32) h![] h![] h![a, b])
    (fun r => r = a / b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1200 in
theorem u16_div_spec {p a b}
  : STHoare p env ⟦⟧
    (div h![] (.u 16) h![] h![] h![a, b])
    (fun r => r = a / b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1200 in
theorem u8_div_spec {p a b}
  : STHoare p env ⟦⟧
    (div h![] (.u 8) h![] h![] h![a, b])
    (fun r => r = a / b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1200 in
theorem u1_div_spec {p a b}
  : STHoare p env ⟦⟧
    (div h![] (.u 1) h![] h![] h![a, b])
    (fun r => r = a / b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1200 in
theorem i8_div_spec {p a b}
  : STHoare p env ⟦⟧
    (div h![] (.i 8) h![] h![] h![a, b])
    (fun r => r = a.sdiv b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1200 in
theorem i16_div_spec {p a b}
  : STHoare p env ⟦⟧
    (div h![] (.i 16) h![] h![] h![a, b])
    (fun r => r = a.sdiv b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1200 in
theorem i32_div_spec {p a b}
  : STHoare p env ⟦⟧
    (div h![] (.i 32) h![] h![] h![a, b])
    (fun r => r = a.sdiv b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1200 in
theorem i64_div_spec {p a b}
  : STHoare p env ⟦⟧
    (div h![] (.i 32) h![] h![] h![a, b])
    (fun r => r = a.sdiv b) := by
  resolve_trait
  steps
  simp_all

/-- A shorthand for a call to the `std::ops::arith::Rem::rem` method. -/
@[reducible]
def rem {p}
    (generics : HList Kind.denote «std-1.0.0-beta.12::ops::arith::Rem».«#genericKinds»)
    (Self : Tp)
    (associatedTypes : HList Kind.denote «std-1.0.0-beta.12::ops::arith::Rem».«#associatedTypesKinds»)
    (fnGenerics : HList Kind.denote «std-1.0.0-beta.12::ops::arith::Rem».rem.«#genericKinds»)
  : HList (Tp.denote p)
      («std-1.0.0-beta.12::ops::arith::Rem».rem.«#inputs» generics Self associatedTypes fnGenerics)
  → Expr (Tp.denote p)
      («std-1.0.0-beta.12::ops::arith::Rem».rem.«#output» generics Self associatedTypes fnGenerics) :=
  «std-1.0.0-beta.12::ops::arith::Rem».rem generics Self associatedTypes fnGenerics

set_option maxRecDepth 1150 in
theorem u128_rem_spec {p a b}
  : STHoare p env ⟦⟧
    (rem h![] (.u 128) h![] h![] h![a, b])
    (fun r => r = a % b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1150 in
theorem u64_rem_spec {p a b}
  : STHoare p env ⟦⟧
    (rem h![] (.u 64) h![] h![] h![a, b])
    (fun r => r = a % b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1150 in
theorem u32_rem_spec {p a b}
  : STHoare p env ⟦⟧
    (rem h![] (.u 32) h![] h![] h![a, b])
    (fun r => r = a % b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1200 in
theorem u16_rem_spec {p a b}
  : STHoare p env ⟦⟧
    (rem h![] (.u 16) h![] h![] h![a, b])
    (fun r => r = a % b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1200 in
theorem u8_rem_spec {p a b}
  : STHoare p env ⟦⟧
    (rem h![] (.u 8) h![] h![] h![a, b])
    (fun r => r = a % b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1200 in
theorem u1_rem_spec {p a b}
  : STHoare p env ⟦⟧
    (rem h![] (.u 1) h![] h![] h![a, b])
    (fun r => r = a % b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1200 in
theorem i8_rem_spec {p a b}
  : STHoare p env ⟦⟧
    (rem h![] (.i 8) h![] h![] h![a, b])
    (fun r => r = Builtin.intRem a b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1200 in
theorem i16_rem_spec {p a b}
  : STHoare p env ⟦⟧
    (rem h![] (.i 16) h![] h![] h![a, b])
    (fun r => r = Builtin.intRem a b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1200 in
theorem i32_rem_spec {p a b}
  : STHoare p env ⟦⟧
    (rem h![] (.i 32) h![] h![] h![a, b])
    (fun r => r = Builtin.intRem a b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1200 in
theorem i64_rem_spec {p a b}
  : STHoare p env ⟦⟧
    (rem h![] (.i 32) h![] h![] h![a, b])
    (fun r => r = Builtin.intRem a b) := by
  resolve_trait
  steps
  simp_all

/-- A shorthand for a call to the `std::ops::arith::Neg::neg` method. -/
@[reducible]
def neg {p}
    (generics : HList Kind.denote «std-1.0.0-beta.12::ops::arith::Neg».«#genericKinds»)
    (Self : Tp)
    (associatedTypes : HList Kind.denote «std-1.0.0-beta.12::ops::arith::Neg».«#associatedTypesKinds»)
    (fnGenerics : HList Kind.denote «std-1.0.0-beta.12::ops::arith::Neg».neg.«#genericKinds»)
  : HList (Tp.denote p)
      («std-1.0.0-beta.12::ops::arith::Neg».neg.«#inputs» generics Self associatedTypes fnGenerics)
  → Expr (Tp.denote p)
      («std-1.0.0-beta.12::ops::arith::Neg».neg.«#output» generics Self associatedTypes fnGenerics) :=
  «std-1.0.0-beta.12::ops::arith::Neg».neg generics Self associatedTypes fnGenerics

set_option maxRecDepth 1200 in
theorem field_neg_spec {p a}
  : STHoare p env ⟦⟧
    (neg h![] .field h![] h![] h![a])
    (fun r => r = -a) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1200 in
theorem i8_neg_spec {p a}
  : STHoare p env ⟦⟧
    (neg h![] (.i 8) h![] h![] h![a])
    (fun r => r = -a) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1200 in
theorem i16_neg_spec {p a}
  : STHoare p env ⟦⟧
    (neg h![] (.i 16) h![] h![] h![a])
    (fun r => r = -a) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1200 in
theorem i32_neg_spec {p a}
  : STHoare p env ⟦⟧
    (neg h![] (.i 32) h![] h![] h![a])
    (fun r => r = -a) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1200 in
theorem i64_neg_spec {p a}
  : STHoare p env ⟦⟧
    (neg h![] (.i 32) h![] h![] h![a])
    (fun r => r = -a) := by
  resolve_trait
  steps
  simp_all

/-- A shorthand for a call to the `std::ops::arith::WrappingAdd::wrapping_add` method. -/
@[reducible]
def wrapping_add {p}
    (generics : HList Kind.denote «std-1.0.0-beta.12::ops::arith::WrappingAdd».«#genericKinds»)
    (Self : Tp)
    (associatedTypes : HList Kind.denote «std-1.0.0-beta.12::ops::arith::WrappingAdd».«#associatedTypesKinds»)
    (fnGenerics : HList Kind.denote «std-1.0.0-beta.12::ops::arith::WrappingAdd».wrapping_add.«#genericKinds»)
  : HList (Tp.denote p)
      («std-1.0.0-beta.12::ops::arith::WrappingAdd».wrapping_add.«#inputs» generics Self associatedTypes fnGenerics)
  → Expr (Tp.denote p)
      («std-1.0.0-beta.12::ops::arith::WrappingAdd».wrapping_add.«#output» generics Self associatedTypes fnGenerics) :=
  «std-1.0.0-beta.12::ops::arith::WrappingAdd».wrapping_add generics Self associatedTypes fnGenerics

set_option maxRecDepth 1200 in
theorem u1_wrapping_add_spec {p a b}
  : STHoare p env ⟦⟧
    (wrapping_add h![] (.u 1) h![] h![] h![a, b])
    (fun r => r = a + b) := by
  resolve_trait
  steps
  subst_vars
  simp only [BitVec.xor_eq]
  rw [←BitVec.add_eq_xor]

set_option maxRecDepth 1200 in
theorem u8_wrapping_add_spec {p a b}
    [gt : Prime.BitsGT p 9]
  : STHoare p env ⟦⟧
    (wrapping_add h![] (.u 8) h![] h![] h![a, b])
    (fun r => r = a + b) := by
  resolve_trait
  steps
  enter_decl
  steps [Convert.as_field_for_u8_spec, Convert.as_u8_for_field_spec]
  simp_all only [Builtin.instCastTpFieldU, BitVec.natCast_eq_ofNat, Builtin.instCastTpUField,
    BitVec.add_def]
  congr 1
  norm_cast

  have : BitVec.toNat a + BitVec.toNat b < 2^9 := by
    have : BitVec.toNat a < 2^8 := by apply BitVec.toNat_lt_twoPow_of_le (by linarith)
    have : BitVec.toNat b < 2^8 := by apply BitVec.toNat_lt_twoPow_of_le (by linarith)
    linarith

  have : BitVec.toNat a + BitVec.toNat b < p.natVal := by linarith [gt.lt_prime]

  conv_lhs => rw [ZMod.val_natCast_of_lt (by linarith)]

set_option maxRecDepth 1200 in
theorem u16_wrapping_add_spec {p a b}
    [gt : Prime.BitsGT p 17]
  : STHoare p env ⟦⟧
    (wrapping_add h![] (.u 16) h![] h![] h![a, b])
    (fun r => r = a + b) := by
  resolve_trait
  steps
  enter_decl
  steps [Convert.as_field_for_u16_spec, Convert.as_u16_for_field_spec]
  simp_all only [Builtin.instCastTpFieldU, BitVec.natCast_eq_ofNat, Builtin.instCastTpUField,
    BitVec.add_def]
  congr 1
  norm_cast

  have : BitVec.toNat a + BitVec.toNat b < 2^17 := by
    have : BitVec.toNat a < 2^16 := by apply BitVec.toNat_lt_twoPow_of_le (by linarith)
    have : BitVec.toNat b < 2^16 := by apply BitVec.toNat_lt_twoPow_of_le (by linarith)
    linarith

  have : BitVec.toNat a + BitVec.toNat b < p.natVal := by linarith [gt.lt_prime]

  conv_lhs => rw [ZMod.val_natCast_of_lt (by linarith)]

set_option maxRecDepth 1200 in
theorem u32_wrapping_add_spec {p a b}
    [gt : Prime.BitsGT p 33]
  : STHoare p env ⟦⟧
    (wrapping_add h![] (.u 32) h![] h![] h![a, b])
    (fun r => r = a + b) := by
  resolve_trait
  steps
  enter_decl
  steps [Convert.as_field_for_u32_spec, Convert.as_u32_for_field_spec]
  simp_all only [Builtin.instCastTpFieldU, BitVec.natCast_eq_ofNat, Builtin.instCastTpUField,
    BitVec.add_def]
  congr 1
  norm_cast

  have : BitVec.toNat a + BitVec.toNat b < 2^33 := by
    have : BitVec.toNat a < 2^32 := by apply BitVec.toNat_lt_twoPow_of_le (by linarith)
    have : BitVec.toNat b < 2^32 := by apply BitVec.toNat_lt_twoPow_of_le (by linarith)
    linarith

  have : BitVec.toNat a + BitVec.toNat b < p.natVal := by linarith [gt.lt_prime]

  conv_lhs => rw [ZMod.val_natCast_of_lt (by linarith)]

set_option maxRecDepth 1200 in
theorem u64_wrapping_add_spec {p a b}
    [gt : Prime.BitsGT p 65]
  : STHoare p env ⟦⟧
    (wrapping_add h![] (.u 64) h![] h![] h![a, b])
    (fun r => r = a + b) := by
  resolve_trait
  steps
  enter_decl
  steps [Convert.as_field_for_u64_spec, Convert.as_u64_for_field_spec]
  simp_all only [Builtin.instCastTpFieldU, BitVec.natCast_eq_ofNat, Builtin.instCastTpUField,
    BitVec.add_def]
  congr 1
  norm_cast

  have : BitVec.toNat a + BitVec.toNat b < 2^65 := by
    have : BitVec.toNat a < 2^64 := by apply BitVec.toNat_lt_twoPow_of_le (by linarith)
    have : BitVec.toNat b < 2^64 := by apply BitVec.toNat_lt_twoPow_of_le (by linarith)
    linarith

  have : BitVec.toNat a + BitVec.toNat b < p.natVal := by linarith [gt.lt_prime]

  conv_lhs => rw [ZMod.val_natCast_of_lt (by linarith)]

set_option maxRecDepth 1200 in
theorem u128_wrapping_add_spec {p a b}
    [gt : Prime.BitsGT p 129]
  : STHoare p env ⟦⟧
    (wrapping_add h![] (.u 128) h![] h![] h![a, b])
    (fun r => r = a + b) := by
  resolve_trait
  steps
  enter_decl
  steps [Convert.as_field_for_u128_spec, Convert.as_u128_for_field_spec]
  simp_all only [Builtin.instCastTpFieldU, BitVec.natCast_eq_ofNat, Builtin.instCastTpUField,
    BitVec.add_def]
  congr 1
  norm_cast

  have : BitVec.toNat a + BitVec.toNat b < 2^129 := by
    have : BitVec.toNat a < 2^128 := by apply BitVec.toNat_lt_twoPow_of_le (by linarith)
    have : BitVec.toNat b < 2^128 := by apply BitVec.toNat_lt_twoPow_of_le (by linarith)
    linarith

  have : BitVec.toNat a + BitVec.toNat b < p.natVal := by linarith [gt.lt_prime]

  conv_lhs => rw [ZMod.val_natCast_of_lt (by linarith)]

set_option maxRecDepth 1250 in
theorem i8_wrapping_add_spec {p a b}
    [gt : Prime.BitsGT p 9]
  : STHoare p env ⟦⟧
    (wrapping_add h![] (.i 8) h![] h![] h![a, b])
    (fun r => r = a + b) := by
  resolve_trait
  steps [u8_wrapping_add_spec (p := p)]
  simp_all

set_option maxRecDepth 1250 in
theorem i16_wrapping_add_spec {p a b}
    [gt : Prime.BitsGT p 17]
  : STHoare p env ⟦⟧
    (wrapping_add h![] (.i 16) h![] h![] h![a, b])
    (fun r => r = a + b) := by
  resolve_trait
  steps [u16_wrapping_add_spec (p := p)]
  simp_all

set_option maxRecDepth 1250 in
theorem i32_wrapping_add_spec {p a b}
    [gt : Prime.BitsGT p 33]
  : STHoare p env ⟦⟧
    (wrapping_add h![] (.i 32) h![] h![] h![a, b])
    (fun r => r = a + b) := by
  resolve_trait
  steps [u32_wrapping_add_spec (p := p)]
  simp_all

set_option maxRecDepth 1250 in
theorem i64_wrapping_add_spec {p a b}
    [gt : Prime.BitsGT p 65]
  : STHoare p env ⟦⟧
    (wrapping_add h![] (.i 64) h![] h![] h![a, b])
    (fun r => r = a + b) := by
  resolve_trait
  steps [u64_wrapping_add_spec (p := p)]
  simp_all

set_option maxRecDepth 1250 in
theorem field_wrapping_add_spec {p a b}
  : STHoare p env ⟦⟧
    (wrapping_add h![] .field h![] h![] h![a, b])
    (fun r => r = a + b) := by
  resolve_trait
  steps
  simp_all

/-- A shorthand for a call to the `std::ops::arith::WrappingSub::wrapping_sub` method. -/
@[reducible]
def wrapping_sub {p}
    (generics : HList Kind.denote «std-1.0.0-beta.12::ops::arith::WrappingSub».«#genericKinds»)
    (Self : Tp)
    (associatedTypes : HList Kind.denote «std-1.0.0-beta.12::ops::arith::WrappingSub».«#associatedTypesKinds»)
    (fnGenerics : HList Kind.denote «std-1.0.0-beta.12::ops::arith::WrappingSub».wrapping_sub.«#genericKinds»)
  : HList (Tp.denote p)
      («std-1.0.0-beta.12::ops::arith::WrappingSub».wrapping_sub.«#inputs» generics Self associatedTypes fnGenerics)
  → Expr (Tp.denote p)
      («std-1.0.0-beta.12::ops::arith::WrappingSub».wrapping_sub.«#output» generics Self associatedTypes fnGenerics) :=
  «std-1.0.0-beta.12::ops::arith::WrappingSub».wrapping_sub generics Self associatedTypes fnGenerics

set_option maxRecDepth 1250 in
theorem u1_wrapping_sub_spec {p a b}
  : STHoare p env ⟦⟧
    (wrapping_sub h![] (.u 1) h![] h![] h![a, b])
    (fun r => r = a - b) := by
  resolve_trait
  steps
  subst_vars
  simp only [BitVec.xor_eq]
  rw [←BitVec.sub_eq_xor]

set_option maxRecDepth 1250 in
theorem u8_wrapping_sub_spec {p a b}
    [gt : Prime.BitsGT p 129]
  : STHoare p env ⟦⟧
    (wrapping_sub h![] (.u 8) h![] h![] h![a, b])
    (fun r => r = a - b) := by
  resolve_trait
  steps
  step_as (⟦⟧) (fun (r : Tp.field.denote p) => r = a.toNat + 2^128 - b.toNat)
  · enter_decl
    steps [Convert.as_field_for_u8_spec]
    rename_i a
    simp only [Builtin.instCastTpUField, Int.cast_ofNat] at a
    norm_num
    simp_all

  steps
  simp_all only [Builtin.instCastTpFieldU, BitVec.natCast_eq_ofNat, BitVec.sub_def, Nat.reducePow]
  conv => {lhs; enter [2, 1]; lhs; norm_cast}

  have a_lt : BitVec.toNat a < 2^128 := by apply BitVec.toNat_lt_twoPow_of_le (by linarith)
  have a_add_lt_p : BitVec.toNat a + 2^128 < p.natVal := by linarith [gt.lt_prime]
  have b_inbounds : BitVec.toNat b < 2^8 := by apply BitVec.toNat_lt_twoPow_of_le (by linarith)
  have b_le : BitVec.toNat b ≤ BitVec.toNat a + 2 ^ 128 := by linarith

  rw [ZMod.val_sub]
  · rw [ZMod.val_natCast_of_lt a_add_lt_p]
    rw [ZMod.val_natCast_of_lt (by linarith)]

    rw [←Integer.BitVec.ofNat_sub_ofNat_of_le (hy := b_inbounds) (hlt := b_le)]
    repeat rw [BitVec.ofNat_add]
    rw [←Integer.BitVec.ofNat_sub_ofNat_of_le (hy := b_inbounds) (hlt := by linarith)]
    simp_all only [Nat.reducePow, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.reduceOfNat,
      BitVec.add_zero, BitVec.zero_sub]
    rw [←BitVec.add_neg_eq_sub]
    rw [BitVec.add_comm]

  repeat rw [ZMod.val_natCast_of_lt (by linarith)]
  linarith

set_option maxRecDepth 1250 in
theorem u16_wrapping_sub_spec {p a b}
    [gt : Prime.BitsGT p 129]
  : STHoare p env ⟦⟧
    (wrapping_sub h![] (.u 16) h![] h![] h![a, b])
    (fun r => r = a - b) := by
  resolve_trait
  steps
  step_as (⟦⟧) (fun (r : Tp.field.denote p) => r = a.toNat + 2^128 - b.toNat)
  · enter_decl
    steps [Convert.as_field_for_u16_spec]
    rename_i a
    simp only [Builtin.instCastTpUField, Int.cast_ofNat] at a
    norm_num
    simp_all

  steps
  simp_all only [Builtin.instCastTpFieldU, BitVec.natCast_eq_ofNat, BitVec.sub_def, Nat.reducePow]
  conv => {lhs; enter [2, 1]; lhs; norm_cast}

  have a_lt : BitVec.toNat a < 2^128 := by apply BitVec.toNat_lt_twoPow_of_le (by linarith)
  have a_add_lt_p : BitVec.toNat a + 2^128 < p.natVal := by linarith [gt.lt_prime]
  have b_inbounds : BitVec.toNat b < 2^16 := by apply BitVec.toNat_lt_twoPow_of_le (by linarith)
  have b_le : BitVec.toNat b ≤ BitVec.toNat a + 2 ^ 128 := by linarith

  rw [ZMod.val_sub]
  · rw [ZMod.val_natCast_of_lt a_add_lt_p]
    rw [ZMod.val_natCast_of_lt (by linarith)]

    rw [←Integer.BitVec.ofNat_sub_ofNat_of_le (hy := b_inbounds) (hlt := b_le)]
    repeat rw [BitVec.ofNat_add]
    rw [←Integer.BitVec.ofNat_sub_ofNat_of_le (hy := b_inbounds) (hlt := by linarith)]
    simp_all only [Nat.reducePow, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.reduceOfNat,
      BitVec.add_zero, BitVec.zero_sub]
    rw [←BitVec.add_neg_eq_sub]
    rw [BitVec.add_comm]

  repeat rw [ZMod.val_natCast_of_lt (by linarith)]
  linarith

set_option maxRecDepth 1250 in
theorem u32_wrapping_sub_spec {p a b}
    [gt : Prime.BitsGT p 129]
  : STHoare p env ⟦⟧
    (wrapping_sub h![] (.u 32) h![] h![] h![a, b])
    (fun r => r = a - b) := by
  resolve_trait
  steps
  step_as (⟦⟧) (fun (r : Tp.field.denote p) => r = a.toNat + 2^128 - b.toNat)
  · enter_decl
    steps [Convert.as_field_for_u32_spec]
    rename_i a
    simp only [Builtin.instCastTpUField, Int.cast_ofNat] at a
    norm_num
    simp_all

  steps
  simp_all only [Builtin.instCastTpFieldU, BitVec.natCast_eq_ofNat, BitVec.sub_def, Nat.reducePow]
  conv => {lhs; enter [2, 1]; lhs; norm_cast}

  have a_lt : BitVec.toNat a < 2^128 := by apply BitVec.toNat_lt_twoPow_of_le (by linarith)
  have a_add_lt_p : BitVec.toNat a + 2^128 < p.natVal := by linarith [gt.lt_prime]
  have b_inbounds : BitVec.toNat b < 2^32 := by apply BitVec.toNat_lt_twoPow_of_le (by linarith)
  have b_le : BitVec.toNat b ≤ BitVec.toNat a + 2 ^ 128 := by linarith

  rw [ZMod.val_sub]
  · rw [ZMod.val_natCast_of_lt a_add_lt_p]
    rw [ZMod.val_natCast_of_lt (by linarith)]

    rw [←Integer.BitVec.ofNat_sub_ofNat_of_le (hy := b_inbounds) (hlt := b_le)]
    repeat rw [BitVec.ofNat_add]
    rw [←Integer.BitVec.ofNat_sub_ofNat_of_le (hy := b_inbounds) (hlt := by linarith)]
    simp_all only [Nat.reducePow, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.reduceOfNat,
      BitVec.add_zero, BitVec.zero_sub]
    rw [←BitVec.add_neg_eq_sub]
    rw [BitVec.add_comm]

  repeat rw [ZMod.val_natCast_of_lt (by linarith)]
  linarith

set_option maxRecDepth 1250 in
theorem u64_wrapping_sub_spec {p a b}
    [gt : Prime.BitsGT p 129]
  : STHoare p env ⟦⟧
    (wrapping_sub h![] (.u 64) h![] h![] h![a, b])
    (fun r => r = a - b) := by
  resolve_trait
  steps
  step_as (⟦⟧) (fun (r : Tp.field.denote p) => r = a.toNat + 2^128 - b.toNat)
  · enter_decl
    steps [Convert.as_field_for_u64_spec]
    rename_i a
    simp only [Builtin.instCastTpUField, Int.cast_ofNat] at a
    norm_num
    simp_all

  steps
  simp_all only [Builtin.instCastTpFieldU, BitVec.natCast_eq_ofNat, BitVec.sub_def, Nat.reducePow]
  conv => {lhs; enter [2, 1]; lhs; norm_cast}

  have a_lt : BitVec.toNat a < 2^128 := by apply BitVec.toNat_lt_twoPow_of_le (by linarith)
  have a_add_lt_p : BitVec.toNat a + 2^128 < p.natVal := by linarith [gt.lt_prime]
  have b_inbounds : BitVec.toNat b < 2^64 := by apply BitVec.toNat_lt_twoPow_of_le (by linarith)
  have b_le : BitVec.toNat b ≤ BitVec.toNat a + 2 ^ 128 := by linarith

  rw [ZMod.val_sub]
  · rw [ZMod.val_natCast_of_lt a_add_lt_p]
    rw [ZMod.val_natCast_of_lt (by linarith)]

    rw [←Integer.BitVec.ofNat_sub_ofNat_of_le (hy := b_inbounds) (hlt := b_le)]
    repeat rw [BitVec.ofNat_add]
    rw [←Integer.BitVec.ofNat_sub_ofNat_of_le (hy := b_inbounds) (hlt := by linarith)]
    simp_all only [Nat.reducePow, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.reduceOfNat,
      BitVec.add_zero, BitVec.zero_sub]
    rw [←BitVec.add_neg_eq_sub]
    rw [BitVec.add_comm]

  repeat rw [ZMod.val_natCast_of_lt (by linarith)]
  linarith

set_option maxRecDepth 1250 in
theorem u128_wrapping_sub_spec {p a b}
    [gt : Prime.BitsGT p 129]
  : STHoare p env ⟦⟧
    (wrapping_sub h![] (.u 128) h![] h![] h![a, b])
    (fun r => r = a - b) := by
  resolve_trait
  steps
  step_as (⟦⟧) (fun (r : Tp.field.denote p) => r = a.toNat + 2^128 - b.toNat)
  · enter_decl
    steps [Convert.as_field_for_u128_spec]
    rename_i a
    simp only [Builtin.instCastTpUField, Int.cast_ofNat] at a
    norm_num
    simp_all

  steps
  simp_all only [Builtin.instCastTpFieldU, BitVec.natCast_eq_ofNat, BitVec.sub_def, Nat.reducePow]
  conv => {lhs; enter [2, 1]; lhs; norm_cast}

  have a_lt : BitVec.toNat a < 2^128 := by apply BitVec.toNat_lt_twoPow_of_le (by linarith)
  have a_add_lt_p : BitVec.toNat a + 2^128 < p.natVal := by linarith [gt.lt_prime]
  have b_inbounds : BitVec.toNat b < 2^128 := by apply BitVec.toNat_lt_twoPow_of_le (by linarith)
  have b_le : BitVec.toNat b ≤ BitVec.toNat a + 2 ^ 128 := by linarith

  rw [ZMod.val_sub]
  · rw [ZMod.val_natCast_of_lt a_add_lt_p]
    rw [ZMod.val_natCast_of_lt (by linarith)]

    rw [←Integer.BitVec.ofNat_sub_ofNat_of_le (hy := b_inbounds) (hlt := b_le)]
    repeat rw [BitVec.ofNat_add]
    rw [←Integer.BitVec.ofNat_sub_ofNat_of_le (hy := b_inbounds) (hlt := by linarith)]
    simp_all only [Nat.reducePow, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.reduceOfNat,
      BitVec.add_zero, BitVec.zero_sub]
    rw [←BitVec.add_neg_eq_sub]
    rw [BitVec.add_comm]

  repeat rw [ZMod.val_natCast_of_lt (by linarith)]
  linarith

set_option maxRecDepth 1250 in
theorem i8_wrapping_sub_spec {p a b}
    [gt : Prime.BitsGT p 129]
  : STHoare p env ⟦⟧
    (wrapping_sub h![] (.i 8) h![] h![] h![a, b])
    (fun r => r = a - b) := by
  resolve_trait
  steps [u8_wrapping_sub_spec (p := p)]
  simp_all

set_option maxRecDepth 1250 in
theorem i16_wrapping_sub_spec {p a b}
    [gt : Prime.BitsGT p 129]
  : STHoare p env ⟦⟧
    (wrapping_sub h![] (.i 16) h![] h![] h![a, b])
    (fun r => r = a - b) := by
  resolve_trait
  steps [u16_wrapping_sub_spec (p := p)]
  simp_all

set_option maxRecDepth 1250 in
theorem i32_wrapping_sub_spec {p a b}
    [gt : Prime.BitsGT p 129]
  : STHoare p env ⟦⟧
    (wrapping_sub h![] (.i 32) h![] h![] h![a, b])
    (fun r => r = a - b) := by
  resolve_trait
  steps [u32_wrapping_sub_spec (p := p)]
  simp_all

set_option maxRecDepth 1250 in
theorem i64_wrapping_sub_spec {p a b}
    [gt : Prime.BitsGT p 129]
  : STHoare p env ⟦⟧
    (wrapping_sub h![] (.i 64) h![] h![] h![a, b])
    (fun r => r = a - b) := by
  resolve_trait
  steps [u64_wrapping_sub_spec (p := p)]
  simp_all

set_option maxRecDepth 1250 in
theorem field_wrapping_sub_spec {p a b}
  : STHoare p env ⟦⟧
    (wrapping_sub h![] .field h![] h![] h![a, b])
    (fun r => r = a - b) := by
  resolve_trait
  steps
  simp_all

/-- A shorthand for a call to the `std::ops::arith::WrappingMul::wrapping_mul` method. -/
@[reducible]
def wrapping_mul {p}
    (generics : HList Kind.denote «std-1.0.0-beta.12::ops::arith::WrappingMul».«#genericKinds»)
    (Self : Tp)
    (associatedTypes : HList Kind.denote «std-1.0.0-beta.12::ops::arith::WrappingMul».«#associatedTypesKinds»)
    (fnGenerics : HList Kind.denote «std-1.0.0-beta.12::ops::arith::WrappingMul».wrapping_mul.«#genericKinds»)
  : HList (Tp.denote p)
      («std-1.0.0-beta.12::ops::arith::WrappingMul».wrapping_mul.«#inputs» generics Self associatedTypes fnGenerics)
  → Expr (Tp.denote p)
      («std-1.0.0-beta.12::ops::arith::WrappingMul».wrapping_mul.«#output» generics Self associatedTypes fnGenerics) :=
  «std-1.0.0-beta.12::ops::arith::WrappingMul».wrapping_mul generics Self associatedTypes fnGenerics

set_option maxRecDepth 1300 in
theorem u1_wrapping_mul_spec {p a b}
  : STHoare p env ⟦⟧
    (wrapping_mul h![] (.u 1) h![] h![] h![a, b])
    (fun r => r = a * b) := by
  resolve_trait
  steps
  subst_vars
  rw [←BitVec.mul_eq_and]

set_option maxRecDepth 1300 in
theorem u8_wrapping_mul {p a b}
    [gt : Prime.BitsGT p 16]
  : STHoare p env ⟦⟧
    (wrapping_mul h![] (.u 8) h![] h![] h![a, b])
    (fun r => r = a * b) := by
  resolve_trait
  steps
  enter_decl
  steps [Convert.as_field_for_u8_spec, Convert.as_u8_for_field_spec]
  simp_all only [Builtin.instCastTpFieldU, BitVec.natCast_eq_ofNat, Builtin.instCastTpUField]
  norm_cast

  have mul_max : BitVec.toNat a * BitVec.toNat b < 2^16 := by apply BitVec.toNat_mul_toNat_lt
  have mul_lt_p : BitVec.toNat a * BitVec.toNat b < p.natVal := by linarith [gt.lt_prime]

  rw [ZMod.val_natCast_of_lt mul_lt_p]
  simp_all only [Nat.reducePow]
  rfl

set_option maxRecDepth 1300 in
theorem u16_wrapping_mul {p a b}
    [gt : Prime.BitsGT p 32]
  : STHoare p env ⟦⟧
    (wrapping_mul h![] (.u 16) h![] h![] h![a, b])
    (fun r => r = a * b) := by
  resolve_trait
  steps
  enter_decl
  steps [Convert.as_field_for_u16_spec, Convert.as_u16_for_field_spec]
  simp_all only [Builtin.instCastTpFieldU, BitVec.natCast_eq_ofNat, Builtin.instCastTpUField]
  norm_cast

  have mul_max : BitVec.toNat a * BitVec.toNat b < 2^32 := by apply BitVec.toNat_mul_toNat_lt
  have mul_lt_p : BitVec.toNat a * BitVec.toNat b < p.natVal := by linarith [gt.lt_prime]

  rw [ZMod.val_natCast_of_lt mul_lt_p]
  simp_all only [Nat.reducePow]
  rfl

set_option maxRecDepth 1300 in
theorem u32_wrapping_mul {p a b}
    [gt : Prime.BitsGT p 64]
  : STHoare p env ⟦⟧
    (wrapping_mul h![] (.u 32) h![] h![] h![a, b])
    (fun r => r = a * b) := by
  resolve_trait
  steps
  enter_decl
  steps [Convert.as_field_for_u32_spec, Convert.as_u32_for_field_spec]
  simp_all only [Builtin.instCastTpFieldU, BitVec.natCast_eq_ofNat, Builtin.instCastTpUField]
  norm_cast

  have mul_max : BitVec.toNat a * BitVec.toNat b < 2^64 := by apply BitVec.toNat_mul_toNat_lt
  have mul_lt_p : BitVec.toNat a * BitVec.toNat b < p.natVal := by linarith [gt.lt_prime]

  rw [ZMod.val_natCast_of_lt mul_lt_p]
  simp_all only [Nat.reducePow]
  rfl

set_option maxRecDepth 1300 in
theorem u64_wrapping_mul {p a b}
    [gt : Prime.BitsGT p 128]
  : STHoare p env ⟦⟧
    (wrapping_mul h![] (.u 64) h![] h![] h![a, b])
    (fun r => r = a * b) := by
  resolve_trait
  steps
  enter_decl
  steps [Convert.as_field_for_u64_spec, Convert.as_u64_for_field_spec]
  simp_all only [Builtin.instCastTpFieldU, BitVec.natCast_eq_ofNat, Builtin.instCastTpUField]
  norm_cast

  have mul_max : BitVec.toNat a * BitVec.toNat b < 2^128 := by apply BitVec.toNat_mul_toNat_lt
  have mul_lt_p : BitVec.toNat a * BitVec.toNat b < p.natVal := by linarith [gt.lt_prime]

  rw [ZMod.val_natCast_of_lt mul_lt_p]
  simp_all only [Nat.reducePow]
  rfl

theorem two_pow_64_spec {p}
  : STHoare p env ⟦⟧
    («std-1.0.0-beta.12::ops::arith::two_pow_64».call h![] h![])
    (fun r => r = Integer.two_pow_64) := by
  enter_decl
  steps
  unfold Integer.two_pow_64
  norm_cast

theorem split_into_64_bit_limbs_spec {p a} [gt : Prime.BitsGT p 128]
  : STHoare p env ⟦⟧
    («std-1.0.0-beta.12::ops::arith::split_into_64_bit_limbs».call h![] h![a])
    (fun r => r = Integer.split64 a) := by
  enter_decl
  step_as (⟦⟧) (fun _ => ⟦⟧)
  · steps
    enter_decl
    steps

  steps [two_pow_64_spec]
  simp only [Builtin.indexTpl] at *
  simp_all only [Builtin.instCastTpUField, beq_true, decide_eq_true_eq]
  rename_i v _
  change «#v_2» = _

  have : a = Integer.combine64 «#v_2» := by
    apply_fun ZMod.val at v
    have (a : BitVec 128) : a.toNat < p.natVal := Nat.lt_trans a.isLt gt.lt_prime
    have (b : BitVec 64) : b.toNat < p.natVal := by linarith [b.isLt, gt.lt_prime]

    have hm : BitVec.toNat «#v_2».2.1 * Integer.two_pow_64.toNat ≤ 2^128 - 2^64 := by
      have : 2^128 - 2^64 = (2^64 - 1) * 2^64 := by decide
      rw [this]
      apply Nat.mul_le_mul_right
      apply Nat.le_of_lt_succ
      exact BitVec.isLt _

    have ham : BitVec.toNat «#v_2».1 + BitVec.toNat «#v_2».2.1 * Integer.two_pow_64.toNat < 2^128 := by
      have : 2^128 = 2^64 + (2^128 - 2^64) := by decide
      rw [this]
      exact Nat.add_lt_add_of_lt_of_le (BitVec.isLt _) hm

    rw [ZMod.val_natCast_of_lt (by apply_assumption), ZMod.val_add_of_lt] at v
    all_goals rw [ZMod.val_natCast_of_lt (by apply_assumption)] at *
    all_goals rw [ZMod.val_mul_of_lt] at *
    all_goals repeat rw [ZMod.val_natCast_of_lt (by apply_assumption)] at *

    any_goals exact lt_of_le_of_lt hm (lt_trans (by decide) gt.lt_prime)
    any_goals exact lt_trans ham gt.lt_prime

    apply BitVec.eq_of_toNat_eq
    rw [Integer.combine64, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_mul,
      BitVec.toNat_setWidth]
    conv_rhs =>
      arg 1
      repeat rw [Nat.mod_eq_of_lt (Nat.lt_trans (BitVec.isLt _) (by decide))]
      rw [Nat.mod_eq_of_lt (lt_of_le_of_lt hm (by decide))]
    rw [Nat.mod_eq_of_lt ham]
    assumption

  subst this
  rw [Integer.split64_combine64_id]

set_option maxRecDepth 1300 in
theorem u128_wrapping_mul {p a b}
    [gt : Prime.BitsGT p 129]
  : STHoare p env ⟦⟧
    (wrapping_mul h![] (.u 128) h![] h![] h![a, b])
    (fun r => r = a * b) := by
  resolve_trait
  steps
  enter_decl
  steps [split_into_64_bit_limbs_spec (p := p), two_pow_64_spec]

  rename_i v_def
  cases v_def
  have := gt.lt_prime

  rename y_lo = _ => y_lo_def
  rcases y_lo with ⟨y_lo, y_lo_lt⟩
  rename y_hi = _ => y_hi_def
  rcases y_hi with ⟨y_hi, y_hi_lt⟩
  rename x_lo = _ => x_lo_def
  rcases x_lo with ⟨x_lo, x_lo_lt⟩
  rename x_hi = _ => x_hi_def
  rcases x_hi with ⟨x_hi, x_hi_lt⟩

  apply_fun BitVec.toNat at x_lo_def y_lo_def x_hi_def y_hi_def
  simp only [Builtin.instCastTpFieldU, Builtin.instCastTpUField, Builtin.indexTpl,
    Integer.split64_fst_toNat, Integer.split64_snd_toNat, BitVec.toNat_ofFin] at *

  rename low = _ => low_def
  rcases low with ⟨low, low_lt_p⟩
  apply_fun ZMod.val at low_def

  norm_cast at low_def

  rw [ZMod.val_natCast_of_lt ?lt] at low_def
  case lt => exact Nat.lt_trans (Nat.mul_lt_mul'' x_lo_lt y_lo_lt) (lt_trans (by decide) gt.lt_prime)
  simp only [ZMod.val, Prime.natVal] at low_def

  rename lo = _ => lo_def
  rcases lo with ⟨lo, lo_lt_p⟩
  apply_fun ZMod.val at lo_def
  simp only [ZMod.val, Prime.natVal, BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat] at lo_def
  rw [Fin.val_natCast, Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.mod_le _ _) low_lt_p)] at lo_def
  cases lo_def

  rename carry = _ => carry_def
  rcases carry with ⟨carry, carry_lt_p⟩
  apply_fun ZMod.val at carry_def

  rw [Field.val_div_of_dvd ?dvd, ZMod.val_sub ?ltmod] at carry_def
  simp only [ZMod.val, Prime.natVal] at carry_def
  conv_rhs at carry_def =>
    arg 2
    rw [Fin.val_natCast, Nat.mod_eq_of_lt (by apply lt_trans (by decide) (gt.lt_prime))]
    change 2^64

  case ltmod => apply Nat.mod_le
  case dvd =>
    rw [ZMod.val_sub (Nat.mod_le _ _)]
    simp only [ZMod.val, Prime.natVal]
    rw [Fin.val_natCast, Nat.mod_eq_of_lt (by apply lt_trans (by decide) (gt.lt_prime))]
    conv_lhs => change 2^64
    exact Nat.dvd_sub_mod _

  rename high = _ => high_def
  rcases high with ⟨high, high_lt_p⟩
  apply_fun ZMod.val at high_def

  have : x_lo * y_hi + x_hi * y_lo < 2^129 - 2^64 := by
    have t1 : x_lo * y_hi < 2 ^ 128 := by
      conv_rhs => change (2 ^ 64 * 2 ^ 64)
      apply Nat.mul_lt_mul'' <;> assumption
    have t2 : x_hi * y_lo ≤ 2 ^ 128 - 2 ^ 64 := by
      conv_rhs => change (2 ^ 64 * (2^64 - 1))
      apply Nat.mul_le_mul (Nat.le_of_lt x_hi_lt) (Nat.le_pred_of_lt y_lo_lt)
    apply add_lt_add_of_lt_of_le t1 t2

  have tc : carry < 2^64 := by
    cases carry_def
    apply Nat.div_lt_of_lt_mul
    apply Nat.sub_lt_of_lt
    cases low_def
    exact Nat.mul_lt_mul'' x_lo_lt y_lo_lt

  norm_cast at high_def
  rw [ZMod.val_add_of_lt ?lt1, ZMod.val_natCast_of_lt ?lt2] at high_def
  simp only [ZMod.val, Prime.natVal] at high_def

  case lt1 =>
    rw [ZMod.val_natCast_of_lt]
    simp only [ZMod.val, Prime.natVal]
    apply Nat.lt_trans _ (gt.lt_prime)
    apply Nat.add_lt_add this tc
    apply Nat.lt_trans this (lt_trans (by decide) gt.lt_prime)
  case lt2 => exact lt_trans this (lt_trans (by decide) gt.lt_prime)

  rename hi = _ => hi_def
  rcases hi with ⟨hi, hi_lt_p⟩
  apply_fun ZMod.val at hi_def
  simp only [ZMod.val, Prime.natVal, BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat] at hi_def
  rw [Fin.val_natCast, Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.mod_le _ _) high_lt_p)] at hi_def

  have lt2 : ZMod.val (↑Integer.two_pow_64.toNat : Fp p) *
    ZMod.val (↑⟨hi, by assumption⟩ : Fp p) < 2^128 := by
    rw [ZMod.val_natCast_of_lt (lt_trans (by decide) gt.lt_prime)]
    simp only [ZMod.val, Prime.natVal]
    conv_rhs => change (2^64 * 2^64)
    cases hi_def
    apply (Nat.mul_lt_mul_left _).mpr
    · apply Nat.mod_lt _ (by decide)
    · decide

  rw [ZMod.val_add_of_lt ?lt1, ZMod.val_mul_of_lt ?lt2, ZMod.val_natCast_of_lt ?lt3]

  case lt3 => exact lt_trans (by decide) gt.lt_prime
  case lt2 => apply lt_trans lt2 (lt_trans (by decide) gt.lt_prime)
  case lt1 =>
    refine Nat.lt_trans ?_ gt.lt_prime
    conv_rhs => change 2^128 + 2^128
    apply Nat.add_lt_add
    · simp only [ZMod.val, Prime.natVal]
      apply lt_trans (Nat.mod_lt _ (by decide)) (by decide)
    · rw [ZMod.val_mul_of_lt]
      · exact lt2
      · exact lt_trans lt2 (lt_trans (by decide) gt.lt_prime)

  apply BitVec.eq_of_toNat_eq
  simp only [ZMod.val, Prime.natVal]
  simp only [BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat, BitVec.toNat_mul]

  have : a.toNat = x_hi * 2^64 + x_lo := by
    cases x_hi_def
    cases x_lo_def
    exact Eq.symm (Nat.div_add_mod' _ _)
  rw [this]

  have : b.toNat = y_hi * 2^64 + y_lo := by
    cases y_hi_def
    cases y_lo_def
    exact Eq.symm (Nat.div_add_mod' _ _)
  rw [this]

  cases low_def
  cases high_def
  cases hi_def
  cases carry_def

  conv in Integer.two_pow_64.toNat => change 2^64

  conv_rhs =>
    simp only [Nat.left_distrib, Nat.right_distrib]
    enter [1, 1, 1]
    calc
      _ = x_hi * y_hi * 2^64 * 2^64 := by linarith
      _ = (x_hi * y_hi) * 2^128 := by linarith

  have : 2^128 = (2^64)^2 := by rfl
  simp only [this, Nat.mod_pow_succ (b := 2^64) (k := 1), Nat.pow_one]

  congr 1
  · rw [Nat.add_mul_mod_self_left]
    simp only [Nat.pow_succ (m := 1), Nat.pow_one, ←mul_assoc, add_assoc]
    simp only [Nat.mul_add_mod_self_right]
    conv_rhs => enter [1, 1]; rw [mul_comm, ←mul_assoc]
    simp only [Nat.mul_add_mod_self_right]
    simp
  · congr 1
    rw [Nat.add_mul_div_left _ _ (by decide)]
    rw [Nat.mod_div_self, Nat.zero_add, Nat.mod_mod]
    simp only [Nat.pow_succ (m := 1), Nat.pow_one, ←mul_assoc, add_assoc]
    conv_rhs => rw [add_comm]
    rw [Nat.add_mul_div_right _ _ (by decide)]
    conv_rhs => rw [Nat.add_mul_mod_self_right]
    conv_rhs =>
      rw [add_comm]
      rw [Nat.add_mul_div_right _ _ (by decide)]
      enter [1, 1, 1, 1, 1]
      rw [mul_comm]
    simp only [mul_assoc]
    rw [Nat.mul_add_div (by decide)]
    conv =>
      congr
      · rw [Nat.add_mod]
      · rw [Nat.add_mod, add_comm]
    congr 4
    rw [←Nat.div_eq_sub_mod_div]

set_option maxRecDepth 1300 in
theorem field_wrapping_mul {p a b}
  : STHoare p env ⟦⟧
    (wrapping_mul h![] .field h![] h![] h![a, b])
    (fun r => r = a * b) := by
  resolve_trait
  steps
  simp_all

