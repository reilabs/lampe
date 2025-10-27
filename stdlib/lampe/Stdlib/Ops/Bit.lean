import «std-1.0.0-beta.12».Extracted
import Lampe

namespace Lampe.Stdlib.Ops.Bit

open «std-1.0.0-beta.12»

set_option Lampe.pp.Expr false
set_option Lampe.pp.STHoare false

/-- A shorthand for a call to the `std::ops::bit::Not::not` method. -/
@[reducible]
def not {p}
    (generics : HList Kind.denote «std-1.0.0-beta.12::ops::bit::Not».«#genericKinds»)
    (Self : Tp)
    (associatedTypes : HList Kind.denote «std-1.0.0-beta.12::ops::bit::Not».«#associatedTypesKinds»)
    (fnGenerics : HList Kind.denote «std-1.0.0-beta.12::ops::bit::Not».not.«#genericKinds»)
  : HList (Tp.denote p)
      («std-1.0.0-beta.12::ops::bit::Not».not.«#inputs» generics Self associatedTypes fnGenerics)
  → Expr (Tp.denote p)
      («std-1.0.0-beta.12::ops::bit::Not».not.«#output» generics Self associatedTypes fnGenerics) :=
  «std-1.0.0-beta.12::ops::bit::Not».not generics Self associatedTypes fnGenerics

set_option maxRecDepth 1300 in
theorem bool_not_spec {p a}
  : STHoare p env ⟦⟧
    (not h![] .bool h![] h![] h![a])
    (fun r => r = !a) := by
  resolve_trait
  steps
  simp_all
  exact ()

set_option maxRecDepth 1300 in
theorem u128_not_spec {p a}
  : STHoare p env ⟦⟧
    (not h![] (.u 128) h![] h![] h![a])
    (fun r => r = a.not) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1300 in
theorem u64_not_spec {p a}
  : STHoare p env ⟦⟧
    (not h![] (.u 64) h![] h![] h![a])
    (fun r => r = a.not) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1300 in
theorem u32_not_spec {p a}
  : STHoare p env ⟦⟧
    (not h![] (.u 32) h![] h![] h![a])
    (fun r => r = a.not) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1300 in
theorem u16_not_spec {p a}
  : STHoare p env ⟦⟧
    (not h![] (.u 16) h![] h![] h![a])
    (fun r => r = a.not) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1300 in
theorem u8_not_spec {p a}
  : STHoare p env ⟦⟧
    (not h![] (.u 8) h![] h![] h![a])
    (fun r => r = a.not) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1350 in
theorem u1_not_spec {p a}
  : STHoare p env ⟦⟧
    (not h![] (.u 1) h![] h![] h![a])
    (fun r => r = a.not) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1350 in
theorem i8_not_spec {p a}
  : STHoare p env ⟦⟧
    (not h![] (.i 8) h![] h![] h![a])
    (fun r => r = a.not) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1350 in
theorem i16_not_spec {p a}
  : STHoare p env ⟦⟧
    (not h![] (.i 16) h![] h![] h![a])
    (fun r => r = a.not) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1350 in
theorem i32_not_spec {p a}
  : STHoare p env ⟦⟧
    (not h![] (.i 32) h![] h![] h![a])
    (fun r => r = a.not) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1350 in
theorem i64_not_spec {p a}
  : STHoare p env ⟦⟧
    (not h![] (.i 64) h![] h![] h![a])
    (fun r => r = a.not) := by
  resolve_trait
  steps
  simp_all

/-- A shorthand for a call to the `std::ops::bit::BitOr::bitor` method. -/
@[reducible]
def bitOr {p}
    (generics : HList Kind.denote «std-1.0.0-beta.12::ops::bit::BitOr».«#genericKinds»)
    (Self : Tp)
    (associatedTypes : HList Kind.denote «std-1.0.0-beta.12::ops::bit::BitOr».«#associatedTypesKinds»)
    (fnGenerics : HList Kind.denote «std-1.0.0-beta.12::ops::bit::BitOr».bitor.«#genericKinds»)
  : HList (Tp.denote p)
      («std-1.0.0-beta.12::ops::bit::BitOr».bitor.«#inputs» generics Self associatedTypes fnGenerics)
  → Expr (Tp.denote p)
      («std-1.0.0-beta.12::ops::bit::BitOr».bitor.«#output» generics Self associatedTypes fnGenerics) :=
  «std-1.0.0-beta.12::ops::bit::BitOr».bitor generics Self associatedTypes fnGenerics

set_option maxRecDepth 1350 in
theorem bool_bit_or_spec {p a b}
  : STHoare p env ⟦⟧
    (bitOr h![] .bool h![] h![] h![a, b])
    (fun r => r = a.or b) := by
  resolve_trait
  steps
  simp_all
  exact ()

set_option maxRecDepth 1350 in
theorem u128_bit_or_spec {p a b}
  : STHoare p env ⟦⟧
    (bitOr h![] (.u 128) h![] h![] h![a, b])
    (fun r => r = a.or b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1350 in
theorem u64_bit_or_spec {p a b}
  : STHoare p env ⟦⟧
    (bitOr h![] (.u 64) h![] h![] h![a, b])
    (fun r => r = a.or b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1350 in
theorem u32_bit_or_spec {p a b}
  : STHoare p env ⟦⟧
    (bitOr h![] (.u 32) h![] h![] h![a, b])
    (fun r => r = a.or b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1350 in
theorem u16_bit_or_spec {p a b}
  : STHoare p env ⟦⟧
    (bitOr h![] (.u 16) h![] h![] h![a, b])
    (fun r => r = a.or b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1350 in
theorem u8_bit_or_spec {p a b}
  : STHoare p env ⟦⟧
    (bitOr h![] (.u 8) h![] h![] h![a, b])
    (fun r => r = a.or b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1350 in
theorem u1_bit_or_spec {p a b}
  : STHoare p env ⟦⟧
    (bitOr h![] (.u 1) h![] h![] h![a, b])
    (fun r => r = a.or b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1350 in
theorem i8_bit_or_spec {p a b}
  : STHoare p env ⟦⟧
    (bitOr h![] (.i 8) h![] h![] h![a, b])
    (fun r => r = a.or b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1350 in
theorem i16_bit_or_spec {p a b}
  : STHoare p env ⟦⟧
    (bitOr h![] (.i 16) h![] h![] h![a, b])
    (fun r => r = a.or b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1350 in
theorem i32_bit_or_spec {p a b}
  : STHoare p env ⟦⟧
    (bitOr h![] (.i 32) h![] h![] h![a, b])
    (fun r => r = a.or b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1350 in
theorem i64_bit_or_spec {p a b}
  : STHoare p env ⟦⟧
    (bitOr h![] (.i 64) h![] h![] h![a, b])
    (fun r => r = a.or b) := by
  resolve_trait
  steps
  simp_all

/-- A shorthand for a call to the `std::ops::bit::BitOr::bitand` method. -/
@[reducible]
def bitAnd {p}
    (generics : HList Kind.denote «std-1.0.0-beta.12::ops::bit::BitAnd».«#genericKinds»)
    (Self : Tp)
    (associatedTypes : HList Kind.denote «std-1.0.0-beta.12::ops::bit::BitAnd».«#associatedTypesKinds»)
    (fnGenerics : HList Kind.denote «std-1.0.0-beta.12::ops::bit::BitAnd».bitand.«#genericKinds»)
  : HList (Tp.denote p)
      («std-1.0.0-beta.12::ops::bit::BitAnd».bitand.«#inputs» generics Self associatedTypes fnGenerics)
  → Expr (Tp.denote p)
      («std-1.0.0-beta.12::ops::bit::BitAnd».bitand.«#output» generics Self associatedTypes fnGenerics) :=
  «std-1.0.0-beta.12::ops::bit::BitAnd».bitand generics Self associatedTypes fnGenerics

set_option maxRecDepth 1350 in
theorem bool_bit_and_spec {p a b}
  : STHoare p env ⟦⟧
    (bitAnd h![] .bool h![] h![] h![a, b])
    (fun r => r = a.and b) := by
  resolve_trait
  steps
  simp_all
  exact ()

set_option maxRecDepth 1400 in
theorem u128_bit_and_spec {p a b}
  : STHoare p env ⟦⟧
    (bitAnd h![] (.u 128) h![] h![] h![a, b])
    (fun r => r = a.and b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1400 in
theorem u64_bit_and_spec {p a b}
  : STHoare p env ⟦⟧
    (bitAnd h![] (.u 64) h![] h![] h![a, b])
    (fun r => r = a.and b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1400 in
theorem u32_bit_and_spec {p a b}
  : STHoare p env ⟦⟧
    (bitAnd h![] (.u 32) h![] h![] h![a, b])
    (fun r => r = a.and b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1400 in
theorem u16_bit_and_spec {p a b}
  : STHoare p env ⟦⟧
    (bitAnd h![] (.u 16) h![] h![] h![a, b])
    (fun r => r = a.and b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1400 in
theorem u8_bit_and_spec {p a b}
  : STHoare p env ⟦⟧
    (bitAnd h![] (.u 8) h![] h![] h![a, b])
    (fun r => r = a.and b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1400 in
theorem u1_bit_and_spec {p a b}
  : STHoare p env ⟦⟧
    (bitAnd h![] (.u 1) h![] h![] h![a, b])
    (fun r => r = a.and b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1400 in
theorem i8_bit_and_spec {p a b}
  : STHoare p env ⟦⟧
    (bitAnd h![] (.i 8) h![] h![] h![a, b])
    (fun r => r = a.and b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1400 in
theorem i16_bit_and_spec {p a b}
  : STHoare p env ⟦⟧
    (bitAnd h![] (.i 16) h![] h![] h![a, b])
    (fun r => r = a.and b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1400 in
theorem i32_bit_and_spec {p a b}
  : STHoare p env ⟦⟧
    (bitAnd h![] (.i 32) h![] h![] h![a, b])
    (fun r => r = a.and b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1400 in
theorem i64_bit_and_spec {p a b}
  : STHoare p env ⟦⟧
    (bitAnd h![] (.i 64) h![] h![] h![a, b])
    (fun r => r = a.and b) := by
  resolve_trait
  steps
  simp_all

/-- A shorthand for a call to the `std::ops::bit::BitXor::bitxor` method. -/
@[reducible]
def bitXor {p}
    (generics : HList Kind.denote «std-1.0.0-beta.12::ops::bit::BitXor».«#genericKinds»)
    (Self : Tp)
    (associatedTypes : HList Kind.denote «std-1.0.0-beta.12::ops::bit::BitXor».«#associatedTypesKinds»)
    (fnGenerics : HList Kind.denote «std-1.0.0-beta.12::ops::bit::BitXor».bitxor.«#genericKinds»)
  : HList (Tp.denote p)
      («std-1.0.0-beta.12::ops::bit::BitXor».bitxor.«#inputs» generics Self associatedTypes fnGenerics)
  → Expr (Tp.denote p)
      («std-1.0.0-beta.12::ops::bit::BitXor».bitxor.«#output» generics Self associatedTypes fnGenerics) :=
  «std-1.0.0-beta.12::ops::bit::BitXor».bitxor generics Self associatedTypes fnGenerics

set_option maxRecDepth 1400 in
theorem bool_bit_xor_spec {p a b}
  : STHoare p env ⟦⟧
    (bitXor h![] .bool h![] h![] h![a, b])
    (fun r => r = a.xor b) := by
  resolve_trait
  steps
  simp_all
  exact ()

set_option maxRecDepth 1400 in
theorem u128_bit_xor_spec {p a b}
  : STHoare p env ⟦⟧
    (bitXor h![] (.u 128) h![] h![] h![a, b])
    (fun r => r = a.xor b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1400 in
theorem u64_bit_xor_spec {p a b}
  : STHoare p env ⟦⟧
    (bitXor h![] (.u 64) h![] h![] h![a, b])
    (fun r => r = a.xor b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1400 in
theorem u32_bit_xor_spec {p a b}
  : STHoare p env ⟦⟧
    (bitXor h![] (.u 32) h![] h![] h![a, b])
    (fun r => r = a.xor b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1400 in
theorem u16_bit_xor_spec {p a b}
  : STHoare p env ⟦⟧
    (bitXor h![] (.u 16) h![] h![] h![a, b])
    (fun r => r = a.xor b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1400 in
theorem u8_bit_xor_spec {p a b}
  : STHoare p env ⟦⟧
    (bitXor h![] (.u 8) h![] h![] h![a, b])
    (fun r => r = a.xor b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1450 in
theorem u1_bit_xor_spec {p a b}
  : STHoare p env ⟦⟧
    (bitXor h![] (.u 1) h![] h![] h![a, b])
    (fun r => r = a.xor b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1450 in
theorem i8_bit_xor_spec {p a b}
  : STHoare p env ⟦⟧
    (bitXor h![] (.i 8) h![] h![] h![a, b])
    (fun r => r = a.xor b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1450 in
theorem i16_bit_xor_spec {p a b}
  : STHoare p env ⟦⟧
    (bitXor h![] (.i 16) h![] h![] h![a, b])
    (fun r => r = a.xor b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1450 in
theorem i32_bit_xor_spec {p a b}
  : STHoare p env ⟦⟧
    (bitXor h![] (.i 32) h![] h![] h![a, b])
    (fun r => r = a.xor b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1450 in
theorem i64_bit_xor_spec {p a b}
  : STHoare p env ⟦⟧
    (bitXor h![] (.i 64) h![] h![] h![a, b])
    (fun r => r = a.xor b) := by
  resolve_trait
  steps
  simp_all

/-- A shorthand for a call to the `std::ops::bit::Shl::shl` method. -/
@[reducible]
def shl {p}
    (generics : HList Kind.denote «std-1.0.0-beta.12::ops::bit::Shl».«#genericKinds»)
    (Self : Tp)
    (associatedTypes : HList Kind.denote «std-1.0.0-beta.12::ops::bit::Shl».«#associatedTypesKinds»)
    (fnGenerics : HList Kind.denote «std-1.0.0-beta.12::ops::bit::Shl».shl.«#genericKinds»)
  : HList (Tp.denote p)
      («std-1.0.0-beta.12::ops::bit::Shl».shl.«#inputs» generics Self associatedTypes fnGenerics)
  → Expr (Tp.denote p)
      («std-1.0.0-beta.12::ops::bit::Shl».shl.«#output» generics Self associatedTypes fnGenerics) :=
  «std-1.0.0-beta.12::ops::bit::Shl».shl generics Self associatedTypes fnGenerics

set_option maxRecDepth 1450 in
theorem u128_shl_spec {p a b}
  : STHoare p env ⟦⟧
    (shl h![] (.u 128) h![] h![] h![a, b])
    (fun r => r = a <<< b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1450 in
theorem u64_shl_spec {p a b}
  : STHoare p env ⟦⟧
    (shl h![] (.u 64) h![] h![] h![a, b])
    (fun r => r = a <<< b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1450 in
theorem u32_shl_spec {p a b}
  : STHoare p env ⟦⟧
    (shl h![] (.u 32) h![] h![] h![a, b])
    (fun r => r = a <<< b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1450 in
theorem u16_shl_spec {p a b}
  : STHoare p env ⟦⟧
    (shl h![] (.u 16) h![] h![] h![a, b])
    (fun r => r = a <<< b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1450 in
theorem u8_shl_spec {p a b}
  : STHoare p env ⟦⟧
    (shl h![] (.u 8) h![] h![] h![a, b])
    (fun r => r = a <<< b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1450 in
theorem u1_shl_spec {p a b}
  : STHoare p env ⟦⟧
    (shl h![] (.u 1) h![] h![] h![a, b])
    (fun r => r = a <<< b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1450 in
theorem i8_shl_spec {p a b}
  : STHoare p env ⟦⟧
    (shl h![] (.i 8) h![] h![] h![a, b])
    (fun r => r = a <<< b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1450 in
theorem i16_shl_spec {p a b}
  : STHoare p env ⟦⟧
    (shl h![] (.i 16) h![] h![] h![a, b])
    (fun r => r = a <<< b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1450 in
theorem i32_shl_spec {p a b}
  : STHoare p env ⟦⟧
    (shl h![] (.i 32) h![] h![] h![a, b])
    (fun r => r = a <<< b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1450 in
theorem i64_shl_spec {p a b}
  : STHoare p env ⟦⟧
    (shl h![] (.i 64) h![] h![] h![a, b])
    (fun r => r = a <<< b) := by
  resolve_trait
  steps
  simp_all

/-- A shorthand for a call to the `std::ops::bit::Shr::shr` method. -/
@[reducible]
def shr {p}
    (generics : HList Kind.denote «std-1.0.0-beta.12::ops::bit::Shr».«#genericKinds»)
    (Self : Tp)
    (associatedTypes : HList Kind.denote «std-1.0.0-beta.12::ops::bit::Shr».«#associatedTypesKinds»)
    (fnGenerics : HList Kind.denote «std-1.0.0-beta.12::ops::bit::Shr».shr.«#genericKinds»)
  : HList (Tp.denote p)
      («std-1.0.0-beta.12::ops::bit::Shr».shr.«#inputs» generics Self associatedTypes fnGenerics)
  → Expr (Tp.denote p)
      («std-1.0.0-beta.12::ops::bit::Shr».shr.«#output» generics Self associatedTypes fnGenerics) :=
  «std-1.0.0-beta.12::ops::bit::Shr».shr generics Self associatedTypes fnGenerics

set_option maxRecDepth 1450 in
theorem u128_shr_spec {p a b}
  : STHoare p env ⟦⟧
    (shr h![] (.u 128) h![] h![] h![a, b])
    (fun r => r = a >>> b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1450 in
theorem u64_shr_spec {p a b}
  : STHoare p env ⟦⟧
    (shr h![] (.u 64) h![] h![] h![a, b])
    (fun r => r = a >>> b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1500 in
theorem u32_shr_spec {p a b}
  : STHoare p env ⟦⟧
    (shr h![] (.u 32) h![] h![] h![a, b])
    (fun r => r = a >>> b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1500 in
theorem u16_shr_spec {p a b}
  : STHoare p env ⟦⟧
    (shr h![] (.u 16) h![] h![] h![a, b])
    (fun r => r = a >>> b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1500 in
theorem u8_shr_spec {p a b}
  : STHoare p env ⟦⟧
    (shr h![] (.u 8) h![] h![] h![a, b])
    (fun r => r = a >>> b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1500 in
theorem u1_shr_spec {p a b}
  : STHoare p env ⟦⟧
    (shr h![] (.u 1) h![] h![] h![a, b])
    (fun r => r = a >>> b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1500 in
theorem i8_shr_spec {p a b}
  : STHoare p env ⟦⟧
    (shr h![] (.i 8) h![] h![] h![a, b])
    (fun r => r = a >>> b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1500 in
theorem i16_shr_spec {p a b}
  : STHoare p env ⟦⟧
    (shr h![] (.i 16) h![] h![] h![a, b])
    (fun r => r = a >>> b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1500 in
theorem i32_shr_spec {p a b}
  : STHoare p env ⟦⟧
    (shr h![] (.i 32) h![] h![] h![a, b])
    (fun r => r = a >>> b) := by
  resolve_trait
  steps
  simp_all

set_option maxRecDepth 1500 in
theorem i64_shr_spec {p a b}
  : STHoare p env ⟦⟧
    (shr h![] (.i 64) h![] h![] h![a, b])
    (fun r => r = a >>> b) := by
  resolve_trait
  steps
  simp_all

