import «std-1.0.0-beta.12».Extracted
import Lampe

namespace Lampe.Stdlib.Convert

open «std-1.0.0-beta.12»

set_option Lampe.pp.Expr true
set_option Lampe.pp.STHoare true

/-- A shorthand for a call to the `std::convert::From::from` method. -/
@[reducible]
def «from» {p}
    (generics : HList Kind.denote «std-1.0.0-beta.12::convert::From».«#genericKinds»)
    (Self : Tp)
    (associatedTypes : HList Kind.denote «std-1.0.0-beta.12::convert::From».«#associatedTypesKinds»)
    (fnGenerics : HList Kind.denote «std-1.0.0-beta.12::convert::From».«from».«#genericKinds»)
  : HList (Tp.denote p)
      («std-1.0.0-beta.12::convert::From».«from».«#inputs» generics Self associatedTypes fnGenerics)
  → Expr (Tp.denote p)
      («std-1.0.0-beta.12::convert::From».«from».«#output» generics Self associatedTypes fnGenerics) :=
  «std-1.0.0-beta.12::convert::From».«from» generics Self associatedTypes fnGenerics

/--
Asserts that the provided `tp` has an implementation of `std::convert::From` in the environment.
-/
@[reducible]
def hasFromImpl (env : Env) (source : Tp) (self : Tp) :=
  «std-1.0.0-beta.12::convert::From».hasImpl env h![source] self

/-- A shorthand for a call to the `std::convert::Into::into` method. -/
@[reducible]
def into {p}
    (generics : HList Kind.denote «std-1.0.0-beta.12::convert::Into».«#genericKinds»)
    (Self : Tp)
    (associatedTypes : HList Kind.denote «std-1.0.0-beta.12::convert::Into».«#associatedTypesKinds»)
    (fnGenerics : HList Kind.denote «std-1.0.0-beta.12::convert::Into».into.«#genericKinds»)
  : HList (Tp.denote p)
      («std-1.0.0-beta.12::convert::Into».into.«#inputs» generics Self associatedTypes fnGenerics)
  → Expr (Tp.denote p)
      («std-1.0.0-beta.12::convert::Into».into.«#output» generics Self associatedTypes fnGenerics) :=
  «std-1.0.0-beta.12::convert::Into».into generics Self associatedTypes fnGenerics

/--
Asserts that the provided `tp` has an implementation of `std::convert::Into` in the environment.
-/
@[reducible]
def hasIntoImpl (env : Env) (target : Tp) (self : Tp) :=
  «std-1.0.0-beta.12::convert::Into».hasImpl env h![target] self

/-- A shorthand for a call to the `std::convert::AsPrimitive::as_` method. -/
@[reducible]
def as_ {p}
    (generics : HList Kind.denote «std-1.0.0-beta.12::convert::AsPrimitive».«#genericKinds»)
    (Self : Tp)
    (associatedTypes : HList Kind.denote «std-1.0.0-beta.12::convert::AsPrimitive».«#associatedTypesKinds»)
    (fnGenerics : HList Kind.denote «std-1.0.0-beta.12::convert::AsPrimitive».as_.«#genericKinds»)
  : HList (Tp.denote p)
      («std-1.0.0-beta.12::convert::AsPrimitive».as_.«#inputs» generics Self associatedTypes fnGenerics)
  → Expr (Tp.denote p)
      («std-1.0.0-beta.12::convert::AsPrimitive».as_.«#output» generics Self associatedTypes fnGenerics) :=
  «std-1.0.0-beta.12::convert::AsPrimitive».as_ generics Self associatedTypes fnGenerics

/--
Asserts that the provided `tp` has an implementation of `std::convert::Into` in the environment.
-/
@[reducible]
def hasAsPrimitiveImpl (env : Env) (target : Tp) (self : Tp) :=
  «std-1.0.0-beta.12::convert::AsPrimitive».hasImpl env h![target] self

theorem from_T_for_T_spec {p T i}
  : STHoare p env ⟦⟧
    («from» h![T] T h![] h![] h![i])
    (fun r => r = i) := by
  resolve_trait
  steps
  simp_all

theorem into_T_for_U_spec {p}
    {T U : Tp}
    {i : U.denote p}
    {has_from : hasFromImpl env U T}
    {from_emb : U.denote p → T.denote p}
    (from_f : ∀a, STHoare p env ⟦⟧ («from» h![U] T h![] h![] h![a]) (fun r => r = from_emb a))
  : STHoare p env ⟦⟧
    (into h![T] U h![] h![] h![i])
    (fun r => r = from_emb i) := by
  resolve_trait
  steps [from_f]
  simp_all

@[reducible]
def convertUintToUintSemantics (s₁ s₂ : ℕ) (p : Prime) (a : Tp.denote p (.u s₁)) :=
  STHoare p env ⟦⟧
    («from» h![.u s₁] (.u s₂) h![] h![] h![a])
    (fun r => r = (a.zeroExtend s₂))

theorem from_u8_for_u16_spec {p a} : convertUintToUintSemantics 8 16 p a := by
  resolve_trait
  steps
  simp_all

theorem from_u8_for_u32_spec {p a} : convertUintToUintSemantics 8 32 p a := by
  resolve_trait
  steps
  simp_all

theorem from_u16_for_u32_spec {p a} : convertUintToUintSemantics 16 32 p a := by
  resolve_trait
  steps
  simp_all

theorem from_u8_for_u64_spec {p a} : convertUintToUintSemantics 8 64 p a := by
  resolve_trait
  steps
  simp_all

theorem from_u16_for_u64_spec {p a} : convertUintToUintSemantics 16 64 p a := by
  resolve_trait
  steps
  simp_all

theorem from_u32_for_u64_spec {p a} : convertUintToUintSemantics 32 64 p a := by
  resolve_trait
  steps
  simp_all

theorem from_u8_for_u128_spec {p a} : convertUintToUintSemantics 8 128 p a := by
  resolve_trait
  steps
  simp_all

theorem from_u16_for_u128_spec {p a} : convertUintToUintSemantics 16 128 p a := by
  resolve_trait
  steps
  simp_all

theorem from_u32_for_u128_spec {p a} : convertUintToUintSemantics 32 128 p a := by
  resolve_trait
  steps
  simp_all

theorem from_u64_for_u128_spec {p a} : convertUintToUintSemantics 64 128 p a := by
  resolve_trait
  steps
  simp_all

@[reducible]
def convertUintToFieldSemantics (s₁ : ℕ) (p : Prime) (a : Tp.denote p (.u s₁)) :=
  STHoare p env ⟦⟧
    («from» h![.u s₁] .field h![] h![] h![a])
    (fun r => r = a.toNat)

theorem from_u8_for_field_spec {p a} : convertUintToFieldSemantics 8 p a := by
  resolve_trait
  steps
  simp_all

theorem from_u16_for_field_spec {p a} : convertUintToFieldSemantics 16 p a := by
  resolve_trait
  steps
  simp_all

theorem from_u32_for_field_spec {p a} : convertUintToFieldSemantics 32 p a := by
  resolve_trait
  steps
  simp_all

theorem from_u64_for_field_spec {p a} : convertUintToFieldSemantics 64 p a := by
  resolve_trait
  steps
  simp_all

theorem from_u128_for_field_spec {p a} : convertUintToFieldSemantics 128 p a := by
  resolve_trait
  steps
  simp_all

@[reducible]
def convertIntToIntSemantics (s₁ s₂ : ℕ) (p : Prime) (a : Tp.denote p (.i s₁)) :=
  STHoare p env ⟦⟧
    («from» h![.i s₁] (.i s₂) h![] h![] h![a])
    (fun r => r = (a.signExtend s₂))

theorem from_i8_for_i16_spec {p a} : convertIntToIntSemantics 8 16 p a := by
  resolve_trait
  steps
  simp_all

theorem from_i8_for_i32_spec {p a} : convertIntToIntSemantics 8 32 p a := by
  resolve_trait
  steps
  simp_all

theorem from_i8_for_i64_spec {p a} : convertIntToIntSemantics 8 64 p a := by
  resolve_trait
  steps
  simp_all

theorem from_i16_for_i64_spec {p a} : convertIntToIntSemantics 16 64 p a := by
  resolve_trait
  steps
  simp_all

theorem from_i32_for_i64_spec {p a} : convertIntToIntSemantics 32 64 p a := by
  resolve_trait
  steps
  simp_all

@[reducible]
def convertBoolToUintSemantics (s₁ : ℕ) (p : Prime) (a : Tp.denote p .bool) :=
  STHoare p env ⟦⟧
    («from» h![.bool] (.u s₁) h![] h![] h![a])
    (fun r => r = if a then 1 else 0)

theorem from_bool_for_u8_spec {p a} : convertBoolToUintSemantics 8 p a := by
  resolve_trait
  steps
  simp_all

theorem from_bool_for_u16_spec {p a} : convertBoolToUintSemantics 16 p a := by
  resolve_trait
  steps
  simp_all

theorem from_bool_for_u32_spec {p a} : convertBoolToUintSemantics 32 p a := by
  resolve_trait
  steps
  simp_all

theorem from_bool_for_u64_spec {p a} : convertBoolToUintSemantics 64 p a := by
  resolve_trait
  steps
  simp_all

theorem from_bool_for_u128_spec {p a} : convertBoolToUintSemantics 128 p a := by
  resolve_trait
  steps
  simp_all

@[reducible]
def convertBoolToIntSemantics (s₁ : ℕ) (p : Prime) (a : Tp.denote p .bool) :=
  STHoare p env ⟦⟧
    («from» h![.bool] (.i s₁) h![] h![] h![a])
    (fun r => r = if a then 1 else 0)

theorem from_bool_for_i8_spec {p a} : convertBoolToIntSemantics 8 p a := by
  resolve_trait
  steps
  simp_all

theorem from_bool_for_i16_spec {p a} : convertBoolToIntSemantics 16 p a := by
  resolve_trait
  steps
  simp_all

theorem from_bool_for_i32_spec {p a} : convertBoolToIntSemantics 32 p a := by
  resolve_trait
  steps
  simp_all

theorem from_bool_for_i64_spec {p a} : convertBoolToIntSemantics 64 p a := by
  resolve_trait
  steps
  simp_all

theorem from_bool_for_field_spec {p a}
  : STHoare p env ⟦⟧
    («from» h![.bool] .field h![] h![] h![a])
    (fun r => r = if a then 1 else 0) := by
  resolve_trait
  steps
  simp_all

/--
The semantics of `AsPrimitive::as_` are defined to be equal to the corresponding primitive cast, so
we delegate straight to our builtin semantics for those here.
-/
@[reducible]
def asPrimitiveSemantics (src tgt : Tp) [Builtin.CastTp src tgt] (p : Prime) (a : Tp.denote p src) :=
  STHoare p env ⟦⟧
    (as_ h![tgt] src h![] h![] h![a])
    (fun r => r = Builtin.CastTp.cast a)

theorem as_u8_for_bool_spec {p a} : asPrimitiveSemantics .bool (.u 8) p a := by
  resolve_trait
  steps
  simp_all

theorem as_i8_for_bool_spec {p a} : asPrimitiveSemantics .bool (.i 8) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u32_for_bool_spec {p a} : asPrimitiveSemantics .bool (.u 32) p a := by
  resolve_trait
  steps
  simp_all

theorem as_i32_for_bool_spec {p a} : asPrimitiveSemantics .bool (.i 32) p a := by
  resolve_trait
  steps
  simp_all

theorem as_bool_for_bool_spec {p a} : asPrimitiveSemantics .bool .bool p a := by
  resolve_trait
  steps
  simp_all

theorem as_bool_for_u8_spec {p a} : asPrimitiveSemantics (.u 8) .bool p a := by
  resolve_trait
  steps
  subst_vars
  rfl

theorem as_bool_for_i8_spec {p a} : asPrimitiveSemantics (.i 8) .bool p a := by
  resolve_trait
  steps
  subst_vars
  rfl

theorem as_bool_for_u16_spec {p a} : asPrimitiveSemantics (.u 16) .bool p a := by
  resolve_trait
  steps
  subst_vars
  rfl

theorem as_bool_for_i16_spec {p a} : asPrimitiveSemantics (.i 16) .bool p a := by
  resolve_trait
  steps
  subst_vars
  rfl

theorem as_bool_for_u32_spec {p a} : asPrimitiveSemantics (.u 32) .bool p a := by
  resolve_trait
  steps
  subst_vars
  rfl

theorem as_bool_for_i32_spec {p a} : asPrimitiveSemantics (.i 32) .bool p a := by
  resolve_trait
  steps
  subst_vars
  rfl

theorem as_bool_for_u64_spec {p a} : asPrimitiveSemantics (.u 64) .bool p a := by
  resolve_trait
  steps
  subst_vars
  rfl

theorem as_bool_for_i64_spec {p a} : asPrimitiveSemantics (.i 64) .bool p a := by
  resolve_trait
  steps
  subst_vars
  rfl

theorem as_bool_for_u128_spec {p a} : asPrimitiveSemantics (.u 128) .bool p a := by
  resolve_trait
  steps
  subst_vars
  rfl

theorem as_bool_for_field_spec {p a} : asPrimitiveSemantics .field .bool p a := by
  resolve_trait
  steps
  simp_all
  rfl
  exact ()

theorem as_u128_for_bool_spec {p a} : asPrimitiveSemantics .bool (.u 128) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u16_for_bool_spec {p a} : asPrimitiveSemantics .bool (.u 16) p a := by
  resolve_trait
  steps
  simp_all

theorem as_i16_for_bool_spec {p a} : asPrimitiveSemantics .bool (.i 16) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u64_for_bool_spec {p a} : asPrimitiveSemantics .bool (.u 64) p a := by
  resolve_trait
  steps
  simp_all

theorem as_i64_for_bool_spec {p a} : asPrimitiveSemantics .bool (.i 64) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u8_for_u32_spec {p a} : asPrimitiveSemantics (.u 8) (.u 32) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u8_for_i32_spec {p a} : asPrimitiveSemantics (.u 8) (.i 32) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u8_for_u128_spec {p a} : asPrimitiveSemantics (.u 128) (.u 8) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u8_for_u16_spec {p a} : asPrimitiveSemantics (.u 16) (.u 8) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u8_for_i16_spec {p a} : asPrimitiveSemantics (.i 16) (.u 8) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u8_for_u64_spec {p a} : asPrimitiveSemantics (.u 64) (.u 8) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u8_for_i64_spec {p a} : asPrimitiveSemantics (.i 64) (.u 8) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u8_for_u8_spec {p a} : asPrimitiveSemantics (.u 8) (.u 8) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u8_for_i8_spec {p a} : asPrimitiveSemantics (.i 8) (.u 8) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u16_for_u32_spec {p a} : asPrimitiveSemantics (.u 32) (.u 16) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u16_for_i32_spec {p a} : asPrimitiveSemantics (.i 32) (.u 16) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u16_from_bool_spec {p a} : asPrimitiveSemantics .bool (.u 16) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u16_for_u128_spec {p a} : asPrimitiveSemantics (.u 128) (.u 16) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u16_for_u16_spec {p a} : asPrimitiveSemantics (.u 16) (.u 16) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u16_for_i16_spec {p a} : asPrimitiveSemantics (.i 16) (.u 16) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u16_for_u64_spec {p a} : asPrimitiveSemantics (.u 64) (.u 16) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u16_for_i64_spec {p a} : asPrimitiveSemantics (.i 64) (.u 16) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u16_for_u8_spec {p a} : asPrimitiveSemantics (.u 8) (.u 16) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u16_for_i8_spec {p a} : asPrimitiveSemantics (.i 8) (.u 16) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u32_for_u32_spec {p a} : asPrimitiveSemantics (.u 32) (.u 32) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u32_for_i32_spec {p a} : asPrimitiveSemantics (.i 32) (.u 32) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u32_for_u128_spec {p a} : asPrimitiveSemantics (.u 128) (.u 32) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u32_for_u16_spec {p a} : asPrimitiveSemantics (.u 16) (.u 32) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u32_for_i16_spec {p a} : asPrimitiveSemantics (.i 16) (.u 32) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u32_for_u64_spec {p a} : asPrimitiveSemantics (.u 64) (.u 32) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u32_for_i64_spec {p a} : asPrimitiveSemantics (.i 64) (.u 32) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u32_for_u8_spec {p a} : asPrimitiveSemantics (.u 8) (.u 32) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u32_for_i8_spec {p a} : asPrimitiveSemantics (.i 8) (.u 32) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u64_for_u32_spec {p a} : asPrimitiveSemantics (.u 32) (.u 64) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u64_for_i32_spec {p a} : asPrimitiveSemantics (.i 32) (.u 64) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u64_for_u128_spec {p a} : asPrimitiveSemantics (.u 128) (.u 64) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u64_for_u16_spec {p a} : asPrimitiveSemantics (.u 16) (.u 64) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u64_for_i16_spec {p a} : asPrimitiveSemantics (.i 16) (.u 64) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u64_for_u64_spec {p a} : asPrimitiveSemantics (.u 64) (.u 64) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u64_for_i64_spec {p a} : asPrimitiveSemantics (.i 64) (.u 64) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u64_for_u8_spec {p a} : asPrimitiveSemantics (.u 8) (.u 64) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u64_for_i8_spec {p a} : asPrimitiveSemantics (.i 8) (.u 64) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u128_for_u32_spec {p a} : asPrimitiveSemantics (.u 32) (.u 128) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u128_for_i32_spec {p a} : asPrimitiveSemantics (.i 32) (.u 128) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u128_for_u128_spec {p a} : asPrimitiveSemantics (.u 128) (.u 128) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u128_for_u16_spec {p a} : asPrimitiveSemantics (.u 16) (.u 128) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u128_for_i16_spec {p a} : asPrimitiveSemantics (.i 16) (.u 128) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u128_for_u64_spec {p a} : asPrimitiveSemantics (.u 64) (.u 128) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u128_for_i64_spec {p a} : asPrimitiveSemantics (.i 64) (.u 128) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u128_for_u8_spec {p a} : asPrimitiveSemantics (.u 8) (.u 128) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u128_for_i8_spec {p a} : asPrimitiveSemantics (.i 8) (.u 128) p a := by
  resolve_trait
  steps
  simp_all

theorem as_i8_for_u128_spec {p a} : asPrimitiveSemantics (.u 128) (.i 8) p a := by
  resolve_trait
  steps
  simp_all

theorem as_i8_for_u16_spec {p a} : asPrimitiveSemantics (.u 16) (.i 8) p a := by
  resolve_trait
  steps
  simp_all

theorem as_i8_for_i16_spec {p a} : asPrimitiveSemantics (.i 16) (.i 8) p a := by
  resolve_trait
  steps
  simp_all

theorem as_i8_for_u64_spec {p a} : asPrimitiveSemantics (.u 64) (.i 8) p a := by
  resolve_trait
  steps
  simp_all

theorem as_i8_for_i64_spec {p a} : asPrimitiveSemantics (.i 64) (.i 8) p a := by
  resolve_trait
  steps
  simp_all

theorem as_i8_for_u8_spec {p a} : asPrimitiveSemantics (.u 8) (.i 8) p a := by
  resolve_trait
  steps
  simp_all

theorem as_i8_for_i8_spec {p a} : asPrimitiveSemantics (.i 8) (.i 8) p a := by
  resolve_trait
  steps
  simp_all

theorem as_i8_for_u32_spec {p a} : asPrimitiveSemantics (.u 32) (.i 8) p a := by
  resolve_trait
  steps
  simp_all

theorem as_i8_for_i32_spec {p a} : asPrimitiveSemantics (.i 32) (.i 8) p a := by
  resolve_trait
  steps
  simp_all

theorem as_16_for_bool_spec {p a} : asPrimitiveSemantics .bool (.i 16) p a := by
  resolve_trait
  steps
  simp_all

theorem as_i16_for_u128_spec {p a} : asPrimitiveSemantics (.u 128) (.i 16) p a := by
  resolve_trait
  steps
  simp_all

theorem as_i16_for_u16_spec {p a} : asPrimitiveSemantics (.u 16) (.i 16) p a := by
  resolve_trait
  steps
  simp_all

theorem as_i16_for_i16_spec {p a} : asPrimitiveSemantics (.i 16) (.i 16) p a := by
  resolve_trait
  steps
  simp_all

theorem as_i16_for_u64_spec {p a} : asPrimitiveSemantics (.u 64) (.i 16) p a := by
  resolve_trait
  steps
  simp_all

theorem as_i16_for_i64_spec {p a} : asPrimitiveSemantics (.i 64) (.i 16) p a := by
  resolve_trait
  steps
  simp_all

theorem as_i16_for_u8_spec {p a} : asPrimitiveSemantics (.u 8) (.i 16) p a := by
  resolve_trait
  steps
  simp_all

theorem as_i16_for_i8_spec {p a} : asPrimitiveSemantics (.i 8) (.i 16) p a := by
  resolve_trait
  steps
  simp_all

theorem as_i16_for_u32_spec {p a} : asPrimitiveSemantics (.u 32) (.i 16) p a := by
  resolve_trait
  steps
  simp_all

theorem as_i16_for_i32_spec {p a} : asPrimitiveSemantics (.i 32) (.i 16) p a := by
  resolve_trait
  steps
  simp_all

theorem as_i32_for_u128_spec {p a} : asPrimitiveSemantics (.u 128) (.i 32) p a := by
  resolve_trait
  steps
  simp_all

theorem as_i32_for_u16_spec {p a} : asPrimitiveSemantics (.u 16) (.i 32) p a := by
  resolve_trait
  steps
  simp_all

theorem as_i32_for_i16_spec {p a} : asPrimitiveSemantics (.i 16) (.i 32) p a := by
  resolve_trait
  steps
  simp_all

theorem as_i32_for_u64_spec {p a} : asPrimitiveSemantics (.u 64) (.i 32) p a := by
  resolve_trait
  steps
  simp_all

theorem as_i32_for_i64_spec {p a} : asPrimitiveSemantics (.i 64) (.i 32) p a := by
  resolve_trait
  steps
  simp_all

theorem as_i32_for_u8_spec {p a} : asPrimitiveSemantics (.u 8) (.i 32) p a := by
  resolve_trait
  steps
  simp_all

theorem as_i32_for_i8_spec {p a} : asPrimitiveSemantics (.i 8) (.i 32) p a := by
  resolve_trait
  steps
  simp_all

theorem as_i32_for_u32_spec {p a} : asPrimitiveSemantics (.u 32) (.i 32) p a := by
  resolve_trait
  steps
  simp_all

theorem as_i32_for_i32_spec {p a} : asPrimitiveSemantics (.i 32) (.i 32) p a := by
  resolve_trait
  steps
  simp_all

theorem as_i64_for_u128_spec {p a} : asPrimitiveSemantics (.u 128) (.i 64) p a := by
  resolve_trait
  steps
  simp_all

theorem as_i64_for_u16_spec {p a} : asPrimitiveSemantics (.u 16) (.i 64) p a := by
  resolve_trait
  steps
  simp_all

theorem as_i64_for_i16_spec {p a} : asPrimitiveSemantics (.i 16) (.i 64) p a := by
  resolve_trait
  steps
  simp_all

theorem as_i64_for_u64_spec {p a} : asPrimitiveSemantics (.u 64) (.i 64) p a := by
  resolve_trait
  steps
  simp_all

theorem as_i64_for_i64_spec {p a} : asPrimitiveSemantics (.i 64) (.i 64) p a := by
  resolve_trait
  steps
  simp_all

theorem as_i64_for_u8_spec {p a} : asPrimitiveSemantics (.u 8) (.i 64) p a := by
  resolve_trait
  steps
  simp_all

theorem as_i64_for_i8_spec {p a} : asPrimitiveSemantics (.i 8) (.i 64) p a := by
  resolve_trait
  steps
  simp_all

theorem as_i64_for_u32_spec {p a} : asPrimitiveSemantics (.u 32) (.i 64) p a := by
  resolve_trait
  steps
  simp_all

theorem as_i64_for_i32_spec {p a} : asPrimitiveSemantics (.i 32) (.i 64) p a := by
  resolve_trait
  steps
  simp_all

-- TODO rename all the above as the order is flipped

theorem as_field_for_bool_spec {p a} : asPrimitiveSemantics .bool .field p a := by
  resolve_trait
  steps
  simp_all

theorem as_field_for_u8_spec {p a} : asPrimitiveSemantics (.u 8) .field p a := by
  resolve_trait
  steps
  simp_all

theorem as_field_for_u16_spec {p a} : asPrimitiveSemantics (.u 16) .field p a := by
  resolve_trait
  steps
  simp_all

theorem as_field_for_u32_spec {p a} : asPrimitiveSemantics (.u 32) .field p a := by
  resolve_trait
  steps
  simp_all

theorem as_field_for_u64_spec {p a} : asPrimitiveSemantics (.u 64) .field p a := by
  resolve_trait
  steps
  simp_all

theorem as_field_for_u128_spec {p a} : asPrimitiveSemantics (.u 128) .field p a := by
  resolve_trait
  steps
  simp_all

theorem as_u64_for_field_spec {p a} : asPrimitiveSemantics .field (.u 64) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u32_for_field_spec {p a} : asPrimitiveSemantics .field (.u 32) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u16_for_field_spec {p a} : asPrimitiveSemantics .field (.u 16) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u8_for_field_spec {p a} : asPrimitiveSemantics .field (.u 8) p a := by
  resolve_trait
  steps
  simp_all

theorem as_u128_for_field_spec {p a} : asPrimitiveSemantics .field (.u 128) p a := by
  resolve_trait
  steps
  simp_all

