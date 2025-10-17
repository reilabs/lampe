import «std-1.0.0-beta.12».Extracted

import Lampe
import Stdlib.Tuple

namespace Lampe.Stdlib.Default

open «std-1.0.0-beta.12»
open Lampe.Stdlib

set_option Lampe.pp.Expr true
set_option Lampe.pp.STHoare true

/-- A shorthand for a call to the `std::default::Default::default` method. -/
@[reducible]
def default {p}
    (generics : HList Kind.denote «std-1.0.0-beta.12::default::Default».«#genericKinds»)
    (Self : Tp)
    (associatedTypes : HList Kind.denote «std-1.0.0-beta.12::default::Default».«#associatedTypesKinds»)
    (fnGenerics : HList Kind.denote «std-1.0.0-beta.12::default::Default».default.«#genericKinds»)
  : HList (Tp.denote p)
      («std-1.0.0-beta.12::default::Default».default.«#inputs» generics Self associatedTypes fnGenerics)
  → Expr (Tp.denote p)
      («std-1.0.0-beta.12::default::Default».default.«#output» generics Self associatedTypes fnGenerics) :=
  «std-1.0.0-beta.12::default::Default».default generics Self associatedTypes fnGenerics

/--
Asserts that the provided `tp` has an implementation of `std::default::Default` in the environment.
-/
@[reducible]
def hasDefaultImpl (env : Env) (tp : Tp) := «std-1.0.0-beta.12::default::Default».hasImpl env h![] tp

theorem field_default_spec {p}
  : STHoare p env ⟦⟧
    (default h![] .field h![] h![] h![])
    (fun r => r = 0) := by
  resolve_trait
  steps
  simp_all

theorem u1_default_spec {p}
  : STHoare p env ⟦⟧
    (default h![] (.u 1) h![] h![] h![])
    (fun r => r = 0) := by
  resolve_trait
  steps
  subst_vars
  rfl

theorem u8_default_spec {p}
  : STHoare p env ⟦⟧
    (default h![] (.u 8) h![] h![] h![])
    (fun r => r = 0) := by
  resolve_trait
  steps
  subst_vars
  rfl

theorem u16_default_spec {p}
  : STHoare p env ⟦⟧
    (default h![] (.u 16) h![] h![] h![])
    (fun r => r = 0) := by
  resolve_trait
  steps
  subst_vars
  rfl

theorem u32_default_spec {p}
  : STHoare p env ⟦⟧
    (default h![] (.u 32) h![] h![] h![])
    (fun r => r = 0) := by
  resolve_trait
  steps
  subst_vars
  rfl

theorem u64_default_spec {p}
  : STHoare p env ⟦⟧
    (default h![] (.u 64) h![] h![] h![])
    (fun r => r = 0) := by
  resolve_trait
  steps
  subst_vars
  rfl

theorem u128_default_spec {p}
  : STHoare p env ⟦⟧
    (default h![] (.u 128) h![] h![] h![])
    (fun r => r = 0) := by
  resolve_trait
  steps
  subst_vars
  rfl

theorem i8_default_spec {p}
  : STHoare p env ⟦⟧
    (default h![] (.i 8) h![] h![] h![])
    (fun r => r = 0) := by
  resolve_trait
  steps
  subst_vars
  rfl

theorem i16_default_spec {p}
  : STHoare p env ⟦⟧
    (default h![] (.i 16) h![] h![] h![])
    (fun r => r = 0) := by
  resolve_trait
  steps
  subst_vars
  rfl

theorem i32_default_spec {p}
  : STHoare p env ⟦⟧
    (default h![] (.i 32) h![] h![] h![])
    (fun r => r = 0) := by
  resolve_trait
  steps
  subst_vars
  rfl

theorem i64_default_spec {p}
  : STHoare p env ⟦⟧
    (default h![] (.i 64) h![] h![] h![])
    (fun r => r = 0) := by
  resolve_trait
  steps
  subst_vars
  rfl

theorem unit_default_spec {p}
  : STHoare p env ⟦⟧
    (default h![] .unit h![] h![] h![])
    (fun r => r = 0) := by
  resolve_trait
  steps

theorem bool_default_spec {p}
  : STHoare p env ⟦⟧
    (default h![] .bool h![] h![] h![])
    (fun r => r = false) := by
  resolve_trait
  steps
  simp_all

theorem array_default_spec {p T N}
    {t_default : hasDefaultImpl env T}
    (t_default_emb : T.denote p)
    (t_default_f : STHoare p env ⟦⟧
      (default h![] T h![] h![] h![])
      (fun r => r = t_default_emb))
  : STHoare p env ⟦⟧
    (default h![] (T.array N) h![] h![] h![])
    (fun r => r = List.Vector.replicate N.toNat t_default_emb) := by
  resolve_trait
  steps [t_default_f]
  simp_all

theorem slice_default_spec {p}
    {T : Tp}
  : STHoare p env ⟦⟧
    (default h![] T.slice h![] h![] h![])
    (fun r => r = []) := by
  resolve_trait
  steps
  simp_all

theorem tuple2_default_spec {p A B}
    {a_default : hasDefaultImpl env A}
    (a_emb : A.denote p)
    (a_sem : STHoare p env ⟦⟧
      (default h![] A h![] h![] h![])
      (fun r => r = a_emb))
    {b_default : hasDefaultImpl env B}
    (b_emb : B.denote p)
    (b_sem : STHoare p env ⟦⟧
      (default h![] B h![] h![] h![])
      (fun r => r = b_emb))
  : STHoare p env ⟦⟧
    (default h![] (Tp.tuple none [A, B]) h![] h![] h![])
    (fun r => r = Tuple.mk h![a_emb, b_emb]) := by
  resolve_trait
  steps [a_sem, b_sem]
  simp_all

theorem tuple3_default_spec {p A B C}
    {a_default : hasDefaultImpl env A}
    (a_emb : A.denote p)
    (a_sem : STHoare p env ⟦⟧
      (default h![] A h![] h![] h![])
      (fun r => r = a_emb))
    {b_default : hasDefaultImpl env B}
    (b_emb : B.denote p)
    (b_sem : STHoare p env ⟦⟧
      (default h![] B h![] h![] h![])
      (fun r => r = b_emb))
    {c_default : hasDefaultImpl env C}
    (c_emb : C.denote p)
    (c_sem : STHoare p env ⟦⟧
      (default h![] C h![] h![] h![])
      (fun r => r = c_emb))
  : STHoare p env ⟦⟧
    (default h![] (Tp.tuple none [A, B, C]) h![] h![] h![])
    (fun r => r = Tuple.mk h![a_emb, b_emb, c_emb]) := by
  resolve_trait
  steps [a_sem, b_sem, c_sem]
  simp_all

theorem tuple4_default_spec {p A B C D}
    {a_default : hasDefaultImpl env A}
    (a_emb : A.denote p)
    (a_sem : STHoare p env ⟦⟧
      (default h![] A h![] h![] h![])
      (fun r => r = a_emb))
    {b_default : hasDefaultImpl env B}
    (b_emb : B.denote p)
    (b_sem : STHoare p env ⟦⟧
      (default h![] B h![] h![] h![])
      (fun r => r = b_emb))
    {c_default : hasDefaultImpl env C}
    (c_emb : C.denote p)
    (c_sem : STHoare p env ⟦⟧
      (default h![] C h![] h![] h![])
      (fun r => r = c_emb))
    {d_default : hasDefaultImpl env D}
    (d_emb : D.denote p)
    (d_sem : STHoare p env ⟦⟧
      (default h![] D h![] h![] h![])
      (fun r => r = d_emb))
  : STHoare p env ⟦⟧
    (default h![] (Tp.tuple none [A, B, C, D]) h![] h![] h![])
    (fun r => r = Tuple.mk h![a_emb, b_emb, c_emb, d_emb]) := by
  resolve_trait
  steps [a_sem, b_sem, c_sem, d_sem]
  simp_all

theorem tuple5_default_spec {p A B C D E}
    {a_default : hasDefaultImpl env A}
    (a_emb : A.denote p)
    (a_sem : STHoare p env ⟦⟧
      (default h![] A h![] h![] h![])
      (fun r => r = a_emb))
    {b_default : hasDefaultImpl env B}
    (b_emb : B.denote p)
    (b_sem : STHoare p env ⟦⟧
      (default h![] B h![] h![] h![])
      (fun r => r = b_emb))
    {c_default : hasDefaultImpl env C}
    (c_emb : C.denote p)
    (c_sem : STHoare p env ⟦⟧
      (default h![] C h![] h![] h![])
      (fun r => r = c_emb))
    {d_default : hasDefaultImpl env D}
    (d_emb : D.denote p)
    (d_sem : STHoare p env ⟦⟧
      (default h![] D h![] h![] h![])
      (fun r => r = d_emb))
    {e_default : hasDefaultImpl env E}
    (e_emb : E.denote p)
    (e_sem : STHoare p env ⟦⟧
      (default h![] E h![] h![] h![])
      (fun r => r = e_emb))
  : STHoare p env ⟦⟧
    (default h![] (Tp.tuple none [A, B, C, D, E]) h![] h![] h![])
    (fun r => r = Tuple.mk h![a_emb, b_emb, c_emb, d_emb, e_emb]) := by
  resolve_trait
  steps [a_sem, b_sem, c_sem, d_sem, e_sem]
  simp_all

