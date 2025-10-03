import «std-1.0.0-beta.12».Extracted
import Lampe

import Mathlib.Order.Compare
import Stdlib.Tuple

namespace Lampe.Stdlib.Cmp

open «std-1.0.0-beta.12»
open Lampe.Stdlib

namespace Eq

set_option Lampe.pp.Expr true
set_option Lampe.pp.STHoare true

/-- A shorthand for a call to the `std::cmp::Eq::eq` method. -/
@[reducible]
def eq {p} 
    (generics : HList Kind.denote «std-1.0.0-beta.12::cmp::Eq».«#genericKinds»)
    (Self : Tp)
    (associatedTypes : HList Kind.denote «std-1.0.0-beta.12::cmp::Eq».«#associatedTypesKinds»)
    (fnGenerics : HList Kind.denote «std-1.0.0-beta.12::cmp::Eq».«#genericKinds»)
  : HList (Tp.denote p)
      («std-1.0.0-beta.12::cmp::Eq».eq.«#inputs» generics Self associatedTypes fnGenerics)
  → Expr (Tp.denote p)
      («std-1.0.0-beta.12::cmp::Eq».eq.«#output» generics Self associatedTypes fnGenerics) :=
  «std-1.0.0-beta.12::cmp::Eq».eq generics Self associatedTypes fnGenerics

/-- Asserts that the provided `tp` has an implementation of `std::cmp::Eq` in the environment. -/
@[reducible]
def hasEqImpl (env : Env) (tp : Tp) := «std-1.0.0-beta.12::cmp::Eq».hasImpl env h![] tp

theorem field_eq_spec {p a b}
  : STHoare p env ⟦⟧
    (eq h![] .field h![] h![] h![a, b])
    fun r: Bool => ⟦r ↔ a = b⟧ := by
  resolve_trait
  steps
  simp_all

theorem u128_eq_spec {p a b}
  : STHoare p env ⟦⟧
    (eq h![] (.u 128) h![] h![] h![a, b])
    (fun r : Bool => r ↔ a = b) := by
  resolve_trait
  steps
  simp_all

theorem u64_eq_spec {p a b}
  : STHoare p env ⟦⟧
    (eq h![] (.u 64) h![] h![] h![a, b])
    (fun r : Bool => r ↔ a = b) := by
  resolve_trait
  steps
  simp_all

theorem u32_eq_spec {p a b}
  : STHoare p env ⟦⟧
    (eq h![] (.u 32) h![] h![] h![a, b])
    (fun r : Bool => r ↔ a = b) := by
  resolve_trait
  steps
  simp_all

theorem u16_eq_spec {p a b}
  : STHoare p env ⟦⟧
    (eq h![] (.u 16) h![] h![] h![a, b])
    (fun r : Bool => r ↔ a = b) := by
  resolve_trait
  steps
  simp_all

theorem u8_eq_spec {p a b}
  : STHoare p env ⟦⟧
    (eq h![] (.u 8) h![] h![] h![a, b])
    fun r : Bool => ⟦r ↔ a = b⟧ := by
  resolve_trait
  steps
  simp_all

theorem u1_eq_spec {p a b}
  : STHoare p env ⟦⟧
    (eq h![] (.u 1) h![] h![] h![a, b])
    fun r : Bool => ⟦r ↔ a = b⟧ := by
  resolve_trait
  steps
  simp_all

theorem i8_eq_spec {p a b}
  : STHoare p env ⟦⟧
    (eq h![] (.i 8) h![] h![] h![a, b])
    fun r : Bool => ⟦r ↔ a = b⟧ := by
  resolve_trait
  steps
  simp_all

theorem i16_eq_spec {p a b}
  : STHoare p env ⟦⟧
    (eq h![] (.i 16) h![] h![] h![a, b])
    fun r : Bool => ⟦r ↔ a = b⟧ := by
  resolve_trait
  steps
  simp_all

theorem i32_eq_spec {p a b}
  : STHoare p env ⟦⟧
    (eq h![] (.i 32) h![] h![] h![a, b])
    fun r : Bool => ⟦r ↔ a = b⟧ := by
  resolve_trait
  steps
  simp_all

theorem i64_eq_spec {p a b}
  : STHoare p env ⟦⟧
    (eq h![] (.i 64) h![] h![] h![a, b])
    fun r : Bool => ⟦r ↔ a = b⟧ := by
  resolve_trait
  steps
  simp_all

theorem unit_eq_spec {p a b}
  : STHoare p env ⟦⟧
    (eq h![] (.unit) h![] h![] h![a, b])
    fun r : Bool => ⟦r ↔ a = b⟧ := by
  resolve_trait
  steps
  simp_all

theorem bool_eq_spec {p a b}
  : STHoare p env ⟦⟧
    (eq h![] (.bool) h![] h![] h![a, b])
    fun r : Bool => ⟦r ↔ a = b⟧ := by
  resolve_trait
  steps
  · simp_all
  · exact ()

theorem array_eq_pure_spec {p T N a b}
    {t_eq : hasEqImpl env T}
    {t_eq_f : ∀a b, STHoare p env ⟦⟧ (eq h![] T h![] h![] h![a, b]) (fun r : Bool => ⟦r ↔ a = b⟧)}
  : STHoare p env ⟦⟧
    (eq h![] (T.array N) h![] h![] h![a, b])
    (fun r : Bool => ⟦r ↔ a = b⟧) := by
  resolve_trait
  steps
  loop_inv nat fun i _ _ => ∃∃v, [result ↦ ⟨.bool, v⟩] ⋆ (v = (a.toList.take i = b.toList.take i))
  · sl
    simp only [eq_iff_iff, true_iff]
    norm_cast
  · simp
  · intro i _ _
    steps [t_eq_f]
    rotate_left
    · exact ()

    simp_all only [BitVec.toNat_intCast, Int.reducePow, EuclideanDomain.zero_mod, Int.toNat_zero,
      zero_le, eq_iff_iff, Builtin.instCastTpU, BitVec.natCast_eq_ofNat, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, BitVec.toNat_ofNatLT, Lens.modify, Option.get_some, Bool.and_eq_true]

    simp_all only [Lens.modify, Option.isSome_some]
    conv => rhs; rw [←List.reverse_inj]

    generalize_proofs
    simp only [List.take_succ, List.reverse_append]
    rw [List.getElem?_eq_getElem, List.getElem?_eq_getElem]
    simp only [Option.toList_some, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.cons.injEq, List.reverse_inj]
    tauto

  steps
  simp_all only [BitVec.toNat_intCast, Int.reducePow, EuclideanDomain.zero_mod, Int.toNat_zero,
    BitVec.natCast_eq_ofNat, BitVec.ofNat_toNat, BitVec.setWidth_eq, zero_le, eq_iff_iff]

  have h_a : BitVec.toNat N = a.toList.length := by
    simp

  have h_b : BitVec.toNat N = b.toList.length := by
    simp

  conv =>
    lhs
    congr
    · lhs; rw [h_a]
    · lhs; rw [h_b]

  simp_rw [List.take_length]

  exact Iff.intro (fun eq => List.Vector.eq _ _ eq) (fun eq => congrArg _ eq)

theorem slice_eq_pure_spec {p T a b}
    (h_trait_res : hasEqImpl env T)
    (h_eq_child: ∀a b, STHoare p env ⟦⟧ (eq h![] T h![] h![] h![a, b]) fun r : Bool => ⟦r ↔ a = b⟧)
  : STHoare p env ⟦⟧
    (eq h![] T.slice h![] h![] h![a, b])
    fun r : Bool => ⟦r ↔ a = b⟧ := by
  resolve_trait
  steps
  by_cases a.length = b.length
  · step_as ([result ↦ ⟨Tp.bool, true⟩]) (fun _ => ∃∃v, [result ↦ ⟨.bool, v⟩] ⋆ (v ↔ a = b))
    · simp only [*, decide_true]
    · simp only [*, decide_true]
      apply STHoare.iteTrue_intro
      steps
      loop_inv nat fun i _ _ => ∃∃v, [result ↦ ⟨.bool, v⟩] ⋆ (v = (a.take i = b.take i))
      · sl
        simp
      · simp
      · intro i _ _
        steps [h_eq_child]
        simp_all only [Nat.reducePow, BitVec.toNat_intCast, Int.reducePow, EuclideanDomain.zero_mod,
          Int.toNat_zero, zero_le, eq_iff_iff, Builtin.instCastTpU, BitVec.natCast_eq_ofNat,
          BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.toNat_ofNatLT, List.get_eq_getElem,
          Lens.modify, Option.get_some, Bool.and_eq_true]
        conv => rhs; rw [←List.reverse_inj]
        generalize_proofs
        simp only [List.take_succ, List.reverse_append]
        rw [List.getElem?_eq_getElem, List.getElem?_eq_getElem]
        · simp only [Option.toList_some, List.reverse_cons, List.reverse_nil, List.nil_append,
            List.cons_append, List.cons.injEq, List.reverse_inj]
          tauto
        · exact ()
      steps
      rename List.length _ = _ => hp
      simp_all only [Nat.reducePow, BitVec.toNat_intCast, Int.reducePow, EuclideanDomain.zero_mod,
        Int.toNat_zero, BitVec.toNat_ofNatLT, zero_le, List.take_length, eq_iff_iff]
      rw [←hp]
      simp
    steps
    simp_all
  · step_as (⟦⟧) (fun _ => ⟦⟧)
    · simp only [BitVec.ofNatLT, Nat.reducePow, BitVec.ofFin.injEq, Fin.mk.injEq, *, decide_false]
      apply STHoare.iteFalse_intro
      steps
    simp only [BitVec.ofNatLT, Nat.reducePow, BitVec.ofFin.injEq, Fin.mk.injEq, *, decide_false]
    have : a ≠ b := by
      intro h
      apply_fun List.length at h
      contradiction
    steps
    simp_all

theorem string_eq_pure_spec {p N a b}
    {u8_eq : «std-1.0.0-beta.12::cmp::Eq».hasImpl env h![] (.u 8)}
  : STHoare p env ⟦⟧
    (eq h![] (.str N) h![] h![] h![a, b])
    (fun r : Bool => ⟦r ↔ a = b⟧) := by
  resolve_trait
  steps [array_eq_pure_spec (t_eq := u8_eq) (t_eq_f := fun _ _ => u8_eq_spec)]
  simp_all only [BitVec.natCast_eq_ofNat, List.Vector.mk_toList]

theorem tuple2_eq_pure_spec {p A B self other}
    {A_eq : hasEqImpl env A}
    {B_eq : hasEqImpl env B}
    {A_eq_f : ∀a b, STHoare p env ⟦⟧ (eq h![] A h![] h![] h![a, b]) (fun r : Bool => ⟦r ↔ a = b⟧)}
    {B_eq_f : ∀a b, STHoare p env ⟦⟧ (eq h![] B h![] h![] h![a, b]) (fun r : Bool => ⟦r ↔ a = b⟧)}
  : STHoare p env ⟦⟧
    (eq h![] (Tp.tuple none [A, B]) h![] h![] h![self, other])
    (fun r : Bool => ⟦r ↔ self = other⟧) := by
  resolve_trait
  steps [A_eq_f, B_eq_f]
  all_goals try exact ()
  subst_vars

  repeat rcases self with ⟨_, self⟩
  repeat rcases other with ⟨_, other⟩

  simp_all

theorem tuple3_eq_pure_spec {p A B C self other}
    {A_eq : hasEqImpl env A}
    {B_eq : hasEqImpl env B}
    {C_eq : hasEqImpl env C}
    {A_eq_f : ∀a b, STHoare p env ⟦⟧ (eq h![] A h![] h![] h![a, b]) (fun r : Bool => ⟦r ↔ a = b⟧)}
    {B_eq_f : ∀a b, STHoare p env ⟦⟧ (eq h![] B h![] h![] h![a, b]) (fun r : Bool => ⟦r ↔ a = b⟧)}
    {C_eq_f : ∀a b, STHoare p env ⟦⟧ (eq h![] C h![] h![] h![a, b]) (fun r : Bool => ⟦r ↔ a = b⟧)}
  : STHoare p env ⟦⟧
    (eq h![] (Tp.tuple none [A, B, C]) h![] h![] h![self, other])
    (fun r : Bool => ⟦r ↔ self = other⟧) := by
  resolve_trait
  steps [A_eq_f, B_eq_f, C_eq_f]
  all_goals try exact ()
  subst_vars

  repeat rcases self with ⟨_, self⟩
  repeat rcases other with ⟨_, other⟩

  simp_all only [Bool.and_eq_true, Prod.mk.injEq, and_true]
  tauto

set_option maxHeartbeats 500000 in
theorem tuple4_eq_pure_spec {p A B C D self other}
    {A_eq : hasEqImpl env A}
    {B_eq : hasEqImpl env B}
    {C_eq : hasEqImpl env C}
    {D_eq : hasEqImpl env D}
    {A_eq_f : ∀a b, STHoare p env ⟦⟧ (eq h![] A h![] h![] h![a, b]) (fun r : Bool => ⟦r ↔ a = b⟧)}
    {B_eq_f : ∀a b, STHoare p env ⟦⟧ (eq h![] B h![] h![] h![a, b]) (fun r : Bool => ⟦r ↔ a = b⟧)}
    {C_eq_f : ∀a b, STHoare p env ⟦⟧ (eq h![] C h![] h![] h![a, b]) (fun r : Bool => ⟦r ↔ a = b⟧)}
    {D_eq_f : ∀a b, STHoare p env ⟦⟧ (eq h![] D h![] h![] h![a, b]) (fun r : Bool => ⟦r ↔ a = b⟧)}
  : STHoare p env ⟦⟧
    (eq h![] (Tp.tuple none [A, B, C, D]) h![] h![] h![self, other])
    (fun r : Bool => ⟦r ↔ self = other⟧) := by
  resolve_trait
  steps [A_eq_f, B_eq_f, C_eq_f, D_eq_f]
  all_goals try exact ()
  subst_vars

  repeat rcases self with ⟨_, self⟩
  repeat rcases other with ⟨_, other⟩

  simp_all only [Bool.and_eq_true, Prod.mk.injEq, and_true]
  tauto

set_option maxHeartbeats 1000000 in
theorem tuple5_eq_pure_spec {p A B C D E self other}
    {A_eq : hasEqImpl env A}
    {B_eq : hasEqImpl env B}
    {C_eq : hasEqImpl env C}
    {D_eq : hasEqImpl env D}
    {E_eq : hasEqImpl env E}
    {A_eq_f : ∀a b, STHoare p env ⟦⟧ (eq h![] A h![] h![] h![a, b]) (fun r : Bool => ⟦r ↔ a = b⟧)}
    {B_eq_f : ∀a b, STHoare p env ⟦⟧ (eq h![] B h![] h![] h![a, b]) (fun r : Bool => ⟦r ↔ a = b⟧)}
    {C_eq_f : ∀a b, STHoare p env ⟦⟧ (eq h![] C h![] h![] h![a, b]) (fun r : Bool => ⟦r ↔ a = b⟧)}
    {D_eq_f : ∀a b, STHoare p env ⟦⟧ (eq h![] D h![] h![] h![a, b]) (fun r : Bool => ⟦r ↔ a = b⟧)}
    {E_eq_f : ∀a b, STHoare p env ⟦⟧ (eq h![] E h![] h![] h![a, b]) (fun r : Bool => ⟦r ↔ a = b⟧)}
  : STHoare p env ⟦⟧
    (eq h![] (Tp.tuple none [A, B, C, D, E]) h![] h![] h![self, other])
    (fun r : Bool => ⟦r ↔ self = other⟧) := by
  resolve_trait
  steps [A_eq_f, B_eq_f, C_eq_f, D_eq_f, E_eq_f]
  all_goals try exact ()
  subst_vars

  repeat rcases self with ⟨_, self⟩
  repeat rcases other with ⟨_, other⟩

  simp_all only [Bool.and_eq_true, Prod.mk.injEq, and_true]
  tauto

theorem ordering_eq_spec {p self other}
  : STHoare p env ⟦⟧
    (eq h![] («std-1.0.0-beta.12::cmp::Ordering».tp h![]) h![] h![] h![self, other])
    (fun r : Bool => ⟦r ↔ self = other⟧) := by
  resolve_trait
  steps
  rcases self with ⟨_, ⟨_⟩⟩
  rcases other with ⟨_, ⟨_⟩⟩
  simp_all only [decide_eq_true_eq]
  tauto

end Eq

namespace Ord

set_option Lampe.pp.Expr true
set_option Lampe.pp.STHoare true

abbrev NoirOrdering := «std-1.0.0-beta.12::cmp::Ordering».tp h![]

/-- A shorthand for a call to the `std::cmp::Ord::cmp` method. -/
@[reducible]
def cmp {p}
    (generics : HList Kind.denote «std-1.0.0-beta.12::cmp::Ord».«#genericKinds»)
    (Self : Tp)
    (associatedTypes : HList Kind.denote «std-1.0.0-beta.12::cmp::Ord».«#associatedTypesKinds»)
    (fnGenerics : HList Kind.denote «std-1.0.0-beta.12::cmp::Ord».cmp.«#genericKinds»)
  : HList (Tp.denote p) 
      («std-1.0.0-beta.12::cmp::Ord».cmp.«#inputs» generics Self associatedTypes fnGenerics)
  → Expr (Tp.denote p) 
      («std-1.0.0-beta.12::cmp::Ord».cmp.«#output» generics Self associatedTypes fnGenerics) :=
  «std-1.0.0-beta.12::cmp::Ord».cmp generics Self associatedTypes fnGenerics

/--
Convert a Lean ordering into a Noir `std::cmp::Ordering`.

We recommend providng the user with `std::cmp::Ordering`s at the boundary of the theorem for any
ordering values 'created' by the theorem.
-/
@[reducible]
def fromOrdering {p} : Ordering → (NoirOrdering.denote p)
| .lt => (0, ())
| .eq => (1, ())
| .gt => (2, ())

/--
Convert a Noir `std-1.0.0-beta.12::cmp::Ordering` into a Lean ordering.

We recommend converting user-provided `std-1.0.0-beta.12::cmp::Ordering`s from the user, and
converting them within the theorem.

Note that in order to ensure that `toOrdering` is total,
-/
def toOrdering {p} : (NoirOrdering.denote p) → Ordering
| (n, ()) => match (n.cast : ZMod 3) with
  | 0 => .lt
  | 1 => .eq
  | 2 => .gt

/-- Constructs the type of an embedded function that compares two instances of an arbitrary type. -/
@[reducible]
def ordFuncOf {p} (tp : Tp) := tp.denote p → tp.denote p → Ordering

/-- Asserts that the provided `tp` has an implementation of `std::cmp::Ord` in the environment. -/
@[reducible]
def hasOrdImpl (env : Env) (tp : Tp) := «std-1.0.0-beta.12::cmp::Ord».hasImpl env h![] tp

/--
A shorthand of the pure semantics for calling an embedded function implementing the ordering
comparison between two `tp`s.
-/
@[reducible]
def pureOrdSemantics {p} {tp : Tp} (env : Env) (emb : ordFuncOf tp) (a b : Tp.denote p tp) :=
  STHoare p env ⟦⟧ (cmp h![] tp h![] h![] h![a, b]) (fun r => r = fromOrdering (emb a b))

theorem less_spec {p}
  : STHoare p env ⟦⟧
    («std-1.0.0-beta.12::cmp::Ordering::less».call h![] h![])
    (fun r => r = fromOrdering .lt) := by
  enter_decl
  steps
  subst_vars
  simp

theorem equal_spec {p}
  : STHoare p env ⟦⟧
    («std-1.0.0-beta.12::cmp::Ordering::equal».call h![] h![])
    (fun r => r = fromOrdering .eq) := by
  enter_decl
  steps
  subst_vars
  simp

theorem greater_spec {p}
  : STHoare p env ⟦⟧
    («std-1.0.0-beta.12::cmp::Ordering::greater».call h![] h![])
    (fun r => r = fromOrdering .gt) := by
  enter_decl
  steps
  subst_vars
  simp

theorem u128_ord_spec {p self other}
  : STHoare p env ⟦⟧
    (cmp h![] (.u 128) h![] h![] h![self, other])
    (fun r => r = fromOrdering (compare self other)) := by
  resolve_trait
  steps
  apply STHoare.ite_intro
  · intro
    steps [less_spec]
    subst_vars; congr 1
    simp_all [compare, compareOfLessAndEq]
  · intro
    steps
    apply STHoare.ite_intro
    · intro
      steps [greater_spec]
      subst_vars; congr 1
      simp_all only [decide_eq_false_iff_not, BitVec.not_lt, gt_iff_lt, decide_eq_true_eq, compare,
        compareOfLessAndEq]
      rename_i leq lt

      have h1 : ¬(self = other) := by
        by_contra! h
        subst h
        simp_all only [BitVec.le_refl, BitVec.lt_irrefl]

      have h2 : ¬(self < other) := by simp_all

      simp_all
    · intro
      steps [equal_spec]
      subst_vars; congr 1
      simp_all [compare, compareOfLessAndEq]

      have h1 : self = other := by
        rename_i a b
        apply BitVec.le_antisymm b a

      have h2 : ¬(self < other) := by
        simp_all

      simp_all

theorem u64_ord_spec {p self other}
  : STHoare p env ⟦⟧
    (cmp h![] (.u 64) h![] h![] h![self, other])
    (fun r => r = fromOrdering (compare self other)) := by
  resolve_trait
  steps
  apply STHoare.ite_intro
  · intro
    steps [less_spec]
    subst_vars; congr 1
    simp_all [compare, compareOfLessAndEq]
  · intro
    steps
    apply STHoare.ite_intro
    · intro
      steps [greater_spec]
      subst_vars; congr 1
      simp_all only [decide_eq_false_iff_not, BitVec.not_lt, gt_iff_lt, decide_eq_true_eq, compare,
        compareOfLessAndEq]
      rename_i leq lt

      have h1 : ¬(self = other) := by
        by_contra! h
        subst h
        simp_all only [BitVec.le_refl, BitVec.lt_irrefl]

      have h2 : ¬(self < other) := by simp_all

      simp_all
    · intro
      steps [equal_spec]
      subst_vars; congr 1
      simp_all [compare, compareOfLessAndEq]

      have h1 : self = other := by
        rename_i a b
        apply BitVec.le_antisymm b a

      have h2 : ¬(self < other) := by
        simp_all

      simp_all

theorem u32_ord_spec {p self other}
  : STHoare p env ⟦⟧
    (cmp h![] (.u 32) h![] h![] h![self, other])
    (fun r => r = fromOrdering (compare self other)) := by
  resolve_trait
  steps
  apply STHoare.ite_intro
  · intro
    steps [less_spec]
    subst_vars; congr 1
    simp_all [compare, compareOfLessAndEq]
  · intro
    steps
    apply STHoare.ite_intro
    · intro
      steps [greater_spec]
      subst_vars; congr 1
      simp_all only [decide_eq_false_iff_not, BitVec.not_lt, gt_iff_lt, decide_eq_true_eq, compare,
        compareOfLessAndEq]
      rename_i leq lt

      have h1 : ¬(self = other) := by
        by_contra! h
        subst h
        simp_all only [BitVec.le_refl, BitVec.lt_irrefl]

      have h2 : ¬(self < other) := by simp_all

      simp_all
    · intro
      steps [equal_spec]
      subst_vars; congr 1
      simp_all [compare, compareOfLessAndEq]

      have h1 : self = other := by
        rename_i a b
        apply BitVec.le_antisymm b a

      have h2 : ¬(self < other) := by
        simp_all

      simp_all

theorem u16_ord_spec {p self other}
  : STHoare p env ⟦⟧
    (cmp h![] (.u 16) h![] h![] h![self, other])
    (fun r => r = fromOrdering (compare self other)) := by
  resolve_trait
  steps
  apply STHoare.ite_intro
  · intro
    steps [less_spec]
    subst_vars; congr 1
    simp_all [compare, compareOfLessAndEq]
  · intro
    steps
    apply STHoare.ite_intro
    · intro
      steps [greater_spec]
      subst_vars; congr 1
      simp_all only [decide_eq_false_iff_not, BitVec.not_lt, gt_iff_lt, decide_eq_true_eq, compare,
        compareOfLessAndEq]
      rename_i leq lt

      have h1 : ¬(self = other) := by
        by_contra! h
        subst h
        simp_all only [BitVec.le_refl, BitVec.lt_irrefl]

      have h2 : ¬(self < other) := by simp_all

      simp_all
    · intro
      steps [equal_spec]
      subst_vars; congr 1
      simp_all [compare, compareOfLessAndEq]

      have h1 : self = other := by
        rename_i a b
        apply BitVec.le_antisymm b a

      have h2 : ¬(self < other) := by
        simp_all

      simp_all

theorem u8_ord_spec {p self other}
  : STHoare p env ⟦⟧
    (cmp h![] (.u 8) h![] h![] h![self, other])
    (fun r => r = fromOrdering (compare self other)) := by
  resolve_trait
  steps
  apply STHoare.ite_intro
  · intro
    steps [less_spec]
    subst_vars; congr 1
    simp_all [compare, compareOfLessAndEq]
  · intro
    steps
    apply STHoare.ite_intro
    · intro
      steps [greater_spec]
      subst_vars; congr 1
      simp_all only [decide_eq_false_iff_not, BitVec.not_lt, gt_iff_lt, decide_eq_true_eq, compare,
        compareOfLessAndEq]
      rename_i leq lt

      have h1 : ¬(self = other) := by
        by_contra! h
        subst h
        simp_all only [BitVec.le_refl, BitVec.lt_irrefl]

      have h2 : ¬(self < other) := by simp_all

      simp_all
    · intro
      steps [equal_spec]
      subst_vars; congr 1
      simp_all [compare, compareOfLessAndEq]

      have h1 : self = other := by
        rename_i a b
        apply BitVec.le_antisymm b a

      have h2 : ¬(self < other) := by
        simp_all

      simp_all

theorem i8_ord_spec {p self other}
  : STHoare p env ⟦⟧
    (cmp h![] (.i 8) h![] h![] h![self, other])
    (fun r => r = fromOrdering (compare self other)) := by
  resolve_trait
  steps
  apply STHoare.ite_intro
  · intro
    steps [less_spec]
    subst_vars; congr 1
    simp_all [compare, compareOfLessAndEq]
  · intro
    steps
    apply STHoare.ite_intro
    · intro
      steps [greater_spec]
      subst_vars; congr 1
      simp_all only [decide_eq_false_iff_not, BitVec.not_lt, gt_iff_lt, decide_eq_true_eq, compare,
        compareOfLessAndEq]
      rename_i leq lt

      have h1 : ¬(self = other) := by
        by_contra! h
        subst h
        simp_all only [BitVec.le_refl, BitVec.lt_irrefl]

      have h2 : ¬(self < other) := by simp_all

      simp_all
    · intro
      steps [equal_spec]
      subst_vars; congr 1
      simp_all [compare, compareOfLessAndEq]

      have h1 : self = other := by
        rename_i a b
        apply BitVec.le_antisymm b a

      have h2 : ¬(self < other) := by
        simp_all

      simp_all

theorem i16_ord_spec {p self other}
  : STHoare p env ⟦⟧
    (cmp h![] (.i 16) h![] h![] h![self, other])
    (fun r => r = fromOrdering (compare self other)) := by
  resolve_trait
  steps
  apply STHoare.ite_intro
  · intro
    steps [less_spec]
    subst_vars; congr 1
    simp_all [compare, compareOfLessAndEq]
  · intro
    steps
    apply STHoare.ite_intro
    · intro
      steps [greater_spec]
      subst_vars; congr 1
      simp_all only [decide_eq_false_iff_not, BitVec.not_lt, gt_iff_lt, decide_eq_true_eq, compare,
        compareOfLessAndEq]
      rename_i leq lt

      have h1 : ¬(self = other) := by
        by_contra! h
        subst h
        simp_all only [BitVec.le_refl, BitVec.lt_irrefl]

      have h2 : ¬(self < other) := by simp_all

      simp_all
    · intro
      steps [equal_spec]
      subst_vars; congr 1
      simp_all [compare, compareOfLessAndEq]

      have h1 : self = other := by
        rename_i a b
        apply BitVec.le_antisymm b a

      have h2 : ¬(self < other) := by
        simp_all

      simp_all

theorem i32_ord_spec {p self other}
  : STHoare p env ⟦⟧
    (cmp h![] (.i 32) h![] h![] h![self, other])
    (fun r => r = fromOrdering (compare self other)) := by
  resolve_trait
  steps
  apply STHoare.ite_intro
  · intro
    steps [less_spec]
    subst_vars; congr 1
    simp_all [compare, compareOfLessAndEq]
  · intro
    steps
    apply STHoare.ite_intro
    · intro
      steps [greater_spec]
      subst_vars; congr 1
      simp_all only [decide_eq_false_iff_not, BitVec.not_lt, gt_iff_lt, decide_eq_true_eq, compare,
        compareOfLessAndEq]
      rename_i leq lt

      have h1 : ¬(self = other) := by
        by_contra! h
        subst h
        simp_all only [BitVec.le_refl, BitVec.lt_irrefl]

      have h2 : ¬(self < other) := by simp_all

      simp_all
    · intro
      steps [equal_spec]
      subst_vars; congr 1
      simp_all [compare, compareOfLessAndEq]

      have h1 : self = other := by
        rename_i a b
        apply BitVec.le_antisymm b a

      have h2 : ¬(self < other) := by
        simp_all

      simp_all

theorem i64_ord_spec {p self other}
  : STHoare p env ⟦⟧
    (cmp h![] (.i 64) h![] h![] h![self, other])
    (fun r => r = fromOrdering (compare self other)) := by
  resolve_trait
  steps
  apply STHoare.ite_intro
  · intro
    steps [less_spec]
    subst_vars; congr 1
    simp_all [compare, compareOfLessAndEq]
  · intro
    steps
    apply STHoare.ite_intro
    · intro
      steps [greater_spec]
      subst_vars; congr 1
      simp_all only [decide_eq_false_iff_not, BitVec.not_lt, gt_iff_lt, decide_eq_true_eq, compare,
        compareOfLessAndEq]
      rename_i leq lt

      have h1 : ¬(self = other) := by
        by_contra! h
        subst h
        simp_all only [BitVec.le_refl, BitVec.lt_irrefl]

      have h2 : ¬(self < other) := by simp_all

      simp_all
    · intro
      steps [equal_spec]
      subst_vars; congr 1
      simp_all [compare, compareOfLessAndEq]

      have h1 : self = other := by
        rename_i a b
        apply BitVec.le_antisymm b a

      have h2 : ¬(self < other) := by
        simp_all

      simp_all

theorem unit_ord_spec {p self other}
  : STHoare p env ⟦⟧
    (cmp h![] .unit h![] h![] h![self, other])
    (fun r => r = fromOrdering (.eq)) := by
  resolve_trait
  steps [equal_spec]
  simp_all

theorem bool_ord_spec {p self other}
  : STHoare p env ⟦⟧
    (cmp h![] .bool h![] h![] h![self, other])
    (fun r => r = fromOrdering (compare self other)) := by
  resolve_trait
  steps
  apply STHoare.ite_intro
  · intro
    apply STHoare.ite_intro
    · intro
      steps [equal_spec]
      simp_all
    · intro
      steps [greater_spec]
      subst_vars
      congr
  · intro
    apply STHoare.ite_intro
    · intro
      steps [less_spec]
      subst_vars
      congr
    · intro
      steps [equal_spec]
      subst_vars
      congr

-- TODO Array

-- TODO Slice

theorem tuple2_ord_pure_spec {p A B self other}
    {A_ord : hasOrdImpl env A}
    {B_ord : hasOrdImpl env B}
    {A_ord_emb : ordFuncOf A}
    {B_ord_emb : ordFuncOf B}
    {A_ord_f : ∀a b, pureOrdSemantics env A_ord_emb a b}
    {B_ord_f : ∀a b, pureOrdSemantics env B_ord_emb a b}
  : STHoare p env ⟦⟧
    (cmp h![] (Tp.tuple none [A, B]) h![] h![] h![self, other])
    (fun r => r = fromOrdering (Tuple.compare h![A_ord_emb, B_ord_emb] self other)) := by
  resolve_trait
  cases self
  cases other

  steps [A_ord_f, equal_spec, Eq.ordering_eq_spec]
  · exact ()

  apply STHoare.ite_intro
  · intro
    steps
    simp [Tuple.compare]

    simp_all only [Bool.not_eq_eq_eq_not, Bool.not_true, ne_eq, ite_not, Bool.false_eq_true,
      false_iff]
    rename_i a1 _ b1 _ _ _ _ _ _
    have h : A_ord_emb a1 b1 ≠ .eq := by intro a; simp_all only [not_true_eq_false]
    simp_all

  · intro
    steps [B_ord_f]
  
    simp_all only [Bool.not_eq_eq_eq_not, Bool.not_false, ne_eq, ite_not, iff_true]
    rename_i a1 a2 b1 b2 _ _ _ _

    generalize r : A_ord_emb a1 b1 = res at *
    rename_i cond
    cases h : res
    · subst h
      simp [fromOrdering] at cond
      injection cond with h1
      norm_num at h1
    · cases h : B_ord_emb a2.1 b2.1
      all_goals (simp [Tuple.compare, fromOrdering]; simp_all)
    · subst h
      simp [fromOrdering] at cond
      injection cond with h1
      apply sub_eq_zero_of_eq at h1
      norm_num at h1

theorem tuple3_ord_pure_spec {p A B C self other}
    {A_ord : hasOrdImpl env A}
    {B_ord : hasOrdImpl env B}
    {C_ord : hasOrdImpl env C}
    {A_ord_emb : ordFuncOf A}
    {B_ord_emb : ordFuncOf B}
    {C_ord_emb : ordFuncOf C}
    {A_ord_f : ∀a b, pureOrdSemantics env A_ord_emb a b}
    {B_ord_f : ∀a b, pureOrdSemantics env B_ord_emb a b}
    {C_ord_f : ∀a b, pureOrdSemantics env C_ord_emb a b}
  : STHoare p env ⟦⟧
    (cmp h![] (Tp.tuple none [A, B, C]) h![] h![] h![self, other])
    (fun r => r = fromOrdering (Tuple.compare h![A_ord_emb, B_ord_emb, C_ord_emb] self other)) := by
  resolve_trait
  steps [A_ord_f, equal_spec, Eq.ordering_eq_spec]
  step_as 
    ([result ↦ ⟨NoirOrdering, fromOrdering $ A_ord_emb self.1 other.1⟩]) 
    (fun _ => [
      result ↦ ⟨NoirOrdering, fromOrdering $ Tuple.compare h![A_ord_emb, B_ord_emb] 
        (Tuple.mk h![self.1, self.2.1]) 
        (Tuple.mk h![other.1, other.2.1])⟩
    ])
  · apply STHoare.ite_intro
    · intro
      steps [B_ord_f]
      simp_all only [true_iff, Lens.modify, Option.get_some, Tuple.mk, Tuple.compare]
      congr
      repeat rw [Tuple.tail_head_eq_snd]
      rename_i equality cond
      repeat rw [Tuple.head_eq_fst] at equality
      
      generalize h1 : A_ord_emb self.1 other.1 = a_res at *
      cases a_res
      · simp [fromOrdering] at equality
        injection equality with fst
        norm_num at fst
      · cases B_ord_emb self.2.1 other.2.1 <;> simp_all
      · simp [fromOrdering] at equality
        injection equality with fst
        apply sub_eq_zero_of_eq at fst
        norm_num at fst

    · intro
      steps
      simp_all only [Bool.false_eq_true, false_iff, Tuple.mk]
      rename_i equality cond
      repeat rw [Tuple.head_eq_fst] at equality
      congr
      unfold Tuple.compare 
      simp only

      generalize A_ord_emb self.1 other.1 = a_res at *
      cases a_res <;> simp_all
  
  steps [Eq.ordering_eq_spec, equal_spec]

  step_as 
    ([result ↦ ⟨NoirOrdering, fromOrdering $ Tuple.compare h![A_ord_emb, B_ord_emb] 
        (Tuple.mk h![self.1, self.2.1]) 
        (Tuple.mk h![other.1, other.2.1])⟩]) 
    (fun _ => [ result ↦ ⟨NoirOrdering, 
      fromOrdering $ Tuple.compare h![A_ord_emb, B_ord_emb, C_ord_emb] self other⟩])
  · apply STHoare.ite_intro
    · intro
      steps [C_ord_f]
      simp_all only [true_iff, Lens.modify, Option.get_some, Tuple.mk, Tuple.compare]
      congr
      repeat rw [Tuple.tail_tail_head_eq_third] at *
      simp_all only [Tuple.mk, Lens.modify]
      rename_i equality cond
      
      generalize A_ord_emb self.1 other.1 = a_res at *
      generalize B_ord_emb self.2.1 other.2.1 = b_res at *
      cases a_res
      · simp [fromOrdering] at equality
        injection equality with fst
        norm_num at fst
      · simp_all
        cases b_res
        · simp [fromOrdering] at equality
          injection equality with fst
          norm_num at fst
        · cases C_ord_emb self.2.2.1 other.2.2.1 <;> simp_all
        · simp [fromOrdering] at equality
          injection equality with fst
          apply sub_eq_zero_of_eq at fst
          norm_num at fst
      · simp [fromOrdering] at equality
        injection equality with fst
        apply sub_eq_zero_of_eq at fst
        norm_num at fst

    · intro
      steps
      simp_all only [Bool.false_eq_true, false_iff, Tuple.mk]
      rename_i equality cond
      repeat rw [Tuple.head_eq_fst] at *
      congr 2

      simp_all only [Tuple.compare]

      generalize A_ord_emb self.1 other.1 = a_res at *
      generalize B_ord_emb self.2.1 other.2.1 = b_res at *

      cases a_res
      · simp_all
      · cases b_res <;> simp_all
      · simp_all

  steps
  subst_vars
  rfl

-- TODO tuple4
-- TODO tuple5

theorem max_pure_spec {p T v1 v2}
    {T_ord : hasOrdImpl env T}
    {T_ord_emb : ordFuncOf T}
    {T_ord_f : ∀a b, pureOrdSemantics env T_ord_emb a b}
  : STHoare p env ⟦⟧
    («std-1.0.0-beta.12::cmp::max».call h![T] h![v1, v2])
    (fun r => r = if T_ord_emb v1 v2 = .gt then v1 else v2) := by
  sorry

theorem min_pure_spec {p T v1 v2}
    {T_ord : hasOrdImpl env T}
    {T_ord_emb : ordFuncOf T}
    {T_ord_f : ∀a b, pureOrdSemantics env T_ord_emb a b}
  : STHoare p env ⟦⟧
    («std-1.0.0-beta.12::cmp::max».call h![T] h![v1, v2])
    (fun r => r = if T_ord_emb v1 v2 = .gt then v2 else v1) := by
  sorry

end Ord
