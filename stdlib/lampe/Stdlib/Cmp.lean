import «std-1.0.0-beta.12».Extracted.Cmp
import «std-1.0.0-beta.12».Extracted.«std-1.0.0-beta.12»
import Lampe

namespace Lampe.Stdlib.Cmp

export «std-1.0.0-beta.12».Extracted (
  «std::cmp::Eq».«#genericKinds»
  «std::cmp::Eq».«#associatedTypesKinds»
  «std::cmp::Eq».eq.«#genericKinds»
  «std::cmp::Eq».eq.«#inputs»
  «std::cmp::Eq».eq.«#output»
  «std::cmp::Eq».eq
  «std::cmp::Ord».«#genericKinds»
  «std::cmp::Ord».«#associatedTypesKinds»
  «std::cmp::Ord».cmp.«#genericKinds»
  «std::cmp::Ord».cmp.«#inputs»
  «std::cmp::Ord».cmp.«#output»
  «std::cmp::Ord».cmp
  «std::cmp::Ordering::less»
  «std::cmp::Ordering::equal»
  «std::cmp::Ordering::greater»
  «std::cmp::max»
  «std::cmp::min»
)

open «std-1.0.0-beta.12».Extracted

namespace Eq

theorem field_eq_spec {p a b}
  : STHoare p env ⟦⟧ 
    («std::cmp::Eq».eq h![] .field h![] h![] h![a, b]) 
    fun r: Bool => ⟦r ↔ a = b⟧ := by
  resolve_trait
  steps
  simp_all

theorem u128_eq_spec {p a b}
  : STHoare p env ⟦⟧
    («std::cmp::Eq».eq h![] (.u 128) h![] h![] h![a, b])
    (fun r : Bool => r ↔ a = b) := by
  resolve_trait
  steps
  simp_all

theorem u64_eq_spec {p a b}
  : STHoare p env ⟦⟧
    («std::cmp::Eq».eq h![] (.u 64) h![] h![] h![a, b])
    (fun r : Bool => r ↔ a = b) := by
  resolve_trait
  steps
  simp_all

theorem u32_eq_spec {p a b}
  : STHoare p env ⟦⟧
    («std::cmp::Eq».eq h![] (.u 32) h![] h![] h![a, b])
    (fun r : Bool => r ↔ a = b) := by
  resolve_trait
  steps
  simp_all

theorem u16_eq_spec {p a b}
  : STHoare p env ⟦⟧
    («std::cmp::Eq».eq h![] (.u 16) h![] h![] h![a, b])
    (fun r : Bool => r ↔ a = b) := by
  resolve_trait
  steps
  simp_all

theorem u8_eq_spec {p a b}
  : STHoare p env ⟦⟧ 
    («std::cmp::Eq».eq h![] (.u 8) h![] h![] h![a, b]) 
    fun r : Bool => ⟦r ↔ a = b⟧ := by
  resolve_trait
  steps
  simp_all

theorem u1_eq_spec {p a b}
  : STHoare p env ⟦⟧ 
    («std::cmp::Eq».eq h![] (.u 1) h![] h![] h![a, b]) 
    fun r : Bool => ⟦r ↔ a = b⟧ := by
  resolve_trait
  steps
  simp_all

theorem i8_eq_spec {p a b}
  : STHoare p env ⟦⟧
    («std::cmp::Eq».eq h![] (.i 8) h![] h![] h![a, b])
    fun r : Bool => ⟦r ↔ a = b⟧ := by
  resolve_trait
  steps
  simp_all

theorem i16_eq_spec {p a b}
  : STHoare p env ⟦⟧
    («std::cmp::Eq».eq h![] (.i 16) h![] h![] h![a, b])
    fun r : Bool => ⟦r ↔ a = b⟧ := by
  resolve_trait
  steps
  simp_all

theorem i32_eq_spec {p a b}
  : STHoare p env ⟦⟧
    («std::cmp::Eq».eq h![] (.i 32) h![] h![] h![a, b])
    fun r : Bool => ⟦r ↔ a = b⟧ := by
  resolve_trait
  steps
  simp_all

theorem i64_eq_spec {p a b}
  : STHoare p env ⟦⟧
    («std::cmp::Eq».eq h![] (.i 64) h![] h![] h![a, b])
    fun r : Bool => ⟦r ↔ a = b⟧ := by
  resolve_trait
  steps
  simp_all

theorem unit_eq_spec {p a b}
  : STHoare p env ⟦⟧
    («std::cmp::Eq».eq h![] (.unit) h![] h![] h![a, b])
    fun r : Bool => ⟦r ↔ a = b⟧ := by
  resolve_trait
  steps
  simp_all

theorem bool_eq_spec {p a b}
  : STHoare p env ⟦⟧
    («std::cmp::Eq».eq h![] (.bool) h![] h![] h![a, b])
    fun r : Bool => ⟦r ↔ a = b⟧ := by
  resolve_trait
  steps
  · simp_all
  · exact ()

theorem array_eq_pure_spec {p T N a b}
    {t_eq : «std::cmp::Eq».hasImpl env h![] T}
    {t_eq_f : ∀a b, STHoare p env ⟦⟧
      («std::cmp::Eq».eq h![] T h![] h![] h![a, b])
      (fun r : Bool => ⟦r ↔ a = b⟧)}
  : STHoare p env ⟦⟧
    («std::cmp::Eq».eq h![] (T.array N) h![] h![] h![a, b])
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
    (h_trait_res : «std::cmp::Eq».hasImpl env h![] T)
    (h_eq_child: ∀a b, STHoare p env ⟦⟧ 
      («std::cmp::Eq».eq h![] T h![] h![] h![a, b]) 
      fun r : Bool => ⟦r ↔ a = b⟧)
  : STHoare p env ⟦⟧ 
    («std::cmp::Eq».eq h![] T.slice h![] h![] h![a, b]) 
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
    {u8_eq : «std::cmp::Eq».hasImpl env h![] (.u 8)}
  : STHoare p env ⟦⟧
    («std::cmp::Eq».eq h![] (.str N) h![] h![] h![a, b])
    (fun r : Bool => ⟦r ↔ a = b⟧) := by
  resolve_trait
  steps [array_eq_pure_spec (t_eq := u8_eq) (t_eq_f := fun _ _ => u8_eq_spec)]
  simp_all only [BitVec.natCast_eq_ofNat, List.Vector.mk_toList]

theorem tuple2_eq_pure_spec {p A B self other}
    {A_eq : «std::cmp::Eq».hasImpl env h![] A}
    {B_eq : «std::cmp::Eq».hasImpl env h![] B}
    {A_eq_f : ∀a b, STHoare p env ⟦⟧
      («std::cmp::Eq».eq h![] A h![] h![] h![a, b])
      (fun r : Bool => ⟦r ↔ a = b⟧)}
    {B_eq_f : ∀a b, STHoare p env ⟦⟧
      («std::cmp::Eq».eq h![] B h![] h![] h![a, b])
      (fun r : Bool => ⟦r ↔ a = b⟧)}
  : STHoare p env ⟦⟧
    («std::cmp::Eq».eq h![] (Tp.tuple none [A, B]) h![] h![] h![self, other])
    (fun r : Bool => ⟦r ↔ self = other⟧) := by
  resolve_trait
  steps [A_eq_f, B_eq_f]
  all_goals try exact ()
  subst_vars

  repeat rcases self with ⟨_, self⟩
  repeat rcases other with ⟨_, other⟩

  simp_all

theorem tuple3_eq_pure_spec {p A B C self other}
    {A_eq : «std::cmp::Eq».hasImpl env h![] A}
    {B_eq : «std::cmp::Eq».hasImpl env h![] B}
    {C_eq : «std::cmp::Eq».hasImpl env h![] C}
    {A_eq_f : ∀a b, STHoare p env ⟦⟧
      («std::cmp::Eq».eq h![] A h![] h![] h![a, b])
      (fun r : Bool => ⟦r ↔ a = b⟧)}
    {B_eq_f : ∀a b, STHoare p env ⟦⟧
      («std::cmp::Eq».eq h![] B h![] h![] h![a, b])
      (fun r : Bool => ⟦r ↔ a = b⟧)}
    {C_eq_f : ∀a b, STHoare p env ⟦⟧
      («std::cmp::Eq».eq h![] C h![] h![] h![a, b])
      (fun r : Bool => ⟦r ↔ a = b⟧)}
  : STHoare p env ⟦⟧
    («std::cmp::Eq».eq h![] (Tp.tuple none [A, B, C]) h![] h![] h![self, other])
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
    {A_eq : «std::cmp::Eq».hasImpl env h![] A}
    {B_eq : «std::cmp::Eq».hasImpl env h![] B}
    {C_eq : «std::cmp::Eq».hasImpl env h![] C}
    {D_eq : «std::cmp::Eq».hasImpl env h![] D}
    {A_eq_f : ∀a b, STHoare p env ⟦⟧
      («std::cmp::Eq».eq h![] A h![] h![] h![a, b])
      (fun r : Bool => ⟦r ↔ a = b⟧)}
    {B_eq_f : ∀a b, STHoare p env ⟦⟧
      («std::cmp::Eq».eq h![] B h![] h![] h![a, b])
      (fun r : Bool => ⟦r ↔ a = b⟧)}
    {C_eq_f : ∀a b, STHoare p env ⟦⟧
      («std::cmp::Eq».eq h![] C h![] h![] h![a, b])
      (fun r : Bool => ⟦r ↔ a = b⟧)}
    {D_eq_f : ∀a b, STHoare p env ⟦⟧
      («std::cmp::Eq».eq h![] D h![] h![] h![a, b])
      (fun r : Bool => ⟦r ↔ a = b⟧)}
  : STHoare p env ⟦⟧
    («std::cmp::Eq».eq h![] (Tp.tuple none [A, B, C, D]) h![] h![] h![self, other])
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
    {A_eq : «std::cmp::Eq».hasImpl env h![] A}
    {B_eq : «std::cmp::Eq».hasImpl env h![] B}
    {C_eq : «std::cmp::Eq».hasImpl env h![] C}
    {D_eq : «std::cmp::Eq».hasImpl env h![] D}
    {E_eq : «std::cmp::Eq».hasImpl env h![] E}
    {A_eq_f : ∀a b, STHoare p env ⟦⟧
      («std::cmp::Eq».eq h![] A h![] h![] h![a, b])
      (fun r : Bool => ⟦r ↔ a = b⟧)}
    {B_eq_f : ∀a b, STHoare p env ⟦⟧
      («std::cmp::Eq».eq h![] B h![] h![] h![a, b])
      (fun r : Bool => ⟦r ↔ a = b⟧)}
    {C_eq_f : ∀a b, STHoare p env ⟦⟧
      («std::cmp::Eq».eq h![] C h![] h![] h![a, b])
      (fun r : Bool => ⟦r ↔ a = b⟧)}
    {D_eq_f : ∀a b, STHoare p env ⟦⟧
      («std::cmp::Eq».eq h![] D h![] h![] h![a, b])
      (fun r : Bool => ⟦r ↔ a = b⟧)}
    {E_eq_f : ∀a b, STHoare p env ⟦⟧
      («std::cmp::Eq».eq h![] E h![] h![] h![a, b])
      (fun r : Bool => ⟦r ↔ a = b⟧)}
  : STHoare p env ⟦⟧
    («std::cmp::Eq».eq h![] (Tp.tuple none [A, B, C, D, E]) h![] h![] h![self, other])
    (fun r : Bool => ⟦r ↔ self = other⟧) := by
  resolve_trait
  steps [A_eq_f, B_eq_f, C_eq_f, D_eq_f, E_eq_f]
  all_goals try exact ()
  subst_vars

  repeat rcases self with ⟨_, self⟩
  repeat rcases other with ⟨_, other⟩

  simp_all only [Bool.and_eq_true, Prod.mk.injEq, and_true]
  tauto

theorem ordering_eq_pure_spec {p self other}
  : STHoare p env ⟦⟧
    («std::cmp::Eq».eq h![] («std::cmp::Ordering».tp h![]) h![] h![] h![self, other])
    (fun r : Bool => ⟦r ↔ self = other⟧) := by
  resolve_trait
  steps
  rcases self with ⟨_, ⟨_⟩⟩
  rcases other with ⟨_, ⟨_⟩⟩
  simp_all only [decide_eq_true_eq]
  tauto

end Eq

namespace Ord

/--
Convert a Lean ordering into a Noir `std::cmp::Ordering`.

We recommend providng the user with `std::cmp::Ordering`s at the boundary of the theorem for any
ordering values 'created' by the theorem.
-/
@[reducible]
def fromOrdering {p} : Ordering → («std::cmp::Ordering».tp h![] |>.denote p)
| .lt => (0, ())
| .eq => (1, ())
| .gt => (2, ())

/--
Convert a Noir `std::cmp::Ordering` into a Lean ordering.

We recommend converting user-provided `std::cmp::Ordering`s from the user, and converting them
within the theorem. 

Note that in order to ensure that `toOrdering` is total, 
-/
def toOrdering {p} : («std::cmp::Ordering».tp h![] |>.denote p) → Ordering
| (n, ()) => match (n.cast : ZMod 3) with
  | 0 => .lt
  | 1 => .eq
  | 2 => .gt

theorem less_spec {p} : STHoare p env ⟦⟧
  («std::cmp::Ordering::less».call h![] h![])
  (fun r => r = fromOrdering .lt) := by
  enter_decl
  steps
  subst_vars
  simp

theorem equal_spec {p} : STHoare p env ⟦⟧
  («std::cmp::Ordering::equal».call h![] h![])
  (fun r => r = fromOrdering .eq) := by
  enter_decl
  steps
  subst_vars
  simp

theorem greater_spec {p} : STHoare p env ⟦⟧
  («std::cmp::Ordering::greater».call h![] h![])
  (fun r => r = fromOrdering .gt) := by
  enter_decl
  steps
  subst_vars
  simp

end Ord
