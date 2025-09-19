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

theorem field_eq_spec {a b}:
    STHoare p env ⟦⟧ («std::cmp::Eq».eq h![] .field h![] h![] h![a, b]) fun r: Bool => ⟦r ↔ a = b⟧ := by
  resolve_trait
  steps
  simp_all

theorem u8_eq_spec {a b}:
    STHoare p env ⟦⟧ («std::cmp::Eq».eq h![] (.u 8) h![] h![] h![a, b]) fun r: Bool => ⟦r ↔ a = b⟧ := by
  resolve_trait
  steps
  simp_all

theorem slice_eq_spec {T a b}
    (h_trait_res : TraitResolvable env ({trait := { name := "«std::cmp::Eq»", traitGenericKinds := [], traitGenerics := h![] }, self := T}))
    (h_eq_child: ∀a b, STHoare p env ⟦⟧ («std::cmp::Eq».eq h![] T h![] h![] h![a, b]) fun r: Bool => ⟦r ↔ a = b⟧):
    STHoare p env ⟦⟧ («std::cmp::Eq».eq h![] T.slice h![] h![] h![a, b]) fun r: Bool => ⟦r ↔ a = b⟧ := by
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
-/
def toOrdering {p} : («std::cmp::Ordering».tp h![] |>.denote p) → Ordering
| (n, ()) => match (n.cast : ZMod 3) with -- TODO is this reasonable?
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
