import Mathlib.Data.Finmap
import Lampe.SeparationLogic.LawfulHeap
import Lampe.SeparationLogic.SLP
import Lampe.Tp

lemma Finmap.insert_eq_singleton_union [DecidableEq α] {ref : α}:
    m.insert ref v = Finmap.singleton ref v ∪ m := by rfl

@[simp]
lemma Finmap.singleton_disjoint_of_not_mem (hp : ref ∉ s):
    Finmap.Disjoint (Finmap.singleton ref v) s := by
  simp_all [Finmap.Disjoint]

lemma Finmap.singleton_disjoint_iff_not_mem :
    Finmap.Disjoint (Finmap.singleton ref v) s ↔ (ref ∉ s) := by
  simp_all [Finmap.Disjoint]

theorem Finmap.union_self [DecidableEq α] {a : Finmap fun _: α => β} :
  a ∪ a = a := by
  apply Finmap.ext_lookup
  intro x
  cases em (x ∈ a)
  . rw [Finmap.lookup_union_left]
    assumption
  . rw [Finmap.lookup_union_left_of_not_in]
    assumption

namespace Lampe

def AnyValue (p : Prime) := (tp : Tp) × tp.denote p

abbrev ValHeap (p : Prime) := Finmap (fun (_ : Ref) => AnyValue p)

instance : LawfulHeap (ValHeap p) where
  union := fun a b => a ∪ b
  disjoint := fun a b => a.Disjoint b
  empty := ∅
  thm_union_empty := Finmap.union_empty
  thm_union_assoc := Finmap.union_assoc
  thm_disjoint_symm_iff := by tauto
  thm_union_comm_of_disjoint := Finmap.union_comm_of_disjoint
  thm_disjoint_union_left := Finmap.disjoint_union_left
  thm_disjoint_empty := Finmap.disjoint_empty

end Lampe
