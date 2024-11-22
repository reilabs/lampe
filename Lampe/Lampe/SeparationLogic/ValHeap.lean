import Lampe.SeparationLogic.SLH
import Lampe.SeparationLogic.SLP

lemma Finmap.insert_eq_singleton_union [DecidableEq α] {ref : α}:
    m.insert ref v = Finmap.singleton ref v ∪ m := by rfl

@[simp]
lemma Finmap.singleton_disjoint_of_not_mem (hp : ref ∉ s):
    Finmap.Disjoint (Finmap.singleton ref v) s := by
  simp_all [Finmap.Disjoint]

theorem Finmap.union_self [DecidableEq α] {a : Finmap fun _: α => β} :
  a ∪ a = a := by
  sorry

namespace Lampe

def AnyValue (p : Prime) := (tp : Tp) × tp.denote p

abbrev ValHeap (p : Prime) := Finmap (fun (_ : Ref) => AnyValue p)

instance : SLH (ValHeap p) where
  union := fun a b => a ∪ b
  disjoint := fun a b => a.Disjoint b
  empty := ∅
  union_empty := Finmap.union_empty
  union_assoc := Finmap.union_assoc
  disjoint_symm_iff := by tauto
  union_comm_of_disjoint := Finmap.union_comm_of_disjoint
  disjoint_union_left := Finmap.disjoint_union_left
  disjoint_union_right := Finmap.disjoint_union_right
  disjoint_empty := Finmap.disjoint_empty

def ValHeap.singleton (r : Ref) (v : AnyValue p) : SLP (ValHeap p) := fun st => st = Finmap.singleton r v

notation:max "[" l " ↦ " r "]" => ValHeap.singleton l r

end Lampe
