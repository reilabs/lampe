import Lampe.Tp
import Mathlib

lemma Finmap.insert_eq_singleton_union [DecidableEq α] {ref : α}:
    m.insert ref v = Finmap.singleton ref v ∪ m := by rfl

@[simp]
lemma Finmap.singleton_disjoint_of_not_mem (hp : ref ∉ s):
    Finmap.Disjoint (Finmap.singleton ref v) s := by
  simp_all [Finmap.Disjoint]

namespace Lampe

def AnyValue (P : Prime) := (tp : Tp) × tp.denote P

abbrev State (P : Prime) := Finmap (fun (_ : Ref) => AnyValue P)

namespace State

end State

end Lampe
