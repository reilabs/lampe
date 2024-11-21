import Mathlib
import Lampe.ValHeap
import Lampe.Ast

namespace Lampe

abbrev Closures := List Function

structure State (p : Prime) where
  vals : ValHeap p
  cls : Closures

@[reducible]
def mapToValHeapCondition
  (Q : Option (State p × T) → Prop)
  (closures : Closures) : Option (ValHeap p × T) → Prop :=
  fun vv => Q (vv.map fun (vals, v) => ⟨⟨vals, closures⟩, v⟩)

end Lampe
