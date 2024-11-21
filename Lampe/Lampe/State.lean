import Mathlib
import Lampe.ValHeap
import Lampe.Ast

namespace Lampe

abbrev Closures := Finmap fun (_ : Ref) => Function

structure State (p : Prime) where
  vals : ValHeap p
  funcs : Closures

@[reducible]
def mapToValHeapCondition
  (Q : Option (State p × T) → Prop)
  (closures : Closures) : Option (ValHeap p × T) → Prop :=
  fun vv => Q (vv.map fun (vals, v) => ⟨⟨vals, closures⟩, v⟩)

end Lampe
