import Lampe.Ast
import Lampe.Tp
import Lampe.Semantics
import Lampe.SeparationLogic
import Lampe.Hoare.Total
import Lampe.Hoare.SepTotal

namespace Lampe.STHoare

theorem eq_intro {tp} {a b : tp.denote p} :
  STHoare p Γ
      ⟦⟧
      (.call h![] [tp, tp] .bool (.builtin .eq) h![a, b])
      (fun v => ∃h, v = ((Builtin.tpBEq tp).get h).beq a b) := by
  apply pureBuiltin_intro_consequence <;> try tauto
  intro h
  simp only
  simp_all only [exists_const]

end Lampe.STHoare
