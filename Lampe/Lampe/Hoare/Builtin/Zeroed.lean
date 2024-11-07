import Lampe.Hoare.SepTotal
import Lampe.Builtin.Zeroed

namespace Lampe.STHoare

theorem zeroed_intro {tp} :
  STHoare p Γ
      ⟦⟧
      (.call h![] [] tp (.builtin .zeroed) h![])
      (fun v => v = (Lampe.Builtin.tpZeroed tp)) := by
  apply pureBuiltin_intro_consequence <;> tauto
  simp

end Lampe.STHoare
