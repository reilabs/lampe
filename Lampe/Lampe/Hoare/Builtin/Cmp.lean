import Lampe.Hoare.SepTotal

namespace Lampe.STHoare

theorem eq_intro {tp} {a b} :
  STHoare p Γ
      ⟦⟧
      (.call h![] [tp, tp] .bool (.builtin .eq) h![a, b])
      (fun v => ∃h, v = ((Builtin.tpBEq tp).get h).beq a b) := by
  apply pureBuiltin_intro_consequence <;> tauto
  intro h
  simp only
  simp_all only [exists_const]

theorem uLt_intro {a b} :
  STHoare p Γ
      ⟦⟧
      (.call h![] [.u 32, .u 32] .bool (.builtin .uLt) h![a, b])
      (fun v => v = (a < b)) := by
  apply pureBuiltin_intro_consequence <;> try rfl
  simp

theorem iLt_intro {a b} :
  STHoare p Γ
      ⟦⟧
      (.call h![] [.i 32, .i 32] .bool (.builtin .iLt) h![a, b])
      (fun v => v = (a < b)) := by
  apply pureBuiltin_intro_consequence <;> try rfl
  simp

theorem uGt_intro {a b} :
  STHoare p Γ
      ⟦⟧
      (.call h![] [.u 32, .u 32] .bool (.builtin .uGt) h![a, b])
      (fun v => v = (a > b)) := by
  apply pureBuiltin_intro_consequence <;> try rfl
  simp

theorem iGt_intro {a b} :
  STHoare p Γ
      ⟦⟧
      (.call h![] [.i 32, .i 32] .bool (.builtin .iGt) h![a, b])
      (fun v => v = (a > b)) := by
  apply pureBuiltin_intro_consequence <;> try rfl
  simp

end Lampe.STHoare
