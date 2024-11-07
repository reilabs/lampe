import Lampe.Hoare.SepTotal

namespace Lampe.STHoare

theorem arrayLen_intro {tp n} {arr}:
    STHoare p Γ
      ⟦⟧
      (.call h![] [.array tp n] (.u 32) (.builtin .arrayLen) h![arr])
      fun v => v = arr.length ∧ arr.length < 2^32 := by
  apply pureBuiltin_intro_consequence <;> tauto
  simp

theorem arrayAsSlice_intro {tp n} {arr}:
    STHoare p Γ
      ⟦⟧
      (.call h![] [.array tp n] (.slice tp) (.builtin .arrayAsSlice) h![arr])
      fun v => v = arr.toList := by
  apply pureBuiltin_intro_consequence <;> tauto
  simp

end Lampe.STHoare
