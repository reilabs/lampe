import Lampe.Hoare.SepTotal

namespace Lampe.STHoare

theorem strAsBytes_intro {n s} :
    STHoare p Γ
      ⟦⟧
      (.call h![] [.str n] (.array (.u 8) n) (.builtin .strAsBytes) h![s])
      fun v => ∃h, v = .map (fun u => u.toNat) ⟨s.toList, h⟩ := by
  apply pureBuiltin_intro_consequence <;> tauto
  simp

end Lampe.STHoare
