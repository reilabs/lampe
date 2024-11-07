import Lampe.Hoare.SepTotal

namespace Lampe.STHoare

theorem fApplyRangeConstraint_intro {a w} :
  STHoare p Γ
      ⟦⟧
      (.call h![] [.field, (.u 32)] .unit (.builtin .fApplyRangeConstraint) h![a, w])
      (fun v => v = () ∧ a.val < 2^w.toNat) := by
  apply pureBuiltin_intro_consequence <;> tauto
  simp

theorem fModNumBits_intro {f} :
  STHoare p Γ
      ⟦⟧
      (.call h![] [.field] (.u 64) (.builtin .fModNumBits) h![f])
      (fun v => v = numBits p.val ∧ numBits p.val < 2^64) := by
  apply pureBuiltin_intro_consequence <;> tauto
  simp

theorem fModLeBits_intro {f} :
  STHoare p Γ
      ⟦⟧
      (.call h![] [.field] (.slice (.u 1)) (.builtin .fModLeBits) h![f])
      (fun v => v = decomposeToRadix 2 p.val (by tauto)) := by
  apply pureBuiltin_intro_consequence <;> tauto
  simp

theorem fModBeBits_intro {f} :
  STHoare p Γ
      ⟦⟧
      (.call h![] [.field] (.slice (.u 1)) (.builtin .fModBeBits) h![f])
      (fun v => v = .reverse (decomposeToRadix 2 p.val (by tauto))) := by
  apply pureBuiltin_intro_consequence <;> tauto
  simp

theorem fModLeBytes_intro {f} :
  STHoare p Γ
      ⟦⟧
      (.call h![] [.field] (.slice (.u 8)) (.builtin .fModLeBytes) h![f])
      (fun v => v = decomposeToRadix 256 p.val (by linarith)) := by
  apply pureBuiltin_intro_consequence <;> tauto
  simp

theorem fModBeBytes_intro {f} :
  STHoare p Γ
      ⟦⟧
      (.call h![] [.field] (.slice (.u 8)) (.builtin .fModBeBytes) h![f])
      (fun v => v = .reverse (decomposeToRadix 256 p.val (by linarith))) := by
  apply pureBuiltin_intro_consequence <;> tauto
  simp

theorem uFromField_intro {s f} :
  STHoare p Γ
      ⟦⟧
      (.call h![] [.field] (.u s) (.builtin .uFromField) h![f])
      (fun v => v = BitVec.ofNat s f.val) := by
  apply pureBuiltin_intro_consequence <;> tauto
  simp

theorem iFromField_intro {s f} :
  STHoare p Γ
      ⟦⟧
      (.call h![] [.field] (.i s) (.builtin .iFromField) h![f])
      (fun v => v = BitVec.ofNat s f.val) := by
  apply pureBuiltin_intro_consequence <;> tauto
  simp

end Lampe.STHoare
