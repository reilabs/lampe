import Lampe.Hoare.SepTotal

namespace Lampe.STHoare

theorem bNot_intro {a} :
    STHoare p Γ
      ⟦⟧
      (.call h![] [.bool] (.bool) (.builtin .bNot) h![a])
      fun v => v = a.not := by
  apply pureBuiltin_intro_consequence <;> tauto
  simp

theorem bAnd_intro {a b} :
    STHoare p Γ
      ⟦⟧
      (.call h![] [.bool, .bool] (.bool) (.builtin .bAnd) h![a, b])
      fun v => v = a.and b := by
  apply pureBuiltin_intro_consequence <;> tauto
  simp

theorem bOr_intro {a b} :
    STHoare p Γ
      ⟦⟧
      (.call h![] [.bool, .bool] (.bool) (.builtin .bOr) h![a, b])
      fun v => v = a.or b := by
  apply pureBuiltin_intro_consequence <;> tauto
  simp

theorem bXor_intro {a b} :
    STHoare p Γ
      ⟦⟧
      (.call h![] [.bool, .bool] (.bool) (.builtin .bXor) h![a, b])
      fun v => v = a.xor b := by
  apply pureBuiltin_intro_consequence <;> tauto
  simp

theorem uNot_intro {s a} :
    STHoare p Γ
      ⟦⟧
      (.call h![] [.u s] (.u s) (.builtin .uNot) h![a])
      fun v => v = a.not := by
  apply pureBuiltin_intro_consequence <;> tauto
  simp

theorem uOr_intro {s a b} :
    STHoare p Γ
      ⟦⟧
      (.call h![] [.u s, .u s] (.u s) (.builtin .uOr) h![a, b])
      fun v => v = a.or b := by
  apply pureBuiltin_intro_consequence <;> tauto
  simp

theorem uAnd_intro {s a b} :
    STHoare p Γ
      ⟦⟧
      (.call h![] [.u s, .u s] (.u s) (.builtin .uAnd) h![a, b])
      fun v => v = a.and b := by
  apply pureBuiltin_intro_consequence <;> tauto
  simp

theorem uXor_intro {s a b} :
    STHoare p Γ
      ⟦⟧
      (.call h![] [.u s, .u s] (.u s) (.builtin .uXor) h![a, b])
      fun v => v = a.xor b := by
  apply pureBuiltin_intro_consequence <;> tauto
  simp

theorem uShl_intro {s a b} :
    STHoare p Γ
      ⟦⟧
      (.call h![] [.u s, .u 8] (.u s) (.builtin .uShl) h![a, b])
      fun v => v = a <<< b := by
  apply pureBuiltin_intro_consequence <;> tauto
  simp

theorem uShr_intro {s a b} :
    STHoare p Γ
      ⟦⟧
      (.call h![] [.u s, .u 8] (.u s) (.builtin .uShr) h![a, b])
      fun v => v = a >>> b := by
  apply pureBuiltin_intro_consequence <;> tauto
  simp

theorem iNot_intro {s a} :
    STHoare p Γ
      ⟦⟧
      (.call h![] [.i s] (.i s) (.builtin .iNot) h![a])
      fun v => v = a.not := by
  apply pureBuiltin_intro_consequence <;> tauto
  simp

theorem iAnd_intro {s a b} :
    STHoare p Γ
      ⟦⟧
      (.call h![] [.i s, .i s] (.i s) (.builtin .iAnd) h![a, b])
      fun v => v = a.and b := by
  apply pureBuiltin_intro_consequence <;> tauto
  simp

theorem iOr_intro {s a b} :
    STHoare p Γ
      ⟦⟧
      (.call h![] [.i s, .i s] (.i s) (.builtin .iOr) h![a, b])
      fun v => v = a.or b := by
  apply pureBuiltin_intro_consequence <;> tauto
  simp

theorem iXor_intro {s a b} :
    STHoare p Γ
      ⟦⟧
      (.call h![] [.i s, .i s] (.i s) (.builtin .iXor) h![a, b])
      fun v => v = a.xor b := by
  apply pureBuiltin_intro_consequence <;> tauto
  simp

theorem iShl_intro {s a b} :
    STHoare p Γ
      ⟦⟧
      (.call h![] [.i s, .u 8] (.i s) (.builtin .iShl) h![a, b])
      fun v => v = a <<< b := by
  apply pureBuiltin_intro_consequence <;> tauto
  simp

theorem iShr_intro {s a b} :
    STHoare p Γ
      ⟦⟧
      (.call h![] [.i s, .u 8] (.i s) (.builtin .iShr) h![a, b])
      fun v => v = a >>> b := by
  apply pureBuiltin_intro_consequence <;> tauto
  simp

end Lampe.STHoare
