import Lampe.Hoare.SepTotal

namespace Lampe.STHoare

theorem uAdd_intro {s a b} :
  STHoare p Γ
      ⟦⟧
      (.call h![] [.u s, .u s] (.u s) (.builtin .uAdd) h![a, b])
      (fun v => v = a + b  ∧ (a.toInt + b.toInt) < 2^s) := by
  apply pureBuiltin_intro_consequence <;> try rfl
  simp

theorem uSub_intro {s a b} :
  STHoare p Γ
      ⟦⟧
      (.call h![] [.u s, .u s] (.u s) (.builtin .uSub) h![a, b])
      (fun v => v = a - b ∧ b ≤ a) := by
  apply pureBuiltin_intro_consequence <;> try rfl
  simp

theorem uMul_intro {s a b} :
  STHoare p Γ
      ⟦⟧
      (.call h![] [.u s, .u s] (.u s) (.builtin .uMul) h![a, b])
      (fun v => v = a * b  ∧ (a.toInt * b.toInt) < 2^s) := by
  apply pureBuiltin_intro_consequence <;> try rfl
  simp

theorem uDiv_intro {s a b} :
  STHoare p Γ
      ⟦⟧
      (.call h![] [.u s, .u s] (.u s) (.builtin .uDiv) h![a, b])
      (fun v => v = a.udiv b ∧ b ≠ 0) := by
  apply pureBuiltin_intro_consequence <;> try rfl
  simp

theorem uRem_intro {s a b} :
  STHoare p Γ
      ⟦⟧
      (.call h![] [.u s, .u s] (.u s) (.builtin .uRem) h![a, b])
      (fun v => v = a % b ∧ b ≠ 0) := by
  apply pureBuiltin_intro_consequence <;> try rfl
  simp

theorem iAdd_intro {s a b} :
  STHoare p Γ
      ⟦⟧
      (.call h![] [.i s, .i s] (.i s) (.builtin .iAdd) h![a, b])
      (fun v => v = a + b ∧ bitsCanRepresent s (a.toInt + b.toInt)) := by
  apply pureBuiltin_intro_consequence <;> try rfl
  simp

theorem iSub_intro {s a b} :
  STHoare p Γ
      ⟦⟧
      (.call h![] [.i s, .i s] (.i s) (.builtin .iSub) h![a, b])
      (fun v => v = a - b ∧ bitsCanRepresent s (a.toInt - b.toInt)) := by
  apply pureBuiltin_intro_consequence <;> try rfl
  simp

theorem iMul_intro {s a b} :
  STHoare p Γ
      ⟦⟧
      (.call h![] [.i s, .i s] (.i s) (.builtin .iMul) h![a, b])
      (fun v => v = a * b ∧ bitsCanRepresent s (a.toInt * b.toInt)) := by
  apply pureBuiltin_intro_consequence <;> try rfl
  simp

theorem iDiv_intro {s a b} :
  STHoare p Γ
      ⟦⟧
      (.call h![] [.i s, .i s] (.i s) (.builtin .iDiv) h![a, b])
      (fun v => v = a.sdiv b ∧ b ≠ 0) := by
  apply pureBuiltin_intro_consequence <;> try rfl
  simp

theorem iRem_intro {s a b} :
  STHoare p Γ
      ⟦⟧
      (.call h![] [.i s, .i s] (.i s) (.builtin .iRem) h![a, b])
      (fun v => v = Builtin.intRem a b ∧ b ≠ 0) := by
  apply pureBuiltin_intro_consequence <;> try rfl
  simp

theorem iNeg_intro {s a} :
  STHoare p Γ
      ⟦⟧
      (.call h![] [.i s] (.i s) (.builtin .iNeg) h![a])
      (fun v => v = -a) := by
  apply pureBuiltin_intro_consequence <;> try rfl
  simp

theorem fAdd_intro {a b} :
  STHoare p Γ
      ⟦⟧
      (.call h![] [.field, .field] (.field) (.builtin .fAdd) h![a, b])
      (fun v => v = a + b) := by
  apply pureBuiltin_intro_consequence <;> tauto
  simp

theorem fSub_intro {a b} :
  STHoare p Γ
      ⟦⟧
      (.call h![] [.field, .field] (.field) (.builtin .fSub) h![a, b])
      (fun v => v = a - b) := by
  apply pureBuiltin_intro_consequence <;> tauto
  simp

theorem fMul_intro {a b} :
  STHoare p Γ
      ⟦⟧
      (.call h![] [.field, .field] (.field) (.builtin .fMul) h![a, b])
      (fun v => v = a * b) := by
  apply pureBuiltin_intro_consequence <;> tauto
  simp

theorem fDiv_intro {a b} :
  STHoare p Γ
      ⟦⟧
      (.call h![] [.field, .field] (.field) (.builtin .fDiv) h![a, b])
      (fun v => v = a / b ∧ b ≠ 0) := by
  apply pureBuiltin_intro_consequence <;> tauto
  simp

theorem fNeg_intro {a} :
  STHoare p Γ
      ⟦⟧
      (.call h![] [.field] (.field) (.builtin .fNeg) h![a])
      (fun v => v = -a) := by
  apply pureBuiltin_intro_consequence <;> tauto
  simp

end Lampe.STHoare
