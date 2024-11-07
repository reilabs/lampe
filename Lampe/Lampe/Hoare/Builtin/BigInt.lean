import Lampe.Hoare.SepTotal
import Lampe.Builtin.BigInt

namespace Lampe.STHoare

theorem bigIntAdd_intro {a b} :
    STHoare p Γ
      ⟦⟧
      (.call h![] [.bi, .bi] (.bi) (.builtin .bigIntAdd) h![a, b])
      fun v => v = a + b := by
  apply pureBuiltin_intro_consequence <;> tauto
  simp

theorem bigIntSub_intro {a b} :
    STHoare p Γ
      ⟦⟧
      (.call h![] [.bi, .bi] (.bi) (.builtin .bigIntSub) h![a, b])
      fun v => v = a - b := by
  apply pureBuiltin_intro_consequence <;> tauto
  simp

theorem bigIntMul_intro {a b} :
    STHoare p Γ
      ⟦⟧
      (.call h![] [.bi, .bi] (.bi) (.builtin .bigIntMul) h![a, b])
      fun v => v = a * b := by
  apply pureBuiltin_intro_consequence <;> tauto
  simp

theorem bigIntDiv_intro {a b} :
    STHoare p Γ
      ⟦⟧
      (.call h![] [.bi, .bi] (.bi) (.builtin .bigIntDiv) h![a, b])
      fun v => v = a / b ∧ b ≠ 0 := by
  apply pureBuiltin_intro_consequence <;> tauto
  simp

theorem bigIntFromLeBytes_intro {bs} :
    STHoare p Γ
      ⟦⟧
      (.call h![] [.slice (.u 8), .slice (.u 8)] (.bi) (.builtin .bigIntFromLeBytes) h![bs, bs])
      fun v => v = composeFromRadix 256 (bs.map (fun u => u.toNat)) := by
  apply pureBuiltin_intro_consequence <;> tauto
  simp

theorem bigIntToLeBytes_intro {a} :
    STHoare p Γ
      ⟦⟧
      (.call h![] [.bi] (.array (.u 8) 32) (.builtin .bigIntToLeBytes) h![a])
      (fun v => bitsCanRepresent 256 a ∧ v = (
        (.map (fun n => BitVec.ofNat 8 n)
          (Builtin.listToVec (decomposeToRadix 256 a.toNat (by linarith)) 0))
      )) := by
  apply pureBuiltin_intro_consequence <;> try rfl
  . simp
  . tauto

end Lampe.STHoare
