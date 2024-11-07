import Lampe.Hoare.SepTotal
import Lampe.Builtin.BigInt

namespace Lampe.STHoare

theorem bigIntAdd_intro : STHoarePureBuiltin p Γ Builtin.bigIntAdd h![a, b] (a := ()) := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem bigIntSub_intro : STHoarePureBuiltin p Γ Builtin.bigIntSub h![a, b] (a := ()) := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem bigIntMul_intro : STHoarePureBuiltin p Γ Builtin.bigIntMul h![a, b] (a := ()) := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem bigIntDiv_intro : STHoarePureBuiltin p Γ Builtin.bigIntDiv h![a, b] (a := ()) := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem bigIntFromLeBytes_intro : STHoarePureBuiltin p Γ Builtin.bigIntFromLeBytes h![bs, mbs] (a := ()) := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem bigIntToLeBytes_intro {a} :
    STHoare p Γ
      ⟦⟧
      (.call h![] [.bi] (.array (.u 8) 32) (.builtin Builtin.bigIntToLeBytes.inner) h![a])
      (fun v => bitsCanRepresent 256 a ∧ v = (
        (.map (fun n => BitVec.ofNat 8 n)
          (Builtin.listToVec (decomposeToRadix 256 a.toNat (by linarith)) 0))
      )) := by
  apply pureBuiltin_intro_consequence <;> try rfl
  . simp
  . tauto

end Lampe.STHoare
