import Lampe.Hoare.SepTotal

namespace Lampe.STHoare

theorem uAdd_intro : STHoarePureBuiltin p Γ Builtin.uAdd h![a, b] := by
  apply pureBuiltin_intro_consequence <;> try rfl
  tauto

theorem uSub_intro : STHoarePureBuiltin p Γ Builtin.uSub h![a, b] := by
  apply pureBuiltin_intro_consequence <;> try rfl
  tauto

theorem uMul_intro : STHoarePureBuiltin p Γ Builtin.uAdd h![a, b] := by
  apply pureBuiltin_intro_consequence <;> try rfl
  tauto

theorem uDiv_intro : STHoarePureBuiltin p Γ Builtin.uDiv h![a, b] := by
  apply pureBuiltin_intro_consequence <;> try rfl
  tauto

theorem uRem_intro : STHoarePureBuiltin p Γ Builtin.uRem h![a, b] := by
  apply pureBuiltin_intro_consequence <;> try rfl
  tauto

theorem iAdd_intro : STHoarePureBuiltin p Γ Builtin.iAdd h![a, b] := by
  apply pureBuiltin_intro_consequence <;> try rfl
  tauto

theorem iSub_intro : STHoarePureBuiltin p Γ Builtin.iSub h![a, b] := by
  apply pureBuiltin_intro_consequence <;> try rfl
  tauto

theorem iMul_intro : STHoarePureBuiltin p Γ Builtin.iMul h![a, b] := by
  apply pureBuiltin_intro_consequence <;> try rfl
  tauto

theorem iDiv_intro : STHoarePureBuiltin p Γ Builtin.iDiv h![a, b] := by
  apply pureBuiltin_intro_consequence <;> try rfl
  tauto

theorem iRem_intro : STHoarePureBuiltin p Γ Builtin.iRem h![a, b] := by
  apply pureBuiltin_intro_consequence <;> try rfl
  tauto

theorem iNeg_intro : STHoarePureBuiltin p Γ Builtin.iNeg h![a] := by
  apply pureBuiltin_intro_consequence <;> try rfl
  tauto

theorem fAdd_intro : STHoarePureBuiltin p Γ Builtin.fAdd h![a, b] (a := ()) := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem fSub_intro : STHoarePureBuiltin p Γ Builtin.fSub h![a, b] (a := ()) := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem fMul_intro : STHoarePureBuiltin p Γ Builtin.fMul h![a, b] (a := ()) := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem fDiv_intro : STHoarePureBuiltin p Γ Builtin.fDiv h![a, b] (a := ()) := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem fNeg_intro : STHoarePureBuiltin p Γ Builtin.fNeg h![a] (a := ()) := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

end Lampe.STHoare
