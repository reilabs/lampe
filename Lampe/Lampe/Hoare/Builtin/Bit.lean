import Lampe.Hoare.SepTotal

namespace Lampe.STHoare

theorem bNot_intro : STHoarePureBuiltin p Γ Builtin.bNot h![a] (a := ()) := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem bAnd_intro : STHoarePureBuiltin p Γ Builtin.bAnd h![a, b] (a := ()) := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem bOr_intro : STHoarePureBuiltin p Γ Builtin.bOr h![a, b] (a := ()) := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem bXor_intro : STHoarePureBuiltin p Γ Builtin.bXor h![a, b] (a := ()) := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem uNot_intro : STHoarePureBuiltin p Γ Builtin.uNot h![a] := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem uOr_intro : STHoarePureBuiltin p Γ Builtin.uOr h![a, b] := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem uAnd_intro : STHoarePureBuiltin p Γ Builtin.uAnd h![a, b] := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem uXor_intro : STHoarePureBuiltin p Γ Builtin.uXor h![a, b] := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem uShl_intro : STHoarePureBuiltin p Γ Builtin.uShl h![a, b] := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem uShr_intro : STHoarePureBuiltin p Γ Builtin.uShl h![a, b] := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem iNot_intro : STHoarePureBuiltin p Γ Builtin.iNot h![a] := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem iAnd_intro : STHoarePureBuiltin p Γ Builtin.iAnd h![a, b] := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem iOr_intro : STHoarePureBuiltin p Γ Builtin.iOr h![a, b] := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem iXor_intro : STHoarePureBuiltin p Γ Builtin.iXor h![a, b] := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem iShl_intro : STHoarePureBuiltin p Γ Builtin.iShl h![a, b] := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem iShr_intro : STHoarePureBuiltin p Γ Builtin.iShr h![a, b] := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

end Lampe.STHoare
