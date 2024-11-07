import Lampe.Hoare.SepTotal

namespace Lampe.STHoare

theorem eq_intro : STHoarePureBuiltin p Γ Builtin.eq h![a, b] := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem uLt_intro : STHoarePureBuiltin p Γ Builtin.uLt h![a, b] := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem iLt_intro : STHoarePureBuiltin p Γ Builtin.iLt h![a, b] := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem uGt_intro : STHoarePureBuiltin p Γ Builtin.uGt h![a, b] := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem iGt_intro : STHoarePureBuiltin p Γ Builtin.iGt h![a, b] := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

end Lampe.STHoare
