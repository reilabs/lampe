import Lampe.Hoare.SepTotal

namespace Lampe.STHoare

theorem arrayLen_intro : STHoarePureBuiltin p Γ Builtin.arrayLen h![arr] := by
  apply pureBuiltin_intro_consequence <;> try rfl
  tauto

theorem arrayAsSlice_intro : STHoarePureBuiltin p Γ Builtin.arrayAsSlice h![arr] := by
  apply pureBuiltin_intro_consequence <;> try rfl
  tauto

end Lampe.STHoare
