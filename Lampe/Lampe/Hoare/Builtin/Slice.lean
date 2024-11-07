import Lampe.Hoare.SepTotal

namespace Lampe.STHoare

theorem sliceLen_intro : STHoarePureBuiltin p Γ Builtin.sliceLen h![s] := by
  apply pureBuiltin_intro_consequence <;> try rfl
  tauto

theorem sliceIndex_intro : STHoarePureBuiltin p Γ Builtin.sliceIndex h![sl, i] := by
  apply pureBuiltin_intro_consequence <;> try rfl
  tauto

theorem slicePushBack_intro : STHoarePureBuiltin p Γ Builtin.slicePushBack h![sl, e] := by
  apply pureBuiltin_intro_consequence <;> try rfl
  tauto

theorem slicePushFront_intro : STHoarePureBuiltin p Γ Builtin.slicePushFront h![sl, e] := by
  apply pureBuiltin_intro_consequence <;> try rfl
  tauto

theorem sliceInsert_intro : STHoarePureBuiltin p Γ Builtin.sliceInsert h![sl, i, e] := by
  apply pureBuiltin_intro_consequence <;> try rfl
  tauto

theorem slicePopFront_intro : STHoarePureBuiltin p Γ Builtin.slicePopFront h![sl] := by
  apply pureBuiltin_intro_consequence <;> try rfl
  tauto

theorem slicePopBack_intro : STHoarePureBuiltin p Γ Builtin.slicePopBack h![sl] := by
  apply pureBuiltin_intro_consequence <;> try rfl
  tauto

theorem sliceRemove_intro : STHoarePureBuiltin p Γ Builtin.sliceRemove h![sl, i]  := by
  apply pureBuiltin_intro_consequence <;> try rfl
  tauto

end Lampe.STHoare
