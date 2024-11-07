import Lampe.Hoare.SepTotal

namespace Lampe.STHoare

theorem fApplyRangeConstraint_intro :
  STHoarePureBuiltin p Γ Builtin.fApplyRangeConstraint h![f, c] (a := ()) := by
  apply pureBuiltin_intro_consequence <;> tauto

theorem fModNumBits_intro : STHoarePureBuiltin p Γ Builtin.fModNumBits h![f] (a := ())  := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem fModLeBits_intro : STHoarePureBuiltin p Γ Builtin.fModLeBits h![f] (a := ()) := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem fModBeBits_intro : STHoarePureBuiltin p Γ Builtin.fModLeBits h![f] (a := ()) := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem fModLeBytes_intro : STHoarePureBuiltin p Γ Builtin.fModLeBytes h![f] (a := ()) := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem fModBeBytes_intro : STHoarePureBuiltin p Γ Builtin.fModLeBytes h![f] (a := ()) := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem uFromField_intro : STHoarePureBuiltin p Γ Builtin.uFromField h![f] (a := s) := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem iFromField_intro : STHoarePureBuiltin p Γ Builtin.iFromField h![f] (a := s) := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

end Lampe.STHoare
