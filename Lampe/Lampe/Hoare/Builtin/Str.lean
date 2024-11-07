import Lampe.Hoare.SepTotal

namespace Lampe.STHoare

theorem strAsBytes_intro : STHoarePureBuiltin p Γ Builtin.strAsBytes h![s] := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

end Lampe.STHoare
