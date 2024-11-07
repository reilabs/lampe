import Lampe.Hoare.SepTotal
import Lampe.Builtin.Zeroed

namespace Lampe.STHoare

theorem zeroed_intro : STHoarePureBuiltin p Γ Builtin.zeroed h![] (a := tp) := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

end Lampe.STHoare
