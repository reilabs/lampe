import Lampe.Builtin.Basic
import Lampe.Crypto.Blake2s
import Lampe.Data.HList
import Lampe.Data.Field

namespace Lampe.Builtin

/--
Noir's `__blake2s` foreign builtin (generic over input length `N`).
Modeled by the concrete `Crypto.Blake2s.blake2sHash`.
-/
def blake2S := newGenericTotalPureBuiltin
  (fun (N : U 32) => ⟨[(Tp.u 8).array N], (Tp.u 8).array (32 : U 32)⟩)
  (fun _N h![input] => Crypto.Blake2s.blake2sHash input)

end Lampe.Builtin
