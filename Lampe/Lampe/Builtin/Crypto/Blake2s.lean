import Lampe.Builtin.Basic
import Lampe.Crypto.Blake2s
import Lampe.Data.HList
import Lampe.Data.Field

namespace Lampe.Builtin

/--
Noir's `__blake2s` foreign builtin (generic over input length `N`).
Modeled by the concrete `Crypto.Blake2s.blake2sHash`.

Noir's `std-1.0.0-beta.14` does not currently wrap `__blake2s` in a
separate stdlib helper (in contrast to `__blake3` and `__keccakf1600`,
which do have wrapper functions to spec against). Downstream Lampe
proofs reason about this builtin directly.
-/
def blake2S := newGenericTotalPureBuiltin
  (fun (N : U 32) => ⟨[(Tp.u 8).array N], (Tp.u 8).array (32 : U 32)⟩)
  (fun _N h![input] => Crypto.Blake2s.blake2sHash input)

end Lampe.Builtin
