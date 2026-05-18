import Lampe.Builtin.Basic
import Lampe.Crypto.Blake3
import Lampe.Data.HList
import Lampe.Data.Field

namespace Lampe.Builtin

/--
Noir's `__blake3` foreign builtin (generic over input length `N`).
Modeled by the opaque `Crypto.Blake3.blake3Hash` returning a 32-byte
digest. The Noir wrapper `hash::blake3` adds an
`is_unconstrained`-guarded `static_assert` on `N ≤ 1024`; under
Lampe's `isUnconstrained = false`, that branch collapses away and
the wrapper reduces to a single builtin call.
-/
def blake3 := newGenericTotalPureBuiltin
  (fun (N : U 32) => ⟨[(Tp.u 8).array N], (Tp.u 8).array (32 : U 32)⟩)
  (fun _N h![input] => Crypto.Blake3.blake3Hash input)

end Lampe.Builtin
