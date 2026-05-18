import Lampe.Builtin.Basic
import Lampe.Crypto.Keccak
import Lampe.Data.HList
import Lampe.Data.Field

namespace Lampe.Builtin

/--
Noir's `keccakf1600` foreign builtin. Modeled by the opaque
`Crypto.Keccak.keccakF1600` permutation on 25 `u64` words.
-/
def keccakf1600 := newTotalPureBuiltin
  ⟨[(Tp.u 64).array (25 : U 32)], (Tp.u 64).array (25 : U 32)⟩
  (fun h![input] => Crypto.Keccak.keccakF1600 input)

end Lampe.Builtin
