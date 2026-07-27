import Lampe.Builtin.Basic
import Lampe.Crypto.Poseidon2
import Lampe.Data.HList
import Lampe.Data.Field

namespace Lampe.Builtin

/--
Noir's `poseidon2_permutation` foreign builtin for the currently supported width-4 field array.

The cryptographic permutation itself is modeled by `Crypto.Poseidon2.noirPermutation4`; the stdlib
implements and proves the sponge layer around this builtin.
-/
def poseidon2Permutation := newTotalPureBuiltin
  ⟨[.array .field (4 : U 32)], .array .field (4 : U 32)⟩
  (fun h![state] => Crypto.Poseidon2.noirPermutation4 state)

/--
Noir's `poseidon2_config_state_size` foreign builtin.

Lampe models the width-4 (BN254) Poseidon2 configuration, so the state size is
the constant `4`.
-/
def poseidon2ConfigStateSize := newTotalPureBuiltin
  ⟨[], .u 32⟩
  (fun h![] => 4)

end Lampe.Builtin
