import Lampe.Builtin.Basic
import Lampe.Crypto.Sha256
import Lampe.Data.HList
import Lampe.Data.Field

namespace Lampe.Builtin

/--
Noir's `__sha256_compression` foreign builtin.

Signature: `(state: [u32; 8], msg: [u32; 16]) → [u32; 8]`.

Semantics: one round of the SHA-256 compression function `F`
(FIPS 180-4 Section 6.2.2). The caller is responsible for SHA-256
padding, length encoding, IV initialisation, and chaining across
multiple blocks — this builtin only updates the chaining state by
absorbing a single pre-parsed message block.

Modeled by the concrete `Crypto.Sha256.compressOne`.

Noir's `std-1.0.0-beta.14` does not currently wrap
`__sha256_compression` in a separate stdlib helper (in contrast to
`__blake3` and `__keccakf1600`, which do have wrapper functions to
spec against). Downstream Lampe proofs reason about this builtin
directly.
-/
def sha256Compression := newTotalPureBuiltin
  ⟨[(Tp.u 32).array (8 : U 32), (Tp.u 32).array (16 : U 32)],
   (Tp.u 32).array (8 : U 32)⟩
  (fun h![state, msg] => Crypto.Sha256.compressOne state msg)

end Lampe.Builtin
