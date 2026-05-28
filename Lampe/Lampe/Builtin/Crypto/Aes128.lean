import Lampe.Builtin.Basic
import Lampe.Crypto.Aes128
import Lampe.Data.HList
import Lampe.Data.Field

namespace Lampe.Builtin

/--
Noir's `aes128_encrypt` foreign builtin. AES-128-CBC encryption of an
already-padded plaintext, modeled by `Crypto.Aes128.aes128Encrypt`.

The Noir wrapper `std::aes128::aes128_encrypt<N>(input, iv, key)`
applies PKCS#7 padding around this builtin call, so the input length
seen here is always a multiple of 16. Our `Crypto.Aes128.aes128Encrypt`
is defined for arbitrary `N` (truncated/zero-padded back to length `N`
if the input length is not a multiple of 16); the wrapper proof never
exercises that branch.
-/
def aes128Encrypt := newGenericTotalPureBuiltin
  (fun (N : U 32) => ⟨[(Tp.u 8).array N, (Tp.u 8).array (16 : U 32),
    (Tp.u 8).array (16 : U 32)], (Tp.u 8).array N⟩)
  (fun N h![input, iv, key] =>
    Crypto.Aes128.aes128Encrypt (N := N) input iv key)

end Lampe.Builtin
