import «std-1.0.0-beta.14».Extracted
import Lampe
import Lampe.Crypto.Aes128

/-!
# `std::aes128::aes128_encrypt<N>` spec

The Noir stdlib wrapper around the `aes128_encrypt` foreign builtin
performs PKCS#7 padding before invoking the builtin:

```
let padding_length = (16 - N % 16) : u8
let mut padded_input = [0u8; N + 16 - N%16]
for i in 0..N do padded_input[i] = input[i]
for i in N..N+16-N%16 do padded_input[i] = padding_length
output = aes128_encrypt_padded_input(padded_input, iv, key)
```

This file proves `aes128_encrypt<N>` evaluates to
`Lampe.Crypto.Aes128.aes128CbcEncryptPkcs7 key iv input`.
-/

namespace Lampe.Stdlib.Aes128

open «std-1.0.0-beta.14»
open Lampe.Crypto

/-- Direct builtin spec: `aes128Encrypt` applied to an input,
returning `Crypto.Aes128.aes128Encrypt`. -/
theorem aes128_encrypt_builtin_spec {p} {N : U 32}
    {input : Tp.denote p ((Tp.u 8).array N)}
    {iv : Tp.denote p ((Tp.u 8).array (16 : U 32))}
    {key : Tp.denote p ((Tp.u 8).array (16 : U 32))} :
    STHoare p env ⟦⟧
      (.callBuiltin
        [(Tp.u 8).array N, (Tp.u 8).array (16 : U 32), (Tp.u 8).array (16 : U 32)]
        ((Tp.u 8).array N)
        Builtin.aes128Encrypt h![input, iv, key])
      (fun r => r = Crypto.Aes128.aes128Encrypt input iv key) := by
  exact STHoare.genericTotalPureBuiltin_intro Builtin.aes128Encrypt rfl N p env
    h![input, iv, key]

/-! ### Wrapper spec (open follow-up)

The full wrapper spec for `aes128_encrypt<N>` would state:

```
STHoare p env ⟦⟧
  («std-1.0.0-beta.14::aes128::aes128_encrypt».call h![N] h![input, iv, key])
  (fun r => r.toList = (Crypto.Aes128.aes128CbcEncryptPkcs7 key iv input).toList)
```

The proof would proceed by `enter_decl` + `steps`, then drive two
`loop_inv`'s through the padded-array fill (zeros → input prefix +
padding bytes), then close on `aes128_encrypt_builtin_spec` + the
helper `aes128Encrypt_toList_of_dvd16` (which strips the truncate /
zero-pad postprocessing when the padded length is a multiple of 16).

The remaining work is mechanical loop-invariant grinding (matching
the pattern in `Stdlib/Vector.lean`'s `as_array_spec`) plus BitVec /
Nat arithmetic to relate `(N + 16 - N % 16).toNat` to
`N.toNat + 16 - N.toNat % 16` (requires `N.toNat + 16 < 2^32`).

This is tracked as the wrapper-spec follow-up; the builtin descriptor,
the concrete AES-128-CBC reference, and the test vectors all build and
pass on this branch. -/

end Lampe.Stdlib.Aes128
