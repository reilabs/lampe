import Lampe.Tp
import Lampe.Crypto.Secp256k1

/-!
# ECDSA signature verification — semantic models

Lampe models Noir's `#[foreign(ecdsa_secp256k1)]` and
`#[foreign(ecdsa_secp256r1)]` builtins as deterministic boolean
functions over fixed-length byte arrays.

* `secp256k1Verify` calls into `Lampe.Crypto.Secp256k1.verifyBytes`,
  a computable Lean reference implementation of FIPS 186-4 §6.4.2.
* `secp256r1Verify` remains opaque — secp256r1 (NIST P-256) shares
  the same algorithm but needs its own curve parameters; we can
  concretize it later by reusing the secp256k1 scaffolding.

The Noir builtins also take a `predicate : bool` argument used to gate
the verification under a circuit predicate; the model below ignores it
because semantically the verification result on the `predicate = true`
branch is what matters in proof contexts (Lampe sets `isUnconstrained`
to `false`).
-/

namespace Lampe.Crypto.Ecdsa

/-- Concrete ECDSA verification over secp256k1. -/
def secp256k1Verify {p : Prime}
    (publicKeyX publicKeyY : Tp.denote p ((Tp.u 8).array (32 : U 32)))
    (signature : Tp.denote p ((Tp.u 8).array (64 : U 32)))
    (messageHash : Tp.denote p ((Tp.u 8).array (32 : U 32))) :
    Bool :=
  Lampe.Crypto.Secp256k1.verifyBytes
    publicKeyX.toList.toArray
    publicKeyY.toList.toArray
    signature.toList.toArray
    messageHash.toList.toArray

/-- Opaque model for ECDSA verification over secp256r1. -/
opaque secp256r1Verify {p : Prime}
    (publicKeyX publicKeyY : Tp.denote p ((Tp.u 8).array (32 : U 32)))
    (signature : Tp.denote p ((Tp.u 8).array (64 : U 32)))
    (messageHash : Tp.denote p ((Tp.u 8).array (32 : U 32))) :
    Bool

end Lampe.Crypto.Ecdsa
