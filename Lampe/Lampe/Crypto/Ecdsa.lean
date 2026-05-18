import Lampe.Tp
import Lampe.Crypto.Secp256k1
import Lampe.Crypto.Secp256r1

/-!
# ECDSA signature verification — semantic models

Concrete Lean references for Noir's `#[foreign(ecdsa_secp256k1)]` and
`#[foreign(ecdsa_secp256r1)]` builtins. Both forward to the shared
`Lampe.Crypto.Weierstrass.verifyBytes` algorithm parameterized by the
respective curve's `CurveParams` (see `Lampe/Crypto/Secp256k1.lean`
and `Lampe/Crypto/Secp256r1.lean`).

The Noir builtins also take a `predicate : bool` argument used to gate
verification under a circuit predicate; the model below ignores it
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

/-- Concrete ECDSA verification over secp256r1 (NIST P-256). -/
def secp256r1Verify {p : Prime}
    (publicKeyX publicKeyY : Tp.denote p ((Tp.u 8).array (32 : U 32)))
    (signature : Tp.denote p ((Tp.u 8).array (64 : U 32)))
    (messageHash : Tp.denote p ((Tp.u 8).array (32 : U 32))) :
    Bool :=
  Lampe.Crypto.Secp256r1.verifyBytes
    publicKeyX.toList.toArray
    publicKeyY.toList.toArray
    signature.toList.toArray
    messageHash.toList.toArray

end Lampe.Crypto.Ecdsa
