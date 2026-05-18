import Lampe.Tp

/-!
# ECDSA signature verification — semantic models

Lampe models Noir's `#[foreign(ecdsa_secp256k1)]` and
`#[foreign(ecdsa_secp256r1)]` builtins as opaque deterministic boolean
functions. We do not reimplement secp256k1/secp256r1 curve arithmetic
in Lean; downstream proofs treat these models as uninterpreted, and
trust the underlying ZK backend to implement them correctly.

The Noir builtins also take a `predicate : bool` argument used to gate
the verification under a circuit predicate; the model below ignores it
because semantically the verification result on the `predicate = true`
branch is what matters in proof contexts (Lampe sets `isUnconstrained`
to `false`).
-/

namespace Lampe.Crypto.Ecdsa

/-- Opaque model for ECDSA verification over secp256k1. -/
opaque secp256k1Verify {p : Prime}
    (publicKeyX publicKeyY : Tp.denote p ((Tp.u 8).array (32 : U 32)))
    (signature : Tp.denote p ((Tp.u 8).array (64 : U 32)))
    (messageHash : Tp.denote p ((Tp.u 8).array (32 : U 32))) :
    Bool

/-- Opaque model for ECDSA verification over secp256r1. -/
opaque secp256r1Verify {p : Prime}
    (publicKeyX publicKeyY : Tp.denote p ((Tp.u 8).array (32 : U 32)))
    (signature : Tp.denote p ((Tp.u 8).array (64 : U 32)))
    (messageHash : Tp.denote p ((Tp.u 8).array (32 : U 32))) :
    Bool

end Lampe.Crypto.Ecdsa
