import Lampe.Tp
import Lampe.Crypto.Secp256k1
import Lampe.Crypto.Secp256r1

/-!
# ECDSA signature verification — semantic models

Lean models for Noir's `#[foreign(ecdsa_secp256k1)]` and
`#[foreign(ecdsa_secp256r1)]` builtins.
-/

namespace Lampe.Crypto.Ecdsa

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
