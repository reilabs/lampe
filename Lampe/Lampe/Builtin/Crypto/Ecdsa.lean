import Lampe.Builtin.Basic
import Lampe.Crypto.Ecdsa
import Lampe.Data.HList
import Lampe.Data.Field

namespace Lampe.Builtin

/--
Noir's `ecdsa_secp256k1` foreign builtin. Modeled by the opaque
`Crypto.Ecdsa.secp256k1Verify`; the trailing `predicate : Bool`
argument from the Noir signature is discarded since the model is
defined only by its inputs.
-/
def ecdsaSecp256K1 := newTotalPureBuiltin
  ⟨[(Tp.u 8).array (32 : U 32), (Tp.u 8).array (32 : U 32),
    (Tp.u 8).array (64 : U 32), (Tp.u 8).array (32 : U 32), .bool], .bool⟩
  (fun h![pkX, pkY, sig, msg, _predicate] =>
    Crypto.Ecdsa.secp256k1Verify pkX pkY sig msg)

/--
Noir's `ecdsa_secp256r1` foreign builtin. Modeled by the opaque
`Crypto.Ecdsa.secp256r1Verify`.
-/
def ecdsaSecp256R1 := newTotalPureBuiltin
  ⟨[(Tp.u 8).array (32 : U 32), (Tp.u 8).array (32 : U 32),
    (Tp.u 8).array (64 : U 32), (Tp.u 8).array (32 : U 32), .bool], .bool⟩
  (fun h![pkX, pkY, sig, msg, _predicate] =>
    Crypto.Ecdsa.secp256r1Verify pkX pkY sig msg)

end Lampe.Builtin
