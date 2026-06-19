import Lampe.Builtin.Basic
import Lampe.Crypto.Ecdsa
import Lampe.Data.HList
import Lampe.Data.Field

namespace Lampe.Builtin

def ecdsaSecp256K1 := newTotalPureBuiltin
  ⟨[(Tp.u 8).array (32 : U 32), (Tp.u 8).array (32 : U 32),
    (Tp.u 8).array (64 : U 32), (Tp.u 8).array (32 : U 32), .bool], .bool⟩
  (fun h![pkX, pkY, sig, msg, _predicate] =>
    Crypto.Ecdsa.secp256k1Verify pkX pkY sig msg)

def ecdsaSecp256R1 := newTotalPureBuiltin
  ⟨[(Tp.u 8).array (32 : U 32), (Tp.u 8).array (32 : U 32),
    (Tp.u 8).array (64 : U 32), (Tp.u 8).array (32 : U 32), .bool], .bool⟩
  (fun h![pkX, pkY, sig, msg, _predicate] =>
    Crypto.Ecdsa.secp256r1Verify pkX pkY sig msg)

end Lampe.Builtin
