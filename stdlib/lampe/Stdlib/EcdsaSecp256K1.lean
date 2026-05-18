import «std-1.0.0-beta.14».Extracted
import Lampe

namespace Lampe.Stdlib.EcdsaSecp256K1

open «std-1.0.0-beta.14»

private theorem ecdsaSecp256K1_builtin_spec {p}
    {pkX pkY : Tp.denote p ((Tp.u 8).array (32 : U 32))}
    {sig : Tp.denote p ((Tp.u 8).array (64 : U 32))}
    {msg : Tp.denote p ((Tp.u 8).array (32 : U 32))} :
    STHoare p env ⟦⟧
      (.callBuiltin
        [(Tp.u 8).array (32 : U 32), (Tp.u 8).array (32 : U 32),
         (Tp.u 8).array (64 : U 32), (Tp.u 8).array (32 : U 32), .bool]
        .bool Builtin.ecdsaSecp256K1 h![pkX, pkY, sig, msg, true])
      (fun r => r = Lampe.Crypto.Ecdsa.secp256k1Verify pkX pkY sig msg) := by
  exact STHoare.genericTotalPureBuiltin_intro Builtin.ecdsaSecp256K1 rfl () p env
    h![pkX, pkY, sig, msg, true]

/-- Spec for `ecdsa_secp256k1::verify_signature`: returns the opaque
ECDSA verification result `Crypto.Ecdsa.secp256k1Verify` on the four
byte-array inputs. The Noir wrapper forwards a hard-coded
`predicate = true` to the foreign builtin, which the model ignores. -/
theorem verify_signature_spec {p}
    {pkX pkY : Tp.denote p ((Tp.u 8).array (32 : U 32))}
    {sig : Tp.denote p ((Tp.u 8).array (64 : U 32))}
    {msg : Tp.denote p ((Tp.u 8).array (32 : U 32))} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::ecdsa_secp256k1::verify_signature».call
        h![] h![pkX, pkY, sig, msg])
      (fun r => r = Lampe.Crypto.Ecdsa.secp256k1Verify pkX pkY sig msg) := by
  enter_decl
  steps [ecdsaSecp256K1_builtin_spec]
  assumption

end Lampe.Stdlib.EcdsaSecp256K1
