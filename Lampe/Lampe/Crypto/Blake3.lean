import Lampe.Tp

/-!
# BLAKE3 — semantic model

Lampe models Noir's `#[foreign(blake3)]` builtin as an opaque
deterministic function from a length-parametric byte array to a
32-byte digest. We do not reimplement BLAKE3 in Lean; downstream
proofs treat the model as uninterpreted and trust the underlying
ZK backend.

No mature Lean 4 BLAKE3 implementation exists at time of writing
(2026-05); a pure-Lean concrete reference would be greenfield work.
-/

namespace Lampe.Crypto.Blake3

/-- Opaque model for BLAKE3 over a length-`N` byte array, returning a
32-byte digest. -/
opaque blake3Hash {p : Prime} {N : U 32}
    (input : Tp.denote p ((Tp.u 8).array N)) :
    Tp.denote p ((Tp.u 8).array (32 : U 32))

end Lampe.Crypto.Blake3
