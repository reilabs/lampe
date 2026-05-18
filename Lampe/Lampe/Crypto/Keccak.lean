import Lampe.Tp

/-!
# Keccak-f[1600] — semantic model

Lampe models Noir's `#[foreign(keccakf1600)]` builtin as an opaque
deterministic permutation on a state of 25 `u64` words (FIPS 202).
We do not reimplement the 24-round Keccak permutation in Lean;
downstream proofs treat the model as uninterpreted and trust the
underlying ZK backend.

A concrete Lean 4 implementation is available externally
(`lfglabs-dev/verity/Compiler/Keccak/`) and could be vendored as a
follow-up; see Lampe docs for the audit notes.
-/

namespace Lampe.Crypto.Keccak

/-- Opaque model for the Keccak-f[1600] permutation. -/
opaque keccakF1600 {p : Prime}
    (input : Tp.denote p ((Tp.u 64).array (25 : U 32))) :
    Tp.denote p ((Tp.u 64).array (25 : U 32))

end Lampe.Crypto.Keccak
