import Lampe.Builtin.Basic
import Lampe.Crypto.Pedersen
import Lampe.Data.HList
import Lampe.Data.Field

namespace Lampe.Builtin

open Lampe.Crypto.EmbeddedCurve
open Lampe.Crypto.Pedersen

/--
Noir's `derive_pedersen_generators` foreign builtin (Aztec/Barretenberg).

Inputs (per Noir signature):
- `domain_separator_bytes : [u8; M]` — domain separator string
- `starting_index : u32`             — absolute starting index

Output:
- `[EmbeddedCurvePoint; N]` — `N` distinct Grumpkin generator points

Modeled semantically by `Lampe.Crypto.Pedersen.derivePedersenGenerators`,
which exposes determinism and length properties but treats the
underlying hash-to-curve algorithm as opaque. See
`Lampe/Crypto/Pedersen.lean` for the abstraction boundary.

The descriptor is **generic** in the pair `(N, M)` of array sizes,
matching the Noir `#[builtin]` signature `<let N: u32, let M: u32>`.
-/
def derivePedersenGenerators := newGenericTotalPureBuiltin
  (fun (nm : U 32 × U 32) =>
    let N := nm.1
    let M := nm.2
    ⟨[(Tp.u 8).array M, Tp.u 32], pointTp.array N⟩)
  (fun {p} nm h![domainBytes, startIdx] =>
    let N := nm.1
    let M := nm.2
    Lampe.Crypto.Pedersen.derivePedersenGenerators p
      (Lampe.Crypto.Pedersen.bytesToList (M := M) domainBytes)
      startIdx.toNat
      N.toNat)

end Lampe.Builtin
