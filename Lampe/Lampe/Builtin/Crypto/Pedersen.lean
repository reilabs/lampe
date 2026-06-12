import Lampe.Builtin.Basic
import Lampe.Crypto.Pedersen
import Lampe.Data.HList
import Lampe.Data.Field

namespace Lampe.Builtin

open Lampe.Crypto.EmbeddedCurve
open Lampe.Crypto.Pedersen

/-- Convert a length-`M` byte vector to the `List (BitVec 8)` used as
the opaque domain-separator key by `derivePedersenGenerators`. -/
def bytesToList {p M} (bs : Tp.denote p ((Tp.u 8).array M)) : List (BitVec 8) :=
  bs.toList

/--
Noir's `derive_pedersen_generators` foreign builtin, generic in the
pair `(N, M)` of array sizes per the Noir signature
`<let N: u32, let M: u32>`.

Inputs:
- `domain_separator_bytes : [u8; M]` — domain separator string
- `starting_index : u32`             — absolute starting index

Output:
- `[EmbeddedCurvePoint; N]` — `N` distinct Grumpkin generator points

Modeled by the concrete BLAKE3-driven hash-to-curve construction in
`Lampe.Crypto.Pedersen.derivePedersenGenerators` (see that file for the
construction; it transcribes the standard `derive_generators` algorithm
that any Noir backend must implement).
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
      (bytesToList (M := M) domainBytes)
      startIdx.toNat
      N.toNat)

end Lampe.Builtin
