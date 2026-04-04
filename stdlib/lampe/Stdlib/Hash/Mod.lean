import «std-1.0.0-beta.14».Extracted
import Lampe
import Stdlib.EmbeddedCurveOps

namespace Lampe.Stdlib.Hash

open «std-1.0.0-beta.14»

/-!
Formalization of Noir's `std::hash` module.

## Trait infrastructure

- `Hasher`: stateful hash accumulator (`write`, `finish`)
- `Hash`: types hashable via `hash<H: Hasher>(self, &mut H)`
- `BuildHasher`: factory producing a `Hasher` via `build_hasher(self) -> H`

## Standalone functions

Most wrap opaque builtins: `blake3`, `poseidon2_permutation`, `pedersen_hash[_with_separator]`,
`pedersen_commitment[_with_separator]`, `derive_generators`, `from_field_unsafe`.

## Hash trait impls

Implemented for all primitive types, arrays, vectors, and tuples up to arity 5.
Each primitive impl calls `Hasher::write(state, cast(self))`.
-/

/-! ## BuildHasherDefault -/

/-- Type abbreviation for `BuildHasherDefault<H>`. -/
abbrev buildHasherDefaultTp (H : Tp) : Tp :=
  «std-1.0.0-beta.14::hash::BuildHasherDefault».tp h![H]

/-! ## Standalone hash functions -/

/-- `poseidon2_permutation` applies the Poseidon2 permutation (opaque builtin).
    Precondition: `input.len() == state_len`. -/
theorem poseidon2_permutation_spec {p N input state_len}
    (hlen : state_len = N) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::hash::poseidon2_permutation».call h![N] h![input, state_len])
      (fun _ => True) := by
  sorry

/-- `blake3` computes a BLAKE3 hash (opaque builtin). -/
theorem blake3_spec {p N input} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::hash::blake3».call h![N] h![input])
      (fun _ => True) := by
  sorry

/-- `from_field_unsafe` decomposes a field element into `(lo, hi)` where
    `scalar = lo + 2^128 * hi`, with range checks via `bn254::assert_lt`.
    Returns an `EmbeddedCurveScalar`. -/
theorem from_field_unsafe_spec {p scalar} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::hash::from_field_unsafe».call h![] h![scalar])
      (fun (r : EmbeddedCurveOps.Scalar.denote p) => True) := by
  sorry

/-- `derive_generators` returns Pedersen generators (opaque builtin, constant inputs). -/
theorem derive_generators_spec {p N M domain_sep starting_idx} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::hash::derive_generators».call h![N, M] h![domain_sep, starting_idx])
      (fun _ => True) := by
  sorry

/-- `pedersen_hash` computes a Pedersen hash with separator 0. -/
theorem pedersen_hash_spec {p N input} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::hash::pedersen_hash».call h![N] h![input])
      (fun _ => True) := by
  sorry

/-- `pedersen_hash_with_separator` computes a Pedersen hash with a given separator. -/
theorem pedersen_hash_with_separator_spec {p N input separator} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::hash::pedersen_hash_with_separator».call h![N] h![input, separator])
      (fun _ => True) := by
  sorry

/-- `pedersen_commitment` computes a Pedersen commitment with separator 0. -/
theorem pedersen_commitment_spec {p N input} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::hash::pedersen_commitment».call h![N] h![input])
      (fun _ => True) := by
  sorry

/-- `pedersen_commitment_with_separator` computes a Pedersen commitment. -/
theorem pedersen_commitment_with_separator_spec {p N input separator} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::hash::pedersen_commitment_with_separator».call h![N]
        h![input, separator])
      (fun _ => True) := by
  sorry

end Lampe.Stdlib.Hash
