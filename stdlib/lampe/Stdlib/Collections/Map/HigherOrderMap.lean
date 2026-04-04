import Stdlib.Collections.Map.Methods
import Stdlib.Collections.BoundedVec.Core

namespace Lampe.Stdlib.Collections.Map

open «std-1.0.0-beta.14»

/-!
Higher-order and iteration method specs for `collections::map::HashMap`.

- `entries_spec`, `keys_spec`, `values_spec`
- `retain_spec`, `iter_values_mut_spec`
- `iter_mut_spec`, `iter_keys_mut_spec`

All specs are stated; proofs require loop invariants over the table array.
-/

/-! ## Table iteration -/

/-- `entries` returns a well-formed `BoundedVec` of key-value pairs from valid slots.
    The internal assert `entries.len() == self._len` succeeds when the map is well-formed. -/
theorem entries_spec {p K V N B self}
    (hwf : wellFormed self) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::collections::map::HashMap::entries».call h![K, V, N, B] h![self])
      (fun r => BoundedVec.wellFormed r ∧
        (BoundedVec.embed r).length = validCount self) := by
  sorry

/-- `keys` returns a well-formed `BoundedVec` of keys from valid slots. -/
theorem keys_spec {p K V N B self}
    (hwf : wellFormed self) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::collections::map::HashMap::keys».call h![K, V, N, B] h![self])
      (fun r => BoundedVec.wellFormed r ∧
        (BoundedVec.embed r).length = validCount self) := by
  sorry

/-- `values` returns a well-formed `BoundedVec` of values from valid slots. -/
theorem values_spec {p K V N B self}
    (hwf : wellFormed self) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::collections::map::HashMap::values».call h![K, V, N, B] h![self])
      (fun r => BoundedVec.wellFormed r ∧
        (BoundedVec.embed r).length = validCount self) := by
  sorry

/-! ## Higher-order mutation -/

/-- `iter_values_mut` applies `f` to each value of a valid slot in-place.
    The result is a well-formed map with the same number of valid entries. -/
theorem iter_values_mut_spec {p K V N B ref m f} :
    STHoare p env
      ([ref ↦ ⟨hmTp K V N B, m⟩])
      («std-1.0.0-beta.14::collections::map::HashMap::iter_values_mut».call h![K, V, N, B]
        h![ref, f])
      (fun _ => ∃∃ m',
        [ref ↦ ⟨hmTp K V N B, m'⟩]) := by
  sorry

/-- `retain` keeps only entries for which `f(key, value)` returns true. -/
theorem retain_spec {p K V N B ref m f} :
    STHoare p env
      ([ref ↦ ⟨hmTp K V N B, m⟩])
      («std-1.0.0-beta.14::collections::map::HashMap::retain».call h![K, V, N, B]
        h![ref, f])
      (fun _ => ∃∃ m',
        [ref ↦ ⟨hmTp K V N B, m'⟩]) := by
  sorry

/-- `iter_mut` rebuilds the map by applying `f` to each (key, value) pair. -/
theorem iter_mut_spec {p K V N B H ref m f} :
    STHoare p env
      ([ref ↦ ⟨hmTp K V N B, m⟩])
      («std-1.0.0-beta.14::collections::map::HashMap::iter_mut».call h![K, V, N, B, H]
        h![ref, f])
      (fun _ => ∃∃ m',
        [ref ↦ ⟨hmTp K V N B, m'⟩]) := by
  sorry

/-- `iter_keys_mut` rebuilds the map by applying `f` to each key, leaving values unchanged. -/
theorem iter_keys_mut_spec {p K V N B H ref m f} :
    STHoare p env
      ([ref ↦ ⟨hmTp K V N B, m⟩])
      («std-1.0.0-beta.14::collections::map::HashMap::iter_keys_mut».call h![K, V, N, B, H]
        h![ref, f])
      (fun _ => ∃∃ m',
        [ref ↦ ⟨hmTp K V N B, m'⟩]) := by
  sorry

end Lampe.Stdlib.Collections.Map
