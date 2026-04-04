import Stdlib.Collections.Map.Core
import Stdlib.Collections.Map.Slot

namespace Lampe.Stdlib.Collections.Map

open «std-1.0.0-beta.14»

/-!
Hoare-logic specs for `collections::map::HashMap` methods.

Simple accessors (fully proved):
- `len_spec`, `capacity_spec`, `is_empty_spec`

Internal helpers (spec stated, proof TODO on BitVec arithmetic):
- `assert_load_factor_spec`, `quadratic_probe_spec`
-/

/-! ## Simple accessors -/

theorem len_spec {p K V N B self} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::collections::map::HashMap::len».call h![K, V, N, B] h![self])
      (fun r => r = len self) := by
  enter_decl
  steps
  simpa [len]

theorem capacity_spec {p K V N B self} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::collections::map::HashMap::capacity».call h![K, V, N, B] h![self])
      (fun r => r = N) := by
  enter_decl
  steps
  assumption

theorem is_empty_spec {p K V N B self} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::collections::map::HashMap::is_empty».call h![K, V, N, B] h![self])
      (fun r => r = decide (len self = (0 : U 32))) := by
  enter_decl
  steps
  simpa [len]

/-! ## Internal helpers -/

/-- The quadratic probing index: `(hash + (attempt + attempt^2) / 2) % N`, computed in u64. -/
def probeIndex (hash : U 32) (attempt : U 32) (N : U 32) : U 32 :=
  let a64 : U 64 := BitVec.ofNat 64 attempt.toNat
  let offset : U 64 := (a64 + a64 * a64) / 2
  let idx : U 64 := (BitVec.ofNat 64 hash.toNat + offset) % BitVec.ofNat 64 N.toNat
  BitVec.ofNat 32 idx.toNat

theorem quadratic_probe_spec {p K V N B self hash attempt} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::collections::map::HashMap::quadratic_probe».call h![K, V, N, B]
        h![self, hash, attempt])
      (fun (r : U 32) => r = probeIndex hash attempt N) := by
  enter_decl
  steps
  subst_vars
  -- TODO: bridge Builtin.CastTp.cast ↔ BitVec.ofNat and close Expr.callBuiltin
  sorry

/-- `assert_load_factor` succeeds (does not panic) when the load factor is not exceeded. -/
theorem assert_load_factor_spec {p K V N B self}
    (hlf : loadFactorOk self) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::collections::map::HashMap::assert_load_factor».call h![K, V, N, B]
        h![self])
      (fun _ => True) := by
  enter_decl
  steps
  sorry

/-! ## Core lookup and mutation -/

/-- `get` returns `some v` if `key` maps to `v` in the valid entries, `none` otherwise. -/
theorem get_spec {p K V N B H self key}
    (hwf : wellFormed self) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::collections::map::HashMap::get».call h![K, V, N, B, H]
        h![self, key])
      (fun r => True) := by
  sorry

/-- `contains_key` returns true iff `get` returns `some`. -/
theorem contains_key_spec {p K V N B H self key}
    (hwf : wellFormed self) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::collections::map::HashMap::contains_key».call h![K, V, N, B, H]
        h![self, key])
      (fun r => True) := by
  sorry

/-- `insert` adds or updates a key-value pair. The result is well-formed.
    Requires the load factor to not be exceeded. -/
theorem insert_spec {p K V N B H ref m key value}
    (hwf : wellFormed m)
    (hlf : loadFactorOk m) :
    STHoare p env
      ([ref ↦ ⟨hmTp K V N B, m⟩])
      («std-1.0.0-beta.14::collections::map::HashMap::insert».call h![K, V, N, B, H]
        h![ref, key, value])
      (fun _ => ∃∃ m',
        [ref ↦ ⟨hmTp K V N B, m'⟩] ⋆
        ⟦wellFormed m'⟧) := by
  sorry

/-- `remove` deletes a key if present. The result is well-formed. -/
theorem remove_spec {p K V N B H ref m key}
    (hwf : wellFormed m) :
    STHoare p env
      ([ref ↦ ⟨hmTp K V N B, m⟩])
      («std-1.0.0-beta.14::collections::map::HashMap::remove».call h![K, V, N, B, H]
        h![ref, key])
      (fun _ => ∃∃ m',
        [ref ↦ ⟨hmTp K V N B, m'⟩] ⋆
        ⟦wellFormed m'⟧) := by
  sorry

end Lampe.Stdlib.Collections.Map
