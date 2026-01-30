import Lampe

/-!
# List.Vector Extensions

Mathlib-style extensions for List.Vector operations.
-/

@[simp] lemma List.Vector.get_eq_getElem (v : List.Vector α n) (i : ℕ) (hi : i < n) :
    List.Vector.get v ⟨i, hi⟩ = v[i] := by
  rfl
