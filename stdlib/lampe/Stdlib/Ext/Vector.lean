import Lampe

/-!
# List.Vector Extensions

Mathlib-style extensions for List.Vector operations.
-/

theorem List.Vector.reverse_map {α β : Type} {d : ℕ} (v : List.Vector α d) (f : α → β) :
    (v.map f).reverse = v.reverse.map f := by
  apply List.Vector.eq
  simp [List.Vector.toList_reverse]
