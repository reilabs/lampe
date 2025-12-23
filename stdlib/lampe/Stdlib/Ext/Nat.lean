import Mathlib.Tactic

/-!
# Nat Extensions

Mathlib-style extensions for Nat operations.
-/

namespace Nat

theorem mod_u32_sub_add_eq (i : Nat) (hi : i ≤ 32) :
    (4294967296 - i + 32) % 4294967296 = 32 - i := by
  have hle : i ≤ 4294967296 := le_trans hi (by decide)
  have hcalc : 4294967296 - i + 32 = 4294967296 + (32 - i) := by
    calc
      4294967296 - i + 32 = 4294967296 + 32 - i := by
        symm
        exact Nat.sub_add_comm hle
      _ = 4294967296 + (32 - i) := by
        exact Nat.add_sub_assoc hi 4294967296
  calc
    (4294967296 - i + 32) % 4294967296 = (4294967296 + (32 - i)) % 4294967296 := by
      simp [hcalc]
    _ = ((4294967296 % 4294967296) + (32 - i) % 4294967296) % 4294967296 := by
      simp [Nat.add_mod]
    _ = (32 - i) % 4294967296 := by simp
    _ = 32 - i := by
      apply Nat.mod_eq_of_lt
      have : 32 - i ≤ 32 := Nat.sub_le _ _
      exact lt_of_le_of_lt this (by decide)

end Nat
