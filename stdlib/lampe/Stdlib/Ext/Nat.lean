import Mathlib.Tactic

/-!
# Nat Extensions

Mathlib-style extensions for Nat operations.
-/

namespace Nat

theorem mod_sub_add_eq (n i k : Nat) (hi : i ≤ k) (hk : k < n) :
    (n - i + k) % n = k - i := by
  have hin : i ≤ n := le_trans hi (le_of_lt hk)
  have hcalc : n - i + k = n + (k - i) := by
    calc
      n - i + k = n + k - i := by
        symm
        exact Nat.sub_add_comm hin
      _ = n + (k - i) := by
        exact Nat.add_sub_assoc hi n
  calc
    (n - i + k) % n = (n + (k - i)) % n := by
      simp [hcalc]
    _ = ((n % n) + (k - i) % n) % n := by
      simp [Nat.add_mod]
    _ = (k - i) % n := by simp
    _ = k - i := by
      apply Nat.mod_eq_of_lt
      have : k - i ≤ k := Nat.sub_le _ _
      exact lt_of_le_of_lt this hk

end Nat
