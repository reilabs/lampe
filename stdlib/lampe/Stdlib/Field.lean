import Lampe

namespace Lampe.Stdlib.Field

set_option Lampe.pp.Expr false
set_option Lampe.pp.STHoare false

lemma val_div_of_dvd {p : Prime} {a b : Fp p} (h : b.val ∣ a.val)
  : ZMod.val (a / b) = a.val / b.val := by
  rcases h with ⟨c, c_def⟩

  have := ZMod.val_lt a
  rw [c_def] at this

  apply_fun (fun a => (a : Fp p)) at c_def
  rw [ZMod.natCast_val, ZMod.cast_id, Nat.cast_mul, ZMod.natCast_val, ZMod.cast_id] at c_def
  cases c_def

  by_cases b = 0
  · simp_all

  have : ZMod.val b ≠ 0 := by simp_all

  have : c < p.natVal := by
    have : c = (ZMod.val b * c) / ZMod.val b := by simp_all
    rw [this]
    apply Nat.div_lt_of_lt_mul
    apply lt_of_lt_of_le (by assumption)
    apply Nat.le_mul_of_pos_left
    apply Nat.zero_lt_of_ne_zero
    assumption

  conv_rhs => rw [ZMod.val_mul_of_lt (by norm_cast; rw [ZMod.val_natCast_of_lt this]; assumption)]
  rw [Nat.mul_div_cancel_left _ (by apply Nat.zero_lt_of_ne_zero; assumption)]
  field_simp
