import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Decidability instances on Mathlib's affine elliptic-curve `Point`

Mathlib does not ship decidable instances for `Equation`,
`Nonsingular`, or equality on `WeierstrassCurve.Affine.Point`.
Filling them in unlocks `native_decide` over any curve point.
-/

namespace Lampe.Crypto

variable {F : Type} [Field F] [DecidableEq F] {W : WeierstrassCurve.Affine F}

instance affineEquation_decidable (x y : F) : Decidable (W.Equation x y) :=
  decidable_of_iff _ (WeierstrassCurve.Affine.equation_iff' (W := W) x y).symm

instance affineNonsingular_decidable (x y : F) : Decidable (W.Nonsingular x y) :=
  decidable_of_iff _ (WeierstrassCurve.Affine.nonsingular_iff' (W := W) x y).symm

instance affinePoint_decidableEq : DecidableEq W.Point := fun p q =>
  match p, q with
  | .zero, .zero => isTrue rfl
  | .zero, @WeierstrassCurve.Affine.Point.some _ _ _ _ _ _ =>
      isFalse (by intro h; cases h)
  | @WeierstrassCurve.Affine.Point.some _ _ _ _ _ _, .zero =>
      isFalse (by intro h; cases h)
  | @WeierstrassCurve.Affine.Point.some _ _ _ x₁ y₁ _,
    @WeierstrassCurve.Affine.Point.some _ _ _ x₂ y₂ _ =>
    if hx : x₁ = x₂ then
      if hy : y₁ = y₂ then
        isTrue (by subst hx; subst hy; rfl)
      else
        isFalse (by intro h; cases h; exact hy rfl)
    else
      isFalse (by intro h; cases h; exact hx rfl)

/-! ## Fast scalar multiplication via double-and-add

Mathlib's `nsmul` for `W.Point` is `nsmulRec`, which is linear in the
scalar and out of reach of `native_decide` for 256-bit ECDSA scalars.
`scalarMul` is the standard right-to-left double-and-add, with
`scalarMul_eq_nsmul` certifying the equivalence on the low 256 bits.
-/

/-- Body of the double-and-add loop. After `n` iterations starting
from `(acc, base, e)`, the result is `acc + (e % 2^n) • base`. -/
def scalarMulLoop (n : Nat) (acc base : W.Point) (e : Nat) : W.Point :=
  match n with
  | 0 => acc
  | n+1 =>
    scalarMulLoop n
      (if e % 2 = 1 then acc + base else acc)
      (base + base)
      (e / 2)

/-- Right-to-left double-and-add scalar multiplication on the low 256
bits of `k`. -/
def scalarMul (P : W.Point) (k : Nat) : W.Point :=
  scalarMulLoop 256 0 P k

private lemma scalarMulLoop_eq (n : Nat) (acc base : W.Point) (e : Nat) :
    scalarMulLoop n acc base e = acc + (e % 2 ^ n) • base := by
  induction n generalizing acc base e with
  | zero =>
    simp [scalarMulLoop, pow_zero, Nat.mod_one]
  | succ n ih =>
    rw [scalarMulLoop, ih]
    have h_mod : e % 2 ^ (n + 1) = e % 2 + 2 * (e / 2 % 2 ^ n) := by
      rw [pow_succ, Nat.mul_comm, Nat.mod_mul]
    have h_step : (e / 2 % 2 ^ n) • (base + base) = (2 * (e / 2 % 2 ^ n)) • base := by
      rw [show base + base = (2 : ℕ) • base from (two_nsmul base).symm,
        ← mul_nsmul', Nat.mul_comm]
    rw [h_step, h_mod, add_nsmul]
    by_cases hbit : e % 2 = 1
    · rw [if_pos hbit, hbit, one_nsmul, add_assoc]
    · have he : e % 2 = 0 := by omega
      rw [if_neg hbit, he, zero_nsmul, zero_add]

/-- The double-and-add and Mathlib's linear `nsmul` agree on
`k % 2^256`. -/
theorem scalarMul_eq_mod_nsmul (P : W.Point) (k : Nat) :
    scalarMul P k = (k % 2 ^ 256) • P := by
  rw [scalarMul, scalarMulLoop_eq, zero_add]

/-- On any scalar fitting in 256 bits, double-and-add equals
Mathlib's `nsmul`. -/
theorem scalarMul_eq_nsmul (P : W.Point) (k : Nat) (hk : k < 2 ^ 256) :
    scalarMul P k = k • P := by
  rw [scalarMul_eq_mod_nsmul, Nat.mod_eq_of_lt hk]

end Lampe.Crypto
