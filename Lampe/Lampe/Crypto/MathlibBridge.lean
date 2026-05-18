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

end Lampe.Crypto
