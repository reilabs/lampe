import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Local decidability instances on Mathlib's affine elliptic-curve `Point`

Mathlib (as of v4.22 / PR #27299) provides a computable `+` on
`WeierstrassCurve.Affine.Point`, but does **not** ship decidable
instances for the supporting predicates (`Equation`, `Nonsingular`)
or for equality on `Point` itself. Any concrete computation —
ECDSA verification, embedded-curve scalar mult on tuple inputs —
needs these to lift raw coordinates into the proof-bundled
`Point.some h` constructor and to compare points by structural
equality.

These instances are field-generic. Each elliptic-curve module
instantiates them implicitly by importing this file.

Hopefully upstreamed alongside, or shortly after, the same
follow-up that motivated PR #27299.
-/

namespace Lampe.Crypto

variable {F : Type} [Field F] [DecidableEq F] {W : WeierstrassCurve.Affine F}

/-- `W.Equation x y` is `polynomial.evalEval x y = 0`, which Mathlib
keeps noncomputable. The `equation_iff'` rewriting turns it into a
polynomial identity in `F`, decidable when `F` has `DecidableEq`. -/
instance affineEquation_decidable (x y : F) : Decidable (W.Equation x y) :=
  decidable_of_iff _ (WeierstrassCurve.Affine.equation_iff' (W := W) x y).symm

/-- `W.Nonsingular x y` is `Equation ∧ (polynomialX ≠ 0 ∨ polynomialY ≠ 0)`.
Same trick — `nonsingular_iff'` rewrites it to field-level facts. -/
instance affineNonsingular_decidable (x y : F) : Decidable (W.Nonsingular x y) :=
  decidable_of_iff _ (WeierstrassCurve.Affine.nonsingular_iff' (W := W) x y).symm

/-- Structural equality on `W.Point`: compare zero vs zero, and for
two `some` constructors compare their coordinates (the `Nonsingular`
proof payload is `Prop`-valued and absorbed by proof irrelevance). -/
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
