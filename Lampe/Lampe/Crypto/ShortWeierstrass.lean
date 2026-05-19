import Lampe.Tp
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic.Ring

set_option linter.unusedSectionVars false

/-!
# Short Weierstrass curves — shared formulas and Mathlib bridge

A reusable computable implementation of short-Weierstrass arithmetic:
y² = x³ + a·x + b over an arbitrary `Field F`. Curve-specific files
(`Crypto/EmbeddedCurve.lean`, `Crypto/Secp256k1.lean`,
`Crypto/Secp256r1.lean`) instantiate this with their field,
coefficients, and any external representation.

The module provides:

* an inductive `Point F = infinity | affine x y`;
* `slope` / `add` / `scalarMulNat` formulas with the general
  `(3·x² + a)` numerator (correct for any short Weierstrass curve);
* a Mathlib bridge via `asAffine a b : WeierstrassCurve.Affine F`
  with `curvePoint?` / `encodeCurvePoint` round-trips and the
  group-law correspondence `add_encodeCurvePoint`,
  `scalarMulNat_encodeCurvePoint`.

The bridge lets downstream proofs lift to Mathlib's `Point` group
structure (associativity, commutativity, scalar distributivity)
without paying for them per-curve.
-/

namespace Lampe.Crypto.ShortWeierstrass

/-- An affine point on a short Weierstrass curve, plus infinity. -/
inductive Point (F : Type) where
  | infinity : Point F
  | affine : F → F → Point F
deriving DecidableEq, Repr

namespace Point

variable {F : Type} [Field F] [DecidableEq F]

/-- Local slope formula for `y² = x³ + a·x + b`. Equal to
`WeierstrassCurve.Affine.slope` (see `slope_eq_mathlib`). -/
def slope (a : F) (x₁ x₂ y₁ y₂ : F) : F :=
  if x₁ = x₂ then
    if y₁ = -y₂ then 0
    else (3 * x₁ ^ 2 + a) / (2 * y₁)
  else (y₁ - y₂) / (x₁ - x₂)

/-- Affine point addition. Identity and additive-inverse cases are
short-circuited; doubling is handled implicitly by `slope` because the
`x₁ = x₂ ∧ y₁ ≠ -y₂` branch reduces to the doubling formula. -/
def add (a : F) (P Q : Point F) : Point F :=
  match P, Q with
  | .infinity, _ => Q
  | _, .infinity => P
  | .affine x₁ y₁, .affine x₂ y₂ =>
    if x₁ = x₂ ∧ y₁ = -y₂ then .infinity
    else
      let lam := slope a x₁ x₂ y₁ y₂
      let xr := lam ^ 2 - x₁ - x₂
      let yr := lam * (x₁ - xr) - y₁
      .affine xr yr

/-- Repeated-addition scalar multiplication. Matches Mathlib's `nsmul`
shape; used by the Mathlib correspondence lemmas. O(n) so not suitable
for `native_decide` with 256-bit scalars — see `scalarMul` for the fast
variant. -/
def scalarMulNat (a : F) (P : Point F) : Nat → Point F
  | 0 => .infinity
  | n + 1 => add a P (scalarMulNat a P n)

/-- Fast scalar multiplication via right-to-left double-and-add.
Performs at most `bits` doublings + adds, so `O(log k)` for `k < 2^bits`.
For ECDSA over 256-bit curves, pass `bits = 256`. -/
def scalarMul (a : F) (P : Point F) (k : Nat) (bits : Nat := 256) : Point F := Id.run do
  let mut acc : Point F := .infinity
  let mut base : Point F := P
  let mut e : Nat := k
  for _ in [:bits] do
    if e % 2 = 1 then
      acc := add a acc base
    base := add a base base
    e := e / 2
  return acc

end Point

/-! ### Mathlib bridge -/

/-- The short Weierstrass curve with coefficients `(a, b)` as a
`WeierstrassCurve F`. -/
@[reducible]
def asWeierstrass {F : Type} [Field F] (a b : F) : WeierstrassCurve F :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := a, a₆ := b }

@[reducible]
def asAffine {F : Type} [Field F] (a b : F) : WeierstrassCurve.Affine F :=
  (asWeierstrass a b).toAffine

variable {F : Type} [Field F] [DecidableEq F]

@[simp]
lemma asAffine_negY (a b : F) (x y : F) :
    (asAffine a b).negY x y = -y := by
  simp [asAffine, asWeierstrass, WeierstrassCurve.Affine.negY]

@[simp]
lemma asAffine_addX (a b : F) (x₁ x₂ s : F) :
    (asAffine a b).addX x₁ x₂ s = s ^ 2 - x₁ - x₂ := by
  simp [asAffine, asWeierstrass, WeierstrassCurve.Affine.addX]

@[simp]
lemma asAffine_addY (a b : F) (x₁ x₂ y₁ s : F) :
    (asAffine a b).addY x₁ x₂ y₁ s =
      s * (x₁ - (asAffine a b).addX x₁ x₂ s) - y₁ := by
  simp [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY]
  ring

lemma slope_eq_mathlib (a b : F) (x₁ x₂ y₁ y₂ : F) :
    Point.slope a x₁ x₂ y₁ y₂ = (asAffine a b).slope x₁ x₂ y₁ y₂ := by
  by_cases hx : x₁ = x₂
  · by_cases hy : y₁ = (asAffine a b).negY x₂ y₂
    · simp [Point.slope, WeierstrassCurve.Affine.slope, hx, hy,
            asAffine_negY]
    · have hy' : ¬ y₁ = -y₂ := by simpa using hy
      have hy_mathlib : ¬ y₁ = -y₂ - 0 * x₂ - 0 := by
        intro h; apply hy'; linear_combination h
      simp only [Point.slope, WeierstrassCurve.Affine.slope, hx, hy, hy',
                 asAffine, asWeierstrass, WeierstrassCurve.Affine.negY,
                 dif_neg, if_false, if_true, reduceIte]
      rw [if_neg hy_mathlib]
      field_simp
      ring
  · simp [Point.slope, WeierstrassCurve.Affine.slope, hx]

instance asAffine_Equation_decidable (a b : F) (x y : F) :
    Decidable ((asAffine a b).Equation x y) :=
  decidable_of_iff _ (WeierstrassCurve.Affine.equation_iff' (W := asAffine a b) x y).symm

instance asAffine_Nonsingular_decidable (a b : F) (x y : F) :
    Decidable ((asAffine a b).Nonsingular x y) :=
  decidable_of_iff _ (WeierstrassCurve.Affine.nonsingular_iff' (W := asAffine a b) x y).symm

/-- Try to encode a `Point F` as a Mathlib `WeierstrassCurve.Affine.Point`
on the curve `asAffine a b`. -/
def curvePoint? (a b : F) (pt : Point F) : Option ((asAffine a b).Point) :=
  match pt with
  | .infinity => some 0
  | .affine x y =>
    if hNs : (asAffine a b).Nonsingular x y then some (.some hNs)
    else none

/-- Inverse of `curvePoint?` on its image. -/
def encodeCurvePoint (a b : F) : (asAffine a b).Point → Point F
  | 0 => .infinity
  | .some (x := x) (y := y) _ => .affine x y

@[simp] theorem encodeCurvePoint_zero (a b : F) :
    encodeCurvePoint a b (0 : (asAffine a b).Point) = .infinity := rfl

@[simp] theorem encodeCurvePoint_some (a b : F) {x y : F}
    (hNs : (asAffine a b).Nonsingular x y) :
    encodeCurvePoint a b (.some hNs) = .affine x y := rfl

@[simp] theorem curvePoint?_infinity (a b : F) :
    curvePoint? a b (.infinity : Point F) = some 0 := by
  simp [curvePoint?]

theorem curvePoint?_some_of_nonsingular (a b : F) {x y : F}
    (hNs : (asAffine a b).Nonsingular x y) :
    curvePoint? a b (Point.affine x y) =
      some (WeierstrassCurve.Affine.Point.some hNs) := by
  classical
  show (if hNs' : _ then some (WeierstrassCurve.Affine.Point.some hNs') else none)
        = some (WeierstrassCurve.Affine.Point.some hNs)
  rw [dif_pos hNs]

@[simp] theorem curvePoint?_encodeCurvePoint (a b : F) (P : (asAffine a b).Point) :
    curvePoint? a b (encodeCurvePoint a b P) = some P := by
  rcases P with (_ | @⟨x, y, hNs⟩)
  · show curvePoint? a b (encodeCurvePoint a b (0 : (asAffine a b).Point)) = some 0
    rw [encodeCurvePoint_zero, curvePoint?_infinity]
  · simpa using curvePoint?_some_of_nonsingular a b hNs

/-- Operational `add` corresponds to Mathlib's `+` on encoded points. -/
theorem add_encodeCurvePoint (a b : F) (P Q : (asAffine a b).Point) :
    Point.add a (encodeCurvePoint a b P) (encodeCurvePoint a b Q) =
      encodeCurvePoint a b (P + Q) := by
  rcases P with (_ | @⟨x₁, y₁, h₁⟩) <;> rcases Q with (_ | @⟨x₂, y₂, h₂⟩)
  · rfl
  · simp [Point.add, encodeCurvePoint, ← WeierstrassCurve.Affine.Point.zero_def]
  · simp [Point.add, encodeCurvePoint, ← WeierstrassCurve.Affine.Point.zero_def]
  · by_cases hxy : x₁ = x₂ ∧ y₁ = (asAffine a b).negY x₂ y₂
    · rcases hxy with ⟨hx, hy⟩
      rw [WeierstrassCurve.Affine.Point.add_of_Y_eq (W := asAffine a b) hx hy]
      simp [Point.add, encodeCurvePoint, hx, hy]
    · by_cases hx : x₁ = x₂
      · have hyne : y₁ ≠ (asAffine a b).negY x₂ y₂ := fun hy => hxy ⟨hx, hy⟩
        have hyne' : ¬ y₁ = -y₂ := by simpa using hyne
        have hxy' : ¬ (x₁ = x₂ ∧ y₁ = -y₂) := fun ⟨_, hy⟩ => hyne' hy
        rw [WeierstrassCurve.Affine.Point.add_of_Y_ne (W := asAffine a b) hyne]
        simp only [Point.add, encodeCurvePoint, hxy', if_false,
                   asAffine_addX, asAffine_addY,
                   slope_eq_mathlib (a := a) (b := b)]
      · rw [WeierstrassCurve.Affine.Point.add_of_X_ne (W := asAffine a b) hx]
        have hxy' : ¬ (x₁ = x₂ ∧ y₁ = -y₂) := fun ⟨hx', _⟩ => hx hx'
        simp only [Point.add, hxy', if_false, encodeCurvePoint,
                   asAffine_addX, asAffine_addY,
                   slope_eq_mathlib (a := a) (b := b)]

theorem scalarMulNat_of_infinity (a : F) :
    ∀ n, Point.scalarMulNat a (.infinity : Point F) n = .infinity
  | 0 => rfl
  | n + 1 => by
      simp [Point.scalarMulNat, scalarMulNat_of_infinity a n, Point.add]

theorem scalarMulNat_encodeCurvePoint (a b : F) (P : (asAffine a b).Point) :
    ∀ n, Point.scalarMulNat a (encodeCurvePoint a b P) n = encodeCurvePoint a b (n • P)
  | 0 => by simp [Point.scalarMulNat]
  | n + 1 => by
      simp [Point.scalarMulNat, scalarMulNat_encodeCurvePoint a b P n,
            add_encodeCurvePoint, succ_nsmul, add_comm]

end Lampe.Crypto.ShortWeierstrass
