import Lampe.Tp
import Lampe.Crypto.MathlibBridge
import Mathlib.Tactic.Ring

namespace Lampe.Crypto.EmbeddedCurve

/--
Concrete semantic model for Noir's embedded-curve builtins.

This models the Grumpkin-style short-Weierstrass arithmetic that the Noir stdlib targets:

- points are tuples `(x, y, isInfinite)`
- scalars are split into low/high 128-bit limbs
- the curve equation is `y^2 = x^3 - 17`

Curve arithmetic uses Mathlib's affine formulae (including `slope`, which is computable
since v4.22 / PR #27299). Decidability of `Equation` / `Nonsingular` / `Point` equality
comes from `Lampe.Crypto.MathlibBridge`.
-/

@[reducible]
def pointTp : Tp :=
  .tuple (some "«std-1.0.0-beta.14::embedded_curve_ops::EmbeddedCurvePoint»")
    [.field, .field, .bool]

@[reducible]
def scalarTp : Tp :=
  .tuple (some "«std-1.0.0-beta.14::embedded_curve_ops::EmbeddedCurveScalar»")
    [.field, .field]

@[reducible]
def Point (p : Prime) := Tp.denote p pointTp

@[reducible]
def Scalar (p : Prime) := Tp.denote p scalarTp

def pointX {p : Prime} (pt : Point p) : Fp p := pt.1
def pointY {p : Prime} (pt : Point p) : Fp p := pt.2.1
def pointIsInfinite {p : Prime} (pt : Point p) : Bool := pt.2.2.1

def scalarLo {p : Prime} (s : Scalar p) : Fp p := s.1
def scalarHi {p : Prime} (s : Scalar p) : Fp p := s.2.1

@[reducible]
def mkPoint {p : Prime} (x y : Fp p) (isInfinite : Bool) : Point p := (x, y, isInfinite, ())

@[reducible]
def pointAtInfinity {p : Prime} : Point p := mkPoint 0 0 true

def canonicalizeInfinity {p : Prime} (pt : Point p) : Point p :=
  if pointIsInfinite pt then pointAtInfinity else pt

def curveB {p : Prime} : Fp p := -17

/-- The concrete Weierstrass curve used by Noir's embedded-curve stdlib: `y^2 = x^3 - 17`. -/
@[reducible]
def curve (p : Prime) : WeierstrassCurve (Fp p) :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 0, a₆ := curveB }

abbrev affineCurve (p : Prime) : WeierstrassCurve.Affine (Fp p) := (curve p).toAffine

@[simp]
lemma affineCurve_negY {p : Prime} (x y : Fp p) :
    (affineCurve p).negY x y = -y := by
  simp [WeierstrassCurve.Affine.negY]

@[simp]
lemma affineCurve_addX {p : Prime} (x₁ x₂ slope : Fp p) :
    (affineCurve p).addX x₁ x₂ slope = slope ^ 2 - x₁ - x₂ := by
  simp [WeierstrassCurve.Affine.addX]

@[simp]
lemma affineCurve_addY {p : Prime} (x₁ x₂ y₁ slope : Fp p) :
    (affineCurve p).addY x₁ x₂ y₁ slope =
      slope * (x₁ - (affineCurve p).addX x₁ x₂ slope) - y₁ := by
  simp [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY]
  ring

def pow128 : Nat := 2 ^ 128

def scalarValueNat {p : Prime} (s : Scalar p) : Nat :=
  (scalarLo s).val + pow128 * (scalarHi s).val

def curvePoint? {p : Prime} (pt : Point p) : Option ((affineCurve p).Point) :=
  if pointIsInfinite pt then
    some 0
  else if hNs : (affineCurve p).Nonsingular (pointX pt) (pointY pt) then
    some (WeierstrassCurve.Affine.Point.some (x := pointX pt) (y := pointY pt) hNs)
  else
    none

def encodeCurvePoint {p : Prime} : (affineCurve p).Point → Point p
  | 0 => pointAtInfinity
  | .some (x := x) (y := y) _ => mkPoint x y false

@[simp]
theorem curvePoint?_infinity {p : Prime} :
    curvePoint? (pointAtInfinity : Point p) = some 0 := by
  simp [curvePoint?, pointIsInfinite]

@[simp]
theorem curvePoint?_of_infinite {p : Prime} {pt : Point p}
    (hInf : pointIsInfinite pt = true) : curvePoint? pt = some 0 := by
  simp [curvePoint?, hInf]

theorem curvePoint?_some_of_finite_nonsingular {p : Prime} {pt : Point p}
    (hFin : pointIsInfinite pt = false)
    (hNs : (affineCurve p).Nonsingular (pointX pt) (pointY pt)) :
    curvePoint? pt = some (WeierstrassCurve.Affine.Point.some (x := pointX pt) (y := pointY pt) hNs) := by
  classical
  simp [curvePoint?, hFin, hNs]

theorem curvePoint?_eq_some_zero_iff {p : Prime} {pt : Point p} :
    curvePoint? pt = some (0 : (affineCurve p).Point) ↔ pointIsInfinite pt = true := by
  classical
  by_cases hInf : pointIsInfinite pt = true
  · simp [curvePoint?, hInf]
  · simp [curvePoint?, hInf]

theorem curvePoint?_eq_some_some_iff {p : Prime} {pt : Point p} {x y : Fp p}
    {hNs : (affineCurve p).Nonsingular x y} :
    curvePoint? pt = some (WeierstrassCurve.Affine.Point.some (x := x) (y := y) hNs) ↔
      pointIsInfinite pt = false ∧ pointX pt = x ∧ pointY pt = y := by
  classical
  by_cases hInf : pointIsInfinite pt = true
  · simp [curvePoint?, hInf]
  · simp only [Bool.not_eq_true] at hInf
    by_cases hNs' : (affineCurve p).Nonsingular (pointX pt) (pointY pt)
    · simp [curvePoint?, hInf, hNs']
    · simp [curvePoint?, hInf, hNs']
      rintro hx hy
      exact absurd (hx ▸ hy ▸ hNs) hNs'

@[simp] theorem encodeCurvePoint_zero {p : Prime} :
    encodeCurvePoint (0 : (affineCurve p).Point) = pointAtInfinity := rfl

@[simp] theorem encodeCurvePoint_some {p : Prime} {x y : Fp p}
    (hNs : (affineCurve p).Nonsingular x y) :
    encodeCurvePoint (WeierstrassCurve.Affine.Point.some (x := x) (y := y) hNs) =
      mkPoint x y false := rfl

theorem encodeCurvePoint_curvePoint? {p : Prime} {pt : Point p} {P : (affineCurve p).Point}
    (hP : curvePoint? pt = some P) :
    encodeCurvePoint P = canonicalizeInfinity pt := by
  rcases P with (_ | @⟨x, y, hNs⟩)
  · have hInf : pointIsInfinite pt = true := curvePoint?_eq_some_zero_iff.mp hP
    simp [encodeCurvePoint, canonicalizeInfinity, hInf,
      ]
  · obtain ⟨hFin, hx, hy⟩ := curvePoint?_eq_some_some_iff.mp hP
    obtain ⟨x', y', inf, ⟨⟩⟩ := pt
    simp only [pointX, pointY, pointIsInfinite] at hFin hx hy
    subst hFin
    subst hx
    subst hy
    simp [encodeCurvePoint, canonicalizeInfinity, pointIsInfinite, mkPoint]

@[simp] theorem curvePoint?_encodeCurvePoint {p : Prime} (P : (affineCurve p).Point) :
    curvePoint? (encodeCurvePoint P) = some P := by
  rcases P with (_ | @⟨x, y, hNs⟩)
  · show curvePoint? (encodeCurvePoint (0 : (affineCurve p).Point)) = some 0
    rw [encodeCurvePoint_zero, curvePoint?_infinity]
  · have hFin : pointIsInfinite (mkPoint x y false : Point p) = false := rfl
    have hxy : (affineCurve p).Nonsingular (pointX (mkPoint x y false : Point p))
        (pointY (mkPoint x y false : Point p)) := hNs
    simp [encodeCurvePoint, curvePoint?_some_of_finite_nonsingular hFin hxy,
          pointX, pointY, mkPoint]

end Lampe.Crypto.EmbeddedCurve
