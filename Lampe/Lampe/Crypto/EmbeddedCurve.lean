import Lampe.Tp
import Lampe.Crypto.ShortWeierstrass

namespace Lampe.Crypto.EmbeddedCurve

/--
Concrete semantic model for Noir's embedded-curve builtins.

The Grumpkin-style short-Weierstrass arithmetic targeted by the Noir
stdlib:

- points are tuples `(x, y, isInfinite)`
- scalars are split into low/high 128-bit limbs
- the curve equation is `y² = x³ - 17`

Curve math and the Mathlib correspondence are inherited from
`Lampe.Crypto.ShortWeierstrass`. This file carries the Noir-struct
tuple plumbing, the Grumpkin-specific coefficients, and 128-bit
scalar handling.
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

def curveA {p : Prime} : Fp p := 0
def curveB {p : Prime} : Fp p := -17

/-- The concrete Weierstrass curve used by Noir's embedded-curve stdlib: `y² = x³ - 17`. -/
@[reducible]
def curve (p : Prime) : WeierstrassCurve (Fp p) :=
  ShortWeierstrass.asWeierstrass (curveA : Fp p) curveB

abbrev affineCurve (p : Prime) : WeierstrassCurve.Affine (Fp p) :=
  ShortWeierstrass.asAffine (curveA : Fp p) curveB

@[simp]
lemma affineCurve_negY {p : Prime} (x y : Fp p) :
    (affineCurve p).negY x y = -y :=
  ShortWeierstrass.asAffine_negY curveA curveB x y

@[simp]
lemma affineCurve_addX {p : Prime} (x₁ x₂ slope : Fp p) :
    (affineCurve p).addX x₁ x₂ slope = slope ^ 2 - x₁ - x₂ :=
  ShortWeierstrass.asAffine_addX curveA curveB x₁ x₂ slope

@[simp]
lemma affineCurve_addY {p : Prime} (x₁ x₂ y₁ slope : Fp p) :
    (affineCurve p).addY x₁ x₂ y₁ slope =
      slope * (x₁ - (affineCurve p).addX x₁ x₂ slope) - y₁ :=
  ShortWeierstrass.asAffine_addY curveA curveB x₁ x₂ y₁ slope

private def slope {p : Prime} (x₁ x₂ y₁ y₂ : Fp p) : Fp p :=
  ShortWeierstrass.Point.slope (curveA : Fp p) x₁ x₂ y₁ y₂

private theorem slope_eq_mathlib {p : Prime} (x₁ x₂ y₁ y₂ : Fp p) :
    slope x₁ x₂ y₁ y₂ = (affineCurve p).slope x₁ x₂ y₁ y₂ :=
  ShortWeierstrass.slope_eq_mathlib (curveA : Fp p) curveB x₁ x₂ y₁ y₂

/-- Total tuple-level extension of Mathlib's `WeierstrassCurve.Affine.Point.add`.
Off-curve tuples are out of contract; on encoded curve points this agrees
with Mathlib's `+` (see `add_encodeCurvePoint`). -/
def add {p : Prime} (point1 point2 : Point p) : Point p :=
  if pointIsInfinite point1 then
    canonicalizeInfinity point2
  else if pointIsInfinite point2 then
    canonicalizeInfinity point1
  else
    let W := affineCurve p
    let x1 := pointX point1
    let y1 := pointY point1
    let x2 := pointX point2
    let y2 := pointY point2
    if x1 = x2 ∧ y1 = W.negY x2 y2 then
      pointAtInfinity
    else
      let slope := slope x1 x2 y1 y2
      mkPoint
        (W.addX x1 x2 slope)
        (W.addY x1 x2 y1 slope)
        false

def pow128 : Nat := 2 ^ 128

def scalarValueNat {p : Prime} (s : Scalar p) : Nat :=
  (scalarLo s).val + pow128 * (scalarHi s).val

/-- Decidability of `Equation` / `Nonsingular` on the Grumpkin curve is
inherited from the shared module's generic instances. -/
instance affineCurve_Equation_decidable {p : Prime} (x y : Fp p) :
    Decidable ((affineCurve p).Equation x y) :=
  ShortWeierstrass.asAffine_Equation_decidable curveA curveB x y

instance affineCurve_Nonsingular_decidable {p : Prime} (x y : Fp p) :
    Decidable ((affineCurve p).Nonsingular x y) :=
  ShortWeierstrass.asAffine_Nonsingular_decidable curveA curveB x y

def curvePoint? {p : Prime} (pt : Point p) : Option ((affineCurve p).Point) :=
  if pointIsInfinite pt then
    some 0
  else if hNs : (affineCurve p).Nonsingular (pointX pt) (pointY pt) then
    some (.some hNs)
  else
    none

def encodeCurvePoint {p : Prime} : (affineCurve p).Point → Point p
  | 0 => pointAtInfinity
  | .some (x := x) (y := y) _ => mkPoint x y false

@[simp]
theorem curvePoint?_infinity {p : Prime} :
    curvePoint? (pointAtInfinity : Point p) = some 0 := by
  simp [curvePoint?, pointAtInfinity, mkPoint, pointIsInfinite]

@[simp]
theorem curvePoint?_of_infinite {p : Prime} {pt : Point p}
    (hInf : pointIsInfinite pt = true) : curvePoint? pt = some 0 := by
  simp [curvePoint?, hInf]

theorem curvePoint?_some_of_finite_nonsingular {p : Prime} {pt : Point p}
    (hFin : pointIsInfinite pt = false)
    (hNs : (affineCurve p).Nonsingular (pointX pt) (pointY pt)) :
    curvePoint? pt = some (.some hNs) := by
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
    curvePoint? pt = some (.some hNs) ↔
      pointIsInfinite pt = false ∧ pointX pt = x ∧ pointY pt = y := by
  classical
  by_cases hInf : pointIsInfinite pt = true
  · simp [curvePoint?, hInf]
  · simp only [Bool.not_eq_true] at hInf
    by_cases hNs' : (affineCurve p).Nonsingular (pointX pt) (pointY pt)
    · simp [curvePoint?, hInf, hNs', and_iff_right hInf]
    · simp [curvePoint?, hInf, hNs']
      rintro hx hy
      exact absurd (hx ▸ hy ▸ hNs) hNs'

@[simp] theorem encodeCurvePoint_zero {p : Prime} :
    encodeCurvePoint (0 : (affineCurve p).Point) = pointAtInfinity := rfl

@[simp] theorem encodeCurvePoint_some {p : Prime} {x y : Fp p}
    (hNs : (affineCurve p).Nonsingular x y) :
    encodeCurvePoint (.some hNs) = mkPoint x y false := rfl

theorem encodeCurvePoint_curvePoint? {p : Prime} {pt : Point p} {P : (affineCurve p).Point}
    (hP : curvePoint? pt = some P) :
    encodeCurvePoint P = canonicalizeInfinity pt := by
  rcases P with (_ | @⟨x, y, hNs⟩)
  · have hInf : pointIsInfinite pt = true := curvePoint?_eq_some_zero_iff.mp hP
    simp [encodeCurvePoint, canonicalizeInfinity, hInf,
      ← WeierstrassCurve.Affine.Point.zero_def]
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
    simp [encodeCurvePoint, curvePoint?_some_of_finite_nonsingular hFin hxy]

def scalarMulNat {p : Prime} (pt : Point p) : Nat → Point p
  | 0 => pointAtInfinity
  | n + 1 => add pt (scalarMulNat pt n)

def scalarMul {p : Prime} (pt : Point p) (s : Scalar p) : Point p :=
  scalarMulNat pt (scalarValueNat s)

theorem add_encodeCurvePoint {p : Prime} (P Q : (affineCurve p).Point) :
    add (encodeCurvePoint P) (encodeCurvePoint Q) = encodeCurvePoint (P + Q) := by
  rcases P with (_ | @⟨x₁, y₁, h₁⟩) <;> rcases Q with (_ | @⟨x₂, y₂, h₂⟩)
  · rfl
  · simp [add, encodeCurvePoint, canonicalizeInfinity, pointAtInfinity, mkPoint,
      pointX, pointY, pointIsInfinite, ← WeierstrassCurve.Affine.Point.zero_def]
  · simp [add, encodeCurvePoint, canonicalizeInfinity, pointAtInfinity, mkPoint,
      pointX, pointY, pointIsInfinite, ← WeierstrassCurve.Affine.Point.zero_def]
  · by_cases hxy : x₁ = x₂ ∧ y₁ = (affineCurve p).negY x₂ y₂
    · rcases hxy with ⟨hx, hy⟩
      rw [WeierstrassCurve.Affine.Point.add_of_Y_eq (W := affineCurve p) hx hy]
      simp [add, encodeCurvePoint, pointAtInfinity, mkPoint, pointX, pointY, pointIsInfinite,
        hx, hy]
    · by_cases hx : x₁ = x₂
      · have hyne : y₁ ≠ (affineCurve p).negY x₂ y₂ := by
          intro hy
          exact hxy ⟨hx, hy⟩
        have hyne' : ¬ y₁ = -y₂ := by
          simpa using hyne
        rw [WeierstrassCurve.Affine.Point.add_of_Y_ne (W := affineCurve p) hyne]
        simp [add, encodeCurvePoint, mkPoint, pointX, pointY, pointIsInfinite, hxy, hx, hyne,
          hyne',
          slope_eq_mathlib]
      · rw [WeierstrassCurve.Affine.Point.add_of_X_ne (W := affineCurve p) hx]
        simp [add, encodeCurvePoint, mkPoint, pointX, pointY, pointIsInfinite, hxy, hx,
          slope_eq_mathlib]

/-- `add` only inspects the canonicalized form of its inputs:
infinity bits short-circuit and finite cases use only `(x, y)`. -/
theorem scalarMulNat_of_infinite {p : Prime} {pt : Point p}
    (hInf : pointIsInfinite pt = true) :
    ∀ n, scalarMulNat pt n = pointAtInfinity
  | 0 => rfl
  | n + 1 => by
      simp [scalarMulNat, scalarMulNat_of_infinite hInf n, add, hInf, canonicalizeInfinity, pointAtInfinity]

theorem scalarMulNat_encodeCurvePoint {p : Prime} (P : (affineCurve p).Point) :
    ∀ n, scalarMulNat (encodeCurvePoint P) n = encodeCurvePoint (n • P)
  | 0 => by simp [scalarMulNat]
  | n + 1 => by
      simp [scalarMulNat, scalarMulNat_encodeCurvePoint, add_encodeCurvePoint, succ_nsmul,
        add_comm, add_left_comm, add_assoc]

theorem scalarMul_eq_smul_encodeCurvePoint {p : Prime} {pt : Point p} {s : Scalar p}
    {P : (affineCurve p).Point} (hP : curvePoint? pt = some P) :
    scalarMul pt s = encodeCurvePoint (scalarValueNat s • P) := by
  rcases P with (_ | @⟨x, y, hNs⟩)
  · have hInf : pointIsInfinite pt = true := (curvePoint?_eq_some_zero_iff).mp hP
    simp [scalarMul, scalarMulNat_of_infinite hInf,
      ← WeierstrassCurve.Affine.Point.zero_def, smul_zero]
  · obtain ⟨x', y', inf, ⟨⟩⟩ := pt
    cases inf
    · obtain ⟨_, hx, hy⟩ := curvePoint?_eq_some_some_iff.mp hP
      simp only [pointX, pointY] at hx hy
      subst hx
      subst hy
      simpa [scalarMul, encodeCurvePoint, mkPoint] using
        (scalarMulNat_encodeCurvePoint (p := p) (.some hNs) (scalarValueNat s))
    · simp [curvePoint?_of_infinite (pt := (x', y', true, ())) rfl] at hP

def multiScalarMulList {p : Prime} : List (Point p) → List (Scalar p) → Point p
  | pt :: pts, s :: ss => add (scalarMul pt s) (multiScalarMulList pts ss)
  | _, _ => pointAtInfinity

/-- If every input point is an encoded Mathlib point, MSM agrees with
the Mathlib `∑ kᵢ • Pᵢ` (under `scalarValueNat` for each scalar). -/
theorem multiScalarMulList_of_encoded {p : Prime} :
    ∀ (Ps : List ((affineCurve p).Point)) (ss : List (Scalar p)),
      multiScalarMulList (Ps.map encodeCurvePoint) ss =
        encodeCurvePoint
          ((ss.zip Ps).foldr (fun (sP : Scalar p × (affineCurve p).Point) acc =>
            scalarValueNat sP.1 • sP.2 + acc) 0)
  | [], ss => by
      cases ss <;> simp [multiScalarMulList, List.zip]
  | _ :: _, [] => by
      simp [multiScalarMulList, List.zip]
  | P :: Ps, s :: ss => by
      simp only [List.map_cons, multiScalarMulList, List.zip_cons_cons, List.foldr_cons]
      rw [multiScalarMulList_of_encoded Ps ss,
          scalarMul_eq_smul_encodeCurvePoint (curvePoint?_encodeCurvePoint P),
          add_encodeCurvePoint]

def multiScalarMul {p : Prime} (n : U 32)
    (points : List.Vector (Point p) n.toNat)
    (scalars : List.Vector (Scalar p) n.toNat) : Point p :=
  multiScalarMulList points.toList scalars.toList

end Lampe.Crypto.EmbeddedCurve
