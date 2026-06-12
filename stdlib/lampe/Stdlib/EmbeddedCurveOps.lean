import «std-1.0.0-beta.14».Extracted
import Lampe
import Stdlib.Field.Bn254
import Stdlib.Hash.Mod

namespace Lampe.Stdlib.EmbeddedCurveOps

open «std-1.0.0-beta.14»
open Lampe.Crypto.EmbeddedCurve

/-!
### Spec layering convention

Following the `BoundedVec` pattern (see
`Stdlib.Collections.BoundedVec.Methods`), each Noir function whose
return shape admits a high-level semantic statement has **two specs**:

- A **`private theorem foo_concrete_spec`** — faithfully restates the
  imperative Noir source (e.g. `r = Scalar.eq self other`,
  `r = Point.neg self`). Used as a proof building-block when chaining
  bigger specs together; not part of the public interface.
- The **public `theorem foo_spec`** — the canonical interface callers
  consume. Stated against semantic projections (`Scalar.valueNat`,
  `Point.extEq`, Mathlib's `WeierstrassCurve.Affine.Point.add` /
  `n • P`, …) under appropriate well-formedness preconditions
  (`Scalar.Canonical`, encoded-input hypotheses, …).

The public spec is always derivable from the private concrete spec
plus algebraic lemmas in `Lampe.Crypto.EmbeddedCurve`. Functions whose
return shape is already semantic (e.g. `point_at_infinity_spec`,
`generator_spec`, `scalar_from_field_spec`) carry only one `_spec`.
-/

private theorem vector_get_eq_getElem (v : List.Vector α n) (i : Nat) (hi : i < n) :
    List.Vector.get v ⟨i, hi⟩ = v[i] := rfl

private lemma sub_add_mod_eq (i k off : Nat)
    (hik : i ≤ k) (hoff : off + k < 4294967296) :
    (4294967296 - i + (off + k)) % 4294967296 = off + k - i := by
  have h1 : 4294967296 - i + (off + k) = (off + k - i) + 4294967296 := by omega
  rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

namespace Point

/-- A useful shorthand for the type of the embedded curve point. -/
@[reducible]
def type := «std-1.0.0-beta.14::embedded_curve_ops::EmbeddedCurvePoint».tp h![]

/-- A useful shorthand for declaring the type of values of the embedded curve point. -/
@[reducible]
def denote (p : Prime) := Tp.denote p type

@[simp] theorem type_eq_crypto_pointTp : Point.type = pointTp := rfl

def mk {p} (x y : Fp p) (isInfinite : Bool) : Point.denote p :=
  mkPoint x y isInfinite

def x {p} (self : Point.denote p) : Fp p := pointX self

def y {p} (self : Point.denote p) : Fp p := pointY self

def isInfinite {p} (self : Point.denote p) : Bool :=
  pointIsInfinite self

def infinity {p} : Point.denote p := pointAtInfinity

def generator {p} : Point.denote p :=
  Point.mk 1 17631683881184975370165255887551781615748388533673675138860 false

def canonicalizeInfinity {p} (self : Point.denote p) : Point.denote p :=
  if Point.isInfinite self then Point.infinity else self

/-- Extensional point equality: equal modulo the canonical infinity
representative. -/
def extEq {p} (self other : Point.denote p) : Prop :=
  Point.canonicalizeInfinity self = Point.canonicalizeInfinity other

@[simp] private theorem indexTpl_x {p} (self : Point.denote p) :
    Builtin.indexTpl self Member.head = Point.x self := rfl

@[simp] private theorem indexTpl_y {p} (self : Point.denote p) :
    Builtin.indexTpl self Member.head.tail = Point.y self := rfl

@[simp] private theorem indexTpl_isInfinite {p} (self : Point.denote p) :
    Builtin.indexTpl self Member.head.tail.tail = Point.isInfinite self := rfl

@[simp] theorem canonicalizeInfinity_of_infinite {p} {self : Point.denote p}
    (h : Point.isInfinite self = true) :
    Point.canonicalizeInfinity self = Point.infinity := by
  simp [Point.canonicalizeInfinity, h]

@[simp] theorem canonicalizeInfinity_of_finite {p} {self : Point.denote p}
    (h : Point.isInfinite self = false) :
    Point.canonicalizeInfinity self = self := by
  simp [Point.canonicalizeInfinity, h]

@[simp] theorem canonicalizeInfinity_infinity {p} :
    Point.canonicalizeInfinity (Point.infinity (p := p)) = Point.infinity := by
  simp [Point.canonicalizeInfinity, Point.infinity]

@[simp] theorem canonicalizeInfinity_idem {p} (self : Point.denote p) :
    Point.canonicalizeInfinity (Point.canonicalizeInfinity self) =
      Point.canonicalizeInfinity self := by
  by_cases h : Point.isInfinite self = true
  · simp [Point.canonicalizeInfinity, h]
  · simp [Point.canonicalizeInfinity, h]

@[simp] theorem extEq_refl {p} (self : Point.denote p) : Point.extEq self self := rfl

def neg {p} (self : Point.denote p) : Point.denote p :=
  Point.mk (Point.x self) (-(Point.y self)) (Point.isInfinite self)

/-- `Point.neg` on an encoded Mathlib curve point matches Mathlib's
group negation under the encoding. Used to bridge `point_sub_spec`
to the Mathlib `P - Q` form. -/
theorem neg_encodeCurvePoint {p}
    (P : (affineCurve p).Point) :
    Point.neg (encodeCurvePoint P) =
      encodeCurvePoint (-P) := by
  rcases P with _ | @⟨x, y, hNs⟩
  · show Point.neg (encodeCurvePoint
          (0 : (affineCurve p).Point)) =
        encodeCurvePoint
          (-(0 : (affineCurve p).Point))
    rw [neg_zero]
    simp [Point.neg, encodeCurvePoint,
      pointAtInfinity,
      mkPoint,
      Point.x, Point.y, Point.isInfinite, Point.mk,
      pointX,
      pointY,
      pointIsInfinite]
  · simp [Point.neg, Point.x, Point.y, Point.isInfinite, Point.mk,
      encodeCurvePoint,
      mkPoint,
      pointX,
      pointY,
      pointIsInfinite]

def eq {p} (a b : Point.denote p) : Bool :=
  (Point.isInfinite a && Point.isInfinite b) ||
    (decide (Point.isInfinite a = Point.isInfinite b) &&
      decide (Point.x a = Point.x b) && decide (Point.y a = Point.y b))

end Point

namespace Scalar

/-- A useful shorthand for the type of the embedded curve scalar. -/
@[reducible]
def type := «std-1.0.0-beta.14::embedded_curve_ops::EmbeddedCurveScalar».tp h![]

/-- A useful shorthand for declaring the type of values of the embedded curve scalar. -/
@[reducible]
def denote (p : Prime) := Tp.denote p type

@[simp] theorem type_eq_crypto_scalarTp : Scalar.type = scalarTp := rfl

def mk {p} (lo hi : Fp p) : Scalar.denote p := (lo, hi, ())

def validOffset (offset : U 32) : Prop :=
  offset.toNat < 33

@[simp] private theorem indexTpl_lo {p} (self : Scalar.denote p) :
    Builtin.indexTpl self Member.head = Scalar.lo self := rfl

@[simp] private theorem indexTpl_hi {p} (self : Scalar.denote p) :
    Builtin.indexTpl self Member.head.tail = Scalar.hi self := rfl

def eq {p} (a b : Scalar.denote p) : Bool :=
  decide (Scalar.hi a = Scalar.hi b) && decide (Scalar.lo a = Scalar.lo b)

def byteAtField {p} (bytes : Tp.denote p ((Tp.u 8).array (64 : U 32))) (idx : Nat) : Fp p :=
  match (List.Vector.toList bytes)[idx]? with
  | some b => Builtin.CastTp.cast b
  | none => 0

def fromBytesLoAcc {p} (bytes : Tp.denote p ((Tp.u 8).array (64 : U 32)))
    (offset : U 32) (i : Nat) : Fp p :=
  ∑ j ∈ Finset.range i, byteAtField bytes (offset.toNat + 31 - j) * (256 : Fp p) ^ j

def fromBytesHiAcc {p} (bytes : Tp.denote p ((Tp.u 8).array (64 : U 32)))
    (offset : U 32) (i : Nat) : Fp p :=
  ∑ j ∈ Finset.range i, byteAtField bytes (offset.toNat + 15 - j) * (256 : Fp p) ^ j

def fromBytes? {p} (bytes : Tp.denote p ((Tp.u 8).array (64 : U 32)))
    (offset : U 32) : Option (Scalar.denote p) :=
  if h : offset.toNat < 33 then
    some <| Scalar.mk
      (Scalar.fromBytesLoAcc bytes offset 16)
      (Scalar.fromBytesHiAcc bytes offset 16)
  else
    none

@[simp] theorem fromBytesLoAcc_zero {p}
    {bytes : Tp.denote p ((Tp.u 8).array (64 : U 32))} {offset : U 32} :
    fromBytesLoAcc bytes offset 0 = 0 := by
  simp [fromBytesLoAcc]

@[simp] theorem fromBytesHiAcc_zero {p}
    {bytes : Tp.denote p ((Tp.u 8).array (64 : U 32))} {offset : U 32} :
    fromBytesHiAcc bytes offset 0 = 0 := by
  simp [fromBytesHiAcc]

@[simp] theorem valueNat_mk {p} {lo hi : Fp p} :
    Scalar.valueNat (Scalar.mk lo hi) =
      lo.val + Lampe.pow128 * hi.val := by
  rfl

theorem fromBytes?_eq_some_of_validOffset {p}
    {bytes : Tp.denote p ((Tp.u 8).array (64 : U 32))} {offset : U 32}
    (h : Scalar.validOffset offset) :
    Scalar.fromBytes? bytes offset =
      some (Scalar.mk
        (Scalar.fromBytesLoAcc bytes offset 16)
        (Scalar.fromBytesHiAcc bytes offset 16)) := by
  have h' : offset.toNat < 33 := by simpa [Scalar.validOffset] using h
  simp [Scalar.fromBytes?, h']

theorem fromBytes?_eq_none_of_not_validOffset {p}
    {bytes : Tp.denote p ((Tp.u 8).array (64 : U 32))} {offset : U 32}
    (h : ¬ Scalar.validOffset offset) :
    Scalar.fromBytes? bytes offset = none := by
  have h' : ¬ offset.toNat < 33 := by simpa [Scalar.validOffset] using h
  simp [Scalar.fromBytes?, h']

theorem fromBytesLoAcc_succ {p}
    {bytes : Tp.denote p ((Tp.u 8).array (64 : U 32))} {offset : U 32} {i : Nat} :
    fromBytesLoAcc bytes offset (i + 1) =
      fromBytesLoAcc bytes offset i +
        byteAtField bytes (offset.toNat + 31 - i) * (256 : Fp p) ^ i := by
  simp [fromBytesLoAcc, Finset.sum_range_succ]

theorem fromBytesHiAcc_succ {p}
    {bytes : Tp.denote p ((Tp.u 8).array (64 : U 32))} {offset : U 32} {i : Nat} :
    fromBytesHiAcc bytes offset (i + 1) =
      fromBytesHiAcc bytes offset i +
        byteAtField bytes (offset.toNat + 15 - i) * (256 : Fp p) ^ i := by
  simp [fromBytesHiAcc, Finset.sum_range_succ]

end Scalar

theorem point_at_infinity_spec {p} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::embedded_curve_ops::EmbeddedCurvePoint::point_at_infinity».call
        h![] h![])
      (fun r => r = Point.infinity) := by
  enter_decl
  steps
  subst_vars
  rfl

theorem generator_spec {p} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::embedded_curve_ops::EmbeddedCurvePoint::generator».call h![] h![])
      (fun r => r = Point.generator) := by
  enter_decl
  steps
  subst_vars
  rfl

theorem scalar_new_spec {p} {lo hi : Fp p} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::embedded_curve_ops::EmbeddedCurveScalar::new».call
        h![] h![lo, hi])
      (fun r => r = Scalar.mk lo hi) := by
  enter_decl
  steps
  subst_vars
  rfl

private theorem point_neg_concrete_spec {p} {self : Point.denote p} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::ops::arith::Neg».neg h![] Point.type h![] h![] h![self])
      (fun r => r = Point.neg self) := by
  resolve_trait
  steps
  subst_vars
  rfl

/-- Canonical spec for `Neg::neg` on `EmbeddedCurvePoint`: under an
encoded-input hypothesis, negation agrees with Mathlib's group `-P`. -/
theorem point_neg_spec {p} {self : Point.denote p}
    {P : (affineCurve p).Point}
    (hself : self = encodeCurvePoint P) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::ops::arith::Neg».neg h![] Point.type h![] h![] h![self])
      (fun r => r = encodeCurvePoint (-P)) := by
  have hEq : Point.neg self = encodeCurvePoint (-P) := by
    subst hself
    exact Point.neg_encodeCurvePoint P
  have h := point_neg_concrete_spec (p := p) (self := self)
  rw [hEq] at h
  exact h

private theorem point_eq_concrete_spec {p} {self other : Point.denote p} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::cmp::Eq».eq h![] Point.type h![] h![] h![self, other])
      (fun r => r = Point.eq self other) := by
  resolve_trait
  reduce_fn_body
  steps
  all_goals try exact ()
  subst_vars
  simp [Point.eq, Point.isInfinite, Point.x, Point.y]
  rfl

/-- Canonical spec for `Eq::eq` on `EmbeddedCurvePoint`: the returned
boolean reflects extensional equality (`Point.extEq`, i.e. equality
modulo the canonical infinity representative). -/
theorem point_eq_spec {p} {self other : Point.denote p} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::cmp::Eq».eq h![] Point.type h![] h![] h![self, other])
      (fun r => r = true ↔ Point.extEq self other) := by
  steps [point_eq_concrete_spec]
  subst_vars
  obtain ⟨sx, sy, sinf, ⟨⟩⟩ := self
  obtain ⟨ox, oy, oinf, ⟨⟩⟩ := other
  cases sinf <;> cases oinf <;>
    simp [Point.eq, Point.extEq, Point.canonicalizeInfinity, Point.infinity,
      Point.x, Point.y, Point.isInfinite, pointX,
      pointY, pointIsInfinite,
      pointAtInfinity, mkPoint,
      Bool.and_eq_true, decide_eq_true_eq]
  -- After simp, three residual goals remain (cases produced in order ff, ft, tf, tt):
  -- false.false: sx=ox ∧ sy=oy ↔ (sx,sy,false,()) = (ox,oy,false,())
  · constructor
    · rintro ⟨rfl, rfl⟩; rfl
    · intro h
      refine ⟨?_, ?_⟩
      · exact (Prod.mk.inj h).1
      · exact (Prod.mk.inj (Prod.mk.inj h).2).1
  -- false.true: ¬ (sx,sy,false,()) = (0,0,true,())
  · intro h
    exact Bool.false_ne_true (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj h).2).2).1
  -- true.false: ¬ (0,0,true,()) = (ox,oy,false,())
  · intro h
    exact Bool.false_ne_true (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj h).2).2).1.symm

private theorem scalar_eq_concrete_spec {p} {self other : Scalar.denote p} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::cmp::Eq».eq h![] Scalar.type h![] h![] h![self, other])
      (fun r => r = Scalar.eq self other) := by
  resolve_trait
  reduce_fn_body
  steps
  all_goals try exact ()
  subst_vars
  simp [Scalar.eq, Scalar.hi, Scalar.lo, eq_comm]
  rfl

/-- Canonical spec for `Eq::eq` on `EmbeddedCurveScalar`: under
canonical-limb hypotheses, Noir's bitwise scalar equality reflects
semantic value-equality. -/
theorem scalar_eq_spec {p} {self other : Scalar.denote p}
    (hself : Scalar.Canonical self) (hother : Scalar.Canonical other) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::cmp::Eq».eq h![] Scalar.type h![] h![] h![self, other])
      (fun r => r = true ↔ Scalar.valueNat self = Scalar.valueNat other) := by
  steps [scalar_eq_concrete_spec]
  subst_vars
  simp [Scalar.eq]
  constructor
  · rintro ⟨hhi, hlo⟩
    simp [Scalar.valueNat, hhi, hlo]
  · intro h
    obtain ⟨hlo, hhi⟩ :=
      Scalar.valueNat_inj_canonical hself hother h
    exact ⟨hhi, hlo⟩

theorem embedded_curve_add_builtin_spec {p}
    {point1 point2 : Point.denote p}
    (hOnCurve :
      (curvePoint? point1).isSome ∧
        (curvePoint? point2).isSome) :
    STHoare p env ⟦⟧
      (.callBuiltin [Point.type, Point.type, .bool] (Point.type.array 1)
        Builtin.embeddedCurveAdd h![point1, point2, true])
      (fun r =>
        r =
          (⟨[encodeCurvePoint
                ((curvePoint? point1).get hOnCurve.1 +
                  (curvePoint? point2).get hOnCurve.2)],
              by simp⟩ : Tp.denote p (Point.type.array 1))) := by
  unfold Builtin.embeddedCurveAdd
  show STHoare p env _
    (.callBuiltin [pointTp, pointTp, .bool]
      (pointTp.array 1) _ h![point1, point2, true]) _
  apply STHoare.pureBuiltin_intro_consequence (a := ())
  any_goals rfl
  rintro ⟨h1, h2⟩
  rfl

theorem embedded_curve_add_inner_spec {p}
    {point1 point2 : Point.denote p}
    (hOnCurve :
      (curvePoint? point1).isSome ∧
        (curvePoint? point2).isSome) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::embedded_curve_ops::embedded_curve_add_inner».call
        h![] h![point1, point2])
      (fun r =>
        r = encodeCurvePoint
          ((curvePoint? point1).get hOnCurve.1 +
            (curvePoint? point2).get hOnCurve.2)) := by
  enter_decl
  steps [embedded_curve_add_builtin_spec (hOnCurve := hOnCurve)]
  simpa

theorem embedded_curve_add_spec {p}
    {point1 point2 : Point.denote p}
    (hOnCurve :
      (curvePoint? point1).isSome ∧
        (curvePoint? point2).isSome) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::embedded_curve_ops::embedded_curve_add».call
        h![] h![point1, point2])
      (fun r =>
        r = encodeCurvePoint
          ((curvePoint? point1).get hOnCurve.1 +
            (curvePoint? point2).get hOnCurve.2)) := by
  enter_decl
  steps
  all_goals try exact ()
  apply STHoare.iteFalse_intro
  steps [embedded_curve_add_inner_spec (hOnCurve := hOnCurve)]
  assumption

private theorem point_add_concrete_spec {p} {self other : Point.denote p}
    (hOnCurve :
      (curvePoint? self).isSome ∧
        (curvePoint? other).isSome) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::ops::arith::Add».add h![] Point.type h![] h![] h![self, other])
      (fun r =>
        r = encodeCurvePoint
          ((curvePoint? self).get hOnCurve.1 +
            (curvePoint? other).get hOnCurve.2)) := by
  resolve_trait
  steps [embedded_curve_add_spec (hOnCurve := hOnCurve)]
  assumption

/-- Canonical spec for `Add::add` on `EmbeddedCurvePoint`: under
encoded-input hypotheses, Noir's point addition agrees with Mathlib's
affine short-Weierstrass group law on `(affineCurve p).Point`. -/
theorem point_add_spec {p} {self other : Point.denote p}
    {P Q : (affineCurve p).Point}
    (hself : self = encodeCurvePoint P)
    (hother : other = encodeCurvePoint Q) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::ops::arith::Add».add h![] Point.type h![] h![] h![self, other])
      (fun r => r = encodeCurvePoint (P + Q)) := by
  have hOnCurve :
      (curvePoint? self).isSome ∧
        (curvePoint? other).isSome := by
    subst hself
    subst hother
    simp
  have h := point_add_concrete_spec (p := p) (self := self) (other := other)
    (hOnCurve := hOnCurve)
  have hEq :
      encodeCurvePoint
          ((curvePoint? self).get hOnCurve.1 +
            (curvePoint? other).get hOnCurve.2) =
        encodeCurvePoint (P + Q) := by
    subst hself
    subst hother
    congr 1
    simp
  rw [hEq] at h
  exact h

private theorem point_double_concrete_spec {p} {self : Point.denote p}
    (hOnCurve : (curvePoint? self).isSome) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::embedded_curve_ops::EmbeddedCurvePoint::double».call h![] h![self])
      (fun r =>
        r = encodeCurvePoint
          ((curvePoint? self).get hOnCurve +
            (curvePoint? self).get hOnCurve)) := by
  enter_decl
  steps [embedded_curve_add_spec (hOnCurve := ⟨hOnCurve, hOnCurve⟩)]
  assumption

/-- Canonical spec for `EmbeddedCurvePoint::double`: under an
encoded-input hypothesis, doubling agrees with Mathlib's `P + P`. -/
theorem point_double_spec {p} {self : Point.denote p}
    {P : (affineCurve p).Point}
    (hself : self = encodeCurvePoint P) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::embedded_curve_ops::EmbeddedCurvePoint::double».call h![] h![self])
      (fun r => r = encodeCurvePoint (P + P)) := by
  have hOnCurve : (curvePoint? self).isSome := by
    subst hself
    simp
  have h := point_double_concrete_spec (p := p) (self := self) (hOnCurve := hOnCurve)
  have hEq :
      encodeCurvePoint
          ((curvePoint? self).get hOnCurve +
            (curvePoint? self).get hOnCurve) =
        encodeCurvePoint (P + P) := by
    subst hself
    congr 1
    simp
  rw [hEq] at h
  exact h

private theorem point_sub_concrete_spec {p} {self other : Point.denote p}
    (hOnCurve :
      (curvePoint? self).isSome ∧
        (curvePoint? (Point.neg other)).isSome) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::ops::arith::Sub».sub h![] Point.type h![] h![] h![self, other])
      (fun r =>
        r = encodeCurvePoint
          ((curvePoint? self).get hOnCurve.1 +
            (curvePoint? (Point.neg other)).get hOnCurve.2)) := by
  resolve_trait
  steps [point_neg_concrete_spec, point_add_concrete_spec (hOnCurve := hOnCurve)]
  simpa [Point.neg]

/-- Canonical spec for `Sub::sub` on `EmbeddedCurvePoint`: under
encoded-input hypotheses, point subtraction agrees with Mathlib's
group `P - Q` (equivalently `P + (-Q)`). -/
theorem point_sub_spec {p} {self other : Point.denote p}
    {P Q : (affineCurve p).Point}
    (hself : self = encodeCurvePoint P)
    (hother : other = encodeCurvePoint Q) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::ops::arith::Sub».sub h![] Point.type h![] h![] h![self, other])
      (fun r => r = encodeCurvePoint (P + (-Q))) := by
  have hOnCurve :
      (curvePoint? self).isSome ∧
        (curvePoint? (Point.neg other)).isSome := by
    subst hself
    subst hother
    refine ⟨by simp, ?_⟩
    rw [Point.neg_encodeCurvePoint]
    simp
  have h := point_sub_concrete_spec (p := p) (self := self) (other := other)
    (hOnCurve := hOnCurve)
  have hEq :
      encodeCurvePoint
          ((curvePoint? self).get hOnCurve.1 +
            (curvePoint? (Point.neg other)).get hOnCurve.2) =
        encodeCurvePoint (P + (-Q)) := by
    subst hself
    subst hother
    simp only [Point.neg_encodeCurvePoint]
    congr 1
    simp
  rw [hEq] at h
  exact h

theorem point_hash_infinite_spec {p H stateRef}
    {self : Point.denote p}
    {state final : Tp.denote p H}
    {h_hasher : Lampe.Stdlib.Hash.Hasher.hasImpl env H}
    (h_inf : Point.isInfinite self = true)
    (h_bool_write : STHoare p env
      [stateRef ↦ ⟨H, state⟩]
      («std-1.0.0-beta.14::hash::Hasher».write h![] H h![] h![]
        h![stateRef, @Builtin.CastTp.cast .bool .field _ p (Point.isInfinite self)])
      (fun _ => [stateRef ↦ ⟨H, final⟩]))
    : STHoare p env
      [stateRef ↦ ⟨H, state⟩]
      («std-1.0.0-beta.14::hash::Hash».hash h![] Point.type h![] h![H] h![self, stateRef])
      (fun _ => [stateRef ↦ ⟨H, final⟩]) := by
  resolve_trait
  reduce_fn_body
  steps
  apply STHoare.ite_intro_of_true h_inf
  steps [Lampe.Stdlib.Hash.bool_hash_spec (h_write_spec := h_bool_write)]
  assumption

theorem point_hash_finite_spec {p H stateRef}
    {self : Point.denote p}
    {state state1 final : Tp.denote p H}
    {h_hasher : Lampe.Stdlib.Hash.Hasher.hasImpl env H}
    (h_fin : Point.isInfinite self = false)
    (h_x_write : STHoare p env
      [stateRef ↦ ⟨H, state⟩]
      («std-1.0.0-beta.14::hash::Hasher».write h![] H h![] h![]
        h![stateRef, Point.x self])
      (fun _ => [stateRef ↦ ⟨H, state1⟩]))
    (h_y_write : STHoare p env
      [stateRef ↦ ⟨H, state1⟩]
      («std-1.0.0-beta.14::hash::Hasher».write h![] H h![] h![]
        h![stateRef, Point.y self])
      (fun _ => [stateRef ↦ ⟨H, final⟩]))
    : STHoare p env
      [stateRef ↦ ⟨H, state⟩]
      («std-1.0.0-beta.14::hash::Hash».hash h![] Point.type h![] h![H] h![self, stateRef])
      (fun _ => [stateRef ↦ ⟨H, final⟩]) := by
  resolve_trait
  reduce_fn_body
  steps
  apply STHoare.ite_intro_of_false h_fin
  steps [Lampe.Stdlib.Hash.field_hash_spec (h_write_spec := h_x_write),
    Lampe.Stdlib.Hash.field_hash_spec (h_write_spec := h_y_write)]
  all_goals assumption

theorem point_hash_spec {p H stateRef}
    {self : Point.denote p}
    {state final : Tp.denote p H}
    {h_hasher : Lampe.Stdlib.Hash.Hasher.hasImpl env H}
    (h_write :
      if Point.isInfinite self then
        STHoare p env
          [stateRef ↦ ⟨H, state⟩]
          («std-1.0.0-beta.14::hash::Hasher».write h![] H h![] h![]
            h![stateRef, @Builtin.CastTp.cast .bool .field _ p (Point.isInfinite self)])
          (fun _ => [stateRef ↦ ⟨H, final⟩])
      else
        ∃ state1,
          STHoare p env
            [stateRef ↦ ⟨H, state⟩]
            («std-1.0.0-beta.14::hash::Hasher».write h![] H h![] h![]
              h![stateRef, Point.x self])
            (fun _ => [stateRef ↦ ⟨H, state1⟩]) ∧
          STHoare p env
            [stateRef ↦ ⟨H, state1⟩]
            («std-1.0.0-beta.14::hash::Hasher».write h![] H h![] h![]
              h![stateRef, Point.y self])
            (fun _ => [stateRef ↦ ⟨H, final⟩]))
    : STHoare p env
      [stateRef ↦ ⟨H, state⟩]
      («std-1.0.0-beta.14::hash::Hash».hash h![] Point.type h![] h![H] h![self, stateRef])
      (fun _ => [stateRef ↦ ⟨H, final⟩]) := by
  by_cases h_inf : Point.isInfinite self = true
  · simp [h_inf] at h_write
    have h_bool_write :
        STHoare p env
          [stateRef ↦ ⟨H, state⟩]
          («std-1.0.0-beta.14::hash::Hasher».write h![] H h![] h![]
            h![stateRef, @Builtin.CastTp.cast .bool .field _ p (Point.isInfinite self)])
          (fun _ => [stateRef ↦ ⟨H, final⟩]) := by
      simpa [h_inf] using h_write
    exact point_hash_infinite_spec
      (h_hasher := h_hasher)
      (h_inf := h_inf)
      (h_bool_write := h_bool_write)
  · simp [h_inf] at h_write
    rcases h_write with ⟨state1, h_x_write, h_y_write⟩
    exact point_hash_finite_spec
      (h_hasher := h_hasher)
      (h_fin := by simpa using h_inf)
      (h_x_write := h_x_write)
      (h_y_write := h_y_write)

/-- A limb decomposition of a field value is automatically canonical:
`scalar.val < r_scalar < 2^254` forces the high limb below `2^126`. -/
private lemma canonical_mk_of_decomp {p} [Lampe.Crypto.Bn254.Prime p]
    {scalar lo hi : Fp p}
    (hlo : lo.val < Lampe.pow128)
    (heq : scalar.val = lo.val + Lampe.pow128 * hi.val) :
    Scalar.Canonical (Scalar.mk lo hi) := by
  have hval_lt : scalar.val < p.natVal := ZMod.val_lt scalar
  have hp : p.natVal = Lampe.Crypto.Bn254.r_scalar :=
    Lampe.Crypto.Bn254.Prime.natVal_eq_r_scalar
  have hr : Lampe.Crypto.Bn254.r_scalar < 2 ^ 254 := by
    unfold Lampe.Crypto.Bn254.r_scalar
    decide
  have hpow : Lampe.pow128 = 2 ^ 128 := rfl
  have hhi : hi.val < 2 ^ 126 := by
    have h1 : Lampe.pow128 * hi.val < 2 ^ 254 := by omega
    rw [hpow] at h1
    have h2 : (2 : Nat) ^ 254 = 2 ^ 128 * 2 ^ 126 := by norm_num
    rw [h2] at h1
    exact Nat.lt_of_mul_lt_mul_left h1
  exact ⟨hlo, hhi⟩

/-- Spec for `EmbeddedCurveScalar::from_field`. Besides the limb
decomposition that the body's `decompose` call enforces, the
postcondition carries `Scalar.Canonical (Scalar.mk lo hi)`: since
`scalar.val < p < 2^254`, the `Nat` equation already forces
`hi.val < 2^126`, so callers get the MSM gadget's canonicality
precondition for free. -/
theorem scalar_from_field_spec {p} [Lampe.Crypto.Bn254.Prime p]
    {scalar : Fp p} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::embedded_curve_ops::EmbeddedCurveScalar::from_field».call
        h![] h![scalar])
      (fun r =>
        ∃∃ lo hi,
          r = Scalar.mk lo hi ∧
          lo.val < Lampe.pow128 ∧
          hi.val < Lampe.pow128 ∧
          scalar.val = lo.val + Lampe.pow128 * hi.val ∧
          Scalar.Canonical (Scalar.mk lo hi)) := by
  enter_decl
  steps [Lampe.Stdlib.Field.Bn254.decompose_intro (p := p)]
  simp [SLP.exists_pure] at *
  sl
  all_goals aesop (add safe forward canonical_mk_of_decomp)

set_option maxRecDepth 4096 in
/-- Success spec for `EmbeddedCurveScalar::from_bytes`.

The caller must guarantee `offset.toNat + 31 < 64`; otherwise the
Noir loop body indexes `bytes[offset + 31 - i]` (u32 arithmetic) past
the end of the 64-byte array and the circuit aborts. No
`scalar_from_bytes_oob_spec` is currently exposed because Lampe
lacks a standardized failure-spec convention in this project; see
the investigation note immediately below this declaration. -/
theorem scalar_from_bytes_spec {p bytes offset}
    (hbound : offset.toNat + 31 < 64) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::embedded_curve_ops::EmbeddedCurveScalar::from_bytes».call
        h![] h![bytes, offset])
      (fun r =>
        r =
          Scalar.mk
            (Scalar.fromBytesLoAcc bytes offset 16)
            (Scalar.fromBytesHiAcc bytes offset 16)) := by
  enter_decl
  steps
  loop_inv nat fun i _ _ =>
    [v ↦ ⟨.field, (256 ^ i : Fp p)⟩] ⋆
      [lo ↦ ⟨.field, Scalar.fromBytesLoAcc bytes offset i⟩] ⋆
      [hi ↦ ⟨.field, Scalar.fromBytesHiAcc bytes offset i⟩]
  · simp [Scalar.fromBytesHiAcc]
    sl
    all_goals simp
  · intro i _ hhi
    have hhi_nat : i < 16 := by simpa using hhi
    steps
    · rw [Scalar.fromBytesLoAcc_succ]
      have hmod := sub_add_mod_eq i 31 offset.toNat (by omega) (by omega)
      have hidxlt : offset.toNat + 31 - i < (List.Vector.toList bytes).length := by
        simp
        omega
      have hvidxlt : offset.toNat + 31 - i < 64 := by
        simpa using hidxlt
      have hge :
          (List.Vector.toList bytes)[offset.toNat + 31 - i]? =
            some (bytes[offset.toNat + 31 - i]'hvidxlt) := by
        rw [List.getElem?_eq_getElem hidxlt, List.Vector.toList_getElem]
        rfl
      simp only [Scalar.byteAtField, Builtin.CastTp.cast,
        Lens.modify, Option.get_some]
      rw [hge]
      simp [vector_get_eq_getElem, hmod]
      rfl
    · rw [Scalar.fromBytesHiAcc_succ]
      have hmod := sub_add_mod_eq i 15 offset.toNat (by omega) (by omega)
      have hidxlt : offset.toNat + 15 - i < (List.Vector.toList bytes).length := by
        simp
        omega
      have hvidxlt : offset.toNat + 15 - i < 64 := by
        simpa using hidxlt
      have hge :
          (List.Vector.toList bytes)[offset.toNat + 15 - i]? =
            some (bytes[offset.toNat + 15 - i]'hvidxlt) := by
        rw [List.getElem?_eq_getElem hidxlt, List.Vector.toList_getElem]
        rfl
      simp only [Scalar.byteAtField, Builtin.CastTp.cast,
        Lens.modify, Option.get_some]
      rw [hge]
      simp [vector_get_eq_getElem, hmod]
      rfl
  steps
  subst_vars
  rfl

theorem scalar_from_bytes_some_spec {p bytes offset scalar}
    (hsome : Scalar.fromBytes? bytes offset = some scalar) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::embedded_curve_ops::EmbeddedCurveScalar::from_bytes».call
        h![] h![bytes, offset])
      (fun r => r = scalar) := by
  have hvalid : Scalar.validOffset offset := by
    by_cases h : Scalar.validOffset offset
    · exact h
    · rw [Scalar.fromBytes?_eq_none_of_not_validOffset h] at hsome
      contradiction
  have hbound : offset.toNat + 31 < 64 := by
    have hoff : offset.toNat < 33 := by
      simpa [Scalar.validOffset] using hvalid
    omega
  have hcanonical :
      scalar =
        Scalar.mk
          (Scalar.fromBytesLoAcc bytes offset 16)
          (Scalar.fromBytesHiAcc bytes offset 16) := by
    have := hsome
    rw [Scalar.fromBytes?_eq_some_of_validOffset hvalid] at this
    exact (Option.some.inj this).symm
  steps [scalar_from_bytes_spec (p := p) (bytes := bytes) (offset := offset) hbound]
  simpa [hcanonical]

theorem scalar_hash_spec {p H stateRef}
    {self : Scalar.denote p}
    {state state1 final : Tp.denote p H}
    {h_hasher : Lampe.Stdlib.Hash.Hasher.hasImpl env H}
    (h_hi_write : STHoare p env
      [stateRef ↦ ⟨H, state⟩]
      («std-1.0.0-beta.14::hash::Hasher».write h![] H h![] h![]
        h![stateRef, Scalar.hi self])
      (fun _ => [stateRef ↦ ⟨H, state1⟩]))
    (h_lo_write : STHoare p env
      [stateRef ↦ ⟨H, state1⟩]
      («std-1.0.0-beta.14::hash::Hasher».write h![] H h![] h![]
        h![stateRef, Scalar.lo self])
      (fun _ => [stateRef ↦ ⟨H, final⟩]))
    : STHoare p env
      [stateRef ↦ ⟨H, state⟩]
      («std-1.0.0-beta.14::hash::Hash».hash h![] Scalar.type h![] h![H] h![self, stateRef])
      (fun _ => [stateRef ↦ ⟨H, final⟩]) := by
  resolve_trait
  reduce_fn_body
  steps [Lampe.Stdlib.Hash.field_hash_spec (h_write_spec := h_hi_write),
    Lampe.Stdlib.Hash.field_hash_spec (h_write_spec := h_lo_write)]
  all_goals assumption

/-- Internal MSM accumulator (matches the builtin descriptor
structure). -/
private def msmAccFinRange {p : Prime} {N : U 32}
    (points : Tp.denote p (Point.type.array N))
    (scalars : Tp.denote p (Scalar.type.array N))
    (h : ∀ i, (curvePoint? (points.get i)).isSome) :
    (affineCurve p).Point :=
  ∑ i, Scalar.valueNat (scalars.get i) •
    (curvePoint? (points.get i)).get (h i)

/-- Builtin-level MSM spec — result equation only.

The builtin's underlying precondition includes `Scalar.Canonical`
(modelling the gadget's `create_limbed_range_constraint`); we discharge
that canonicality requirement inside the proof but do not surface it
here. Callers that also need the canonicality fact (notably the
Pedersen `_spec_canonical` proofs) consume
`multi_scalar_mul_builtin_combined_spec` instead. -/
theorem multi_scalar_mul_builtin_spec {p N}
    {points : Tp.denote p (Point.type.array N)}
    {scalars : Tp.denote p (Scalar.type.array N)}
    (hOnCurve : ∀ i, (curvePoint? (points.get i)).isSome) :
    STHoare p env ⟦⟧
      (.callBuiltin [Point.type.array N, Scalar.type.array N, .bool] (Point.type.array 1)
        Builtin.multiScalarMul h![points, scalars, true])
      (fun r =>
        r =
          (⟨[encodeCurvePoint
                (msmAccFinRange points scalars hOnCurve)],
              by simp⟩ : Tp.denote p (Point.type.array 1))) := by
  unfold Builtin.multiScalarMul
  show STHoare p env _
    (.callBuiltin [pointTp.array N,
        scalarTp.array N, .bool]
      (pointTp.array 1) _ h![points, scalars, true]) _
  apply STHoare.pureBuiltin_intro_consequence (a := N)
  any_goals rfl
  intro h
  rfl

private theorem multi_scalar_mul_concrete_spec {p N}
    {points : Tp.denote p (Point.type.array N)}
    {scalars : Tp.denote p (Scalar.type.array N)}
    (hOnCurve : ∀ i, (curvePoint? (points.get i)).isSome) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::embedded_curve_ops::multi_scalar_mul».call
        h![N] h![points, scalars])
      (fun r =>
        r = encodeCurvePoint
          (msmAccFinRange points scalars hOnCurve)) := by
  enter_decl
  steps
  apply STHoare.letIn_intro
    (Q := fun r : Tp.denote p (Point.type.array 1) =>
      ⟦r =
        (⟨[encodeCurvePoint
              (msmAccFinRange points scalars hOnCurve)],
            by simp⟩ : Tp.denote p (Point.type.array 1))⟧)
  · exact multi_scalar_mul_builtin_spec (p := p) (N := N)
      (points := points) (scalars := scalars) (hOnCurve := hOnCurve)
  · intro r
    steps
    subst_vars
    rfl

/-- Combined builtin spec: result equation **and** canonicality
(the gadget's `create_limbed_range_constraint` postcondition,
`LO_BITS = 128`, `HI_BITS = 126`, composable with the downstream
uniqueness machinery `Scalar.canonicalDecomp_unique`). This is
the spec callers use when they need both facts without going through
two separate spec applications. The proof is direct because the
builtin's precondition gives us both `onCurve` and canonicality. -/
theorem multi_scalar_mul_builtin_combined_spec {p N}
    {points : Tp.denote p (Point.type.array N)}
    {scalars : Tp.denote p (Scalar.type.array N)}
    (hOnCurve : ∀ i, (curvePoint? (points.get i)).isSome) :
    STHoare p env ⟦⟧
      (.callBuiltin [Point.type.array N, Scalar.type.array N, .bool] (Point.type.array 1)
        Builtin.multiScalarMul h![points, scalars, true])
      (fun r =>
        (∀ i, Scalar.Canonical (scalars.get i)) ∧
        r =
          (⟨[encodeCurvePoint
                (msmAccFinRange points scalars hOnCurve)],
              by simp⟩ : Tp.denote p (Point.type.array 1))) := by
  unfold Builtin.multiScalarMul
  show STHoare p env _
    (.callBuiltin [pointTp.array N,
        scalarTp.array N, .bool]
      (pointTp.array 1) _ h![points, scalars, true]) _
  apply STHoare.pureBuiltin_intro_consequence (a := N)
  any_goals rfl
  rintro ⟨_, hCan⟩
  exact ⟨hCan, rfl⟩

/-- Helper: if `points.toList = Ps.toList.map encodeCurvePoint`, then `points.get i =
encodeCurvePoint (Ps.get i)` for every `i`. -/
private lemma points_get_eq_encode {p : Prime} {N : U 32}
    {points : Tp.denote p (Point.type.array N)}
    {Ps : List.Vector (affineCurve p).Point N.toNat}
    (h_enc : points.toList = Ps.toList.map encodeCurvePoint)
    (i : Fin N.toNat) :
    points.get i = encodeCurvePoint (Ps.get i) := by
  have hi_pts : i.val < points.toList.length := by
    rw [List.Vector.toList_length]; exact i.isLt
  have hi_Ps : i.val < Ps.toList.length := by
    rw [List.Vector.toList_length]; exact i.isLt
  have hpts : points.get i = points.toList[i.val]'hi_pts := by
    rw [List.Vector.get_eq_get_toList]; rfl
  have hPs : Ps.get i = Ps.toList[i.val]'hi_Ps := by
    rw [List.Vector.get_eq_get_toList]; rfl
  rw [hpts, hPs]
  have h' := congrArg (fun l : List _ => l[i.val]?) h_enc
  simp only at h'
  rw [List.getElem?_eq_getElem hi_pts] at h'
  rw [List.getElem?_eq_getElem (by simp)] at h'
  simp [List.getElem_map] at h'
  exact h'

/-- Bridging lemma: when each point is exactly the encoding of `Ps i`,
the MSM accumulator equals the canonical sum
`∑ i, Scalar.valueNat (scalars i) • Ps i`. -/
private lemma msmAccFinRange_eq_sum {p : Prime} {N : U 32}
    {points : Tp.denote p (Point.type.array N)}
    {scalars : Tp.denote p (Scalar.type.array N)}
    {Ps : List.Vector (affineCurve p).Point N.toNat}
    (h_enc : points.toList = Ps.toList.map encodeCurvePoint)
    (hOnCurve : ∀ i, (curvePoint? (points.get i)).isSome) :
    msmAccFinRange points scalars hOnCurve =
      ∑ i, Scalar.valueNat (scalars.get i) • Ps.get i := by
  unfold msmAccFinRange
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hSome :
      curvePoint? (points.get i) = some (Ps.get i) := by
    rw [points_get_eq_encode h_enc i]; simp
  rw [Option.get_of_eq_some _ hSome]

/-- Result-equation spec for `multi_scalar_mul`. When each input point is
the encoding of a Mathlib `WeierstrassCurve.Affine.Point`, the result is
`encodeCurvePoint (∑ Scalar.valueNat (scalars i) • Ps i)`. -/
theorem multi_scalar_mul_spec {p N}
    {points : Tp.denote p (Point.type.array N)}
    {scalars : Tp.denote p (Scalar.type.array N)}
    {Ps : List.Vector (affineCurve p).Point N.toNat}
    (h_enc :
      points.toList = Ps.toList.map encodeCurvePoint) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::embedded_curve_ops::multi_scalar_mul».call
        h![N] h![points, scalars])
      (fun r =>
        r = encodeCurvePoint
          (∑ i, Scalar.valueNat (scalars.get i) • Ps.get i)) := by
  have hOnCurve :
      ∀ i, (curvePoint? (points.get i)).isSome := by
    intro i
    rw [points_get_eq_encode h_enc i]
    simp
  have h := multi_scalar_mul_concrete_spec (p := p) (N := N)
    (points := points) (scalars := scalars) (hOnCurve := hOnCurve)
  rw [msmAccFinRange_eq_sum h_enc hOnCurve] at h
  exact h

/-- Combined wrapper spec: result equation and canonicality together.
Used by Pedersen `_spec_canonical` proofs to extract both facts in a
single `steps` invocation. -/
theorem multi_scalar_mul_combined_spec {p N}
    {points : Tp.denote p (Point.type.array N)}
    {scalars : Tp.denote p (Scalar.type.array N)}
    {Ps : List.Vector (affineCurve p).Point N.toNat}
    (h_enc :
      points.toList = Ps.toList.map encodeCurvePoint) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::embedded_curve_ops::multi_scalar_mul».call
        h![N] h![points, scalars])
      (fun r =>
        (∀ i, Scalar.Canonical (scalars.get i)) ∧
        r = encodeCurvePoint
          (∑ i, Scalar.valueNat (scalars.get i) • Ps.get i)) := by
  have hOnCurve :
      ∀ i, (curvePoint? (points.get i)).isSome := by
    intro i
    rw [points_get_eq_encode h_enc i]
    simp
  -- Compose result-eq spec and canon spec at the wrapper level by
  -- proving inline: re-run the body of multi_scalar_mul (which is
  -- multi_scalar_mul_array_return(...)[0]) using the combined builtin
  -- spec for the body's builtin call.
  enter_decl
  steps
  apply STHoare.letIn_intro
    (Q := fun r : Tp.denote p (Point.type.array 1) =>
      ⟦(∀ i, Scalar.Canonical (scalars.get i)) ∧
       r =
        (⟨[encodeCurvePoint
              (msmAccFinRange points scalars hOnCurve)],
            by simp⟩ : Tp.denote p (Point.type.array 1))⟧)
  · exact multi_scalar_mul_builtin_combined_spec (p := p) (N := N)
      (points := points) (scalars := scalars) (hOnCurve := hOnCurve)
  · intro r
    steps
    -- After steps, the conjunction `(canon ∧ r = ⟨[...], _⟩)` is in
    -- scope. Extract and rebuild the goal's conjunction with the
    -- bridged sum form.
    have hPair :
        (∀ i, Scalar.Canonical (scalars.get i)) ∧
        r = (⟨[encodeCurvePoint
                (msmAccFinRange points scalars hOnCurve)],
            by simp⟩ : Tp.denote p (Point.type.array 1)) := by assumption
    obtain ⟨hCan, hr⟩ := hPair
    refine ⟨hCan, ?_⟩
    subst hr
    subst_vars
    rw [msmAccFinRange_eq_sum h_enc hOnCurve]
    rfl

private theorem fixed_base_scalar_mul_concrete_spec {p}
    {scalar : Scalar.denote p}
    {Pgen : (affineCurve p).Point}
    (h_gen :
      (Point.generator : Point.denote p) =
        encodeCurvePoint Pgen) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::embedded_curve_ops::fixed_base_scalar_mul».call h![] h![scalar])
      (fun r =>
        r = encodeCurvePoint
          (Scalar.valueNat scalar • Pgen)) := by
  enter_decl
  -- The MSM here is over the singleton arrays `[generator]` and `[scalar]`. We prove
  -- the on-curve hypothesis specialised to that singleton (knowing the only entry is
  -- `Point.generator = encodeCurvePoint Pgen`).
  set pointsVec : Tp.denote p (Point.type.array (1 : U 32)) :=
    ⟨[Point.generator], by simp⟩ with hpointsVec
  set scalarsVec : Tp.denote p (Scalar.type.array (1 : U 32)) :=
    ⟨[scalar], by simp⟩ with hscalarsVec
  have hOnCurve :
      ∀ i,
        (curvePoint?
          (List.Vector.get pointsVec i)).isSome := by
    intro i
    have hgi : List.Vector.get pointsVec i = Point.generator := by
      rcases i with ⟨k, hk⟩
      have hk' : k < 1 := by simpa using hk
      interval_cases k
      rfl
    have hcp :
        curvePoint? (List.Vector.get pointsVec i) =
          curvePoint? Point.generator :=
      congrArg _ hgi
    rw [hcp, h_gen]
    simp
  steps [generator_spec,
    multi_scalar_mul_concrete_spec (p := p) (N := (1 : U 32))
      (points := pointsVec)
      (scalars := scalarsVec)
      (hOnCurve := hOnCurve)]
  have hmsm :
      msmAccFinRange pointsVec scalarsVec hOnCurve =
        Scalar.valueNat scalar • Pgen := by
    let Ps : List.Vector (affineCurve p).Point ((1 : U 32).toNat) :=
      ⟨[Pgen], rfl⟩
    have h_enc : pointsVec.toList = Ps.toList.map encodeCurvePoint := by
      show [Point.generator] = [encodeCurvePoint Pgen]
      rw [h_gen]; rfl
    rw [msmAccFinRange_eq_sum (Ps := Ps) h_enc hOnCurve]
    show (∑ i : Fin 1, Scalar.valueNat (scalarsVec.get i) • Ps.get i) = _
    rw [Fin.sum_univ_one]
    rfl
  rename_i hRet
  rw [hmsm] at hRet
  exact hRet

/-- Canonical spec for `fixed_base_scalar_mul`: provided the Grumpkin
generator `Point.generator` is the encoding of some Mathlib
`(affineCurve p).Point` `Pgen`, the result is the encoding of
`Scalar.valueNat scalar • Pgen`.

The hypothesis `h_gen` is a side condition because proving
`(affineCurve p).Nonsingular 1 <generator-y>` for an arbitrary `p`
requires knowing the concrete characteristic; downstream callers
that pin `p` to BN254 discharge it directly (see
`Lampe.Stdlib.EmbeddedCurveOps.Bn254.fixed_base_scalar_mul_bn254_spec`). -/
theorem fixed_base_scalar_mul_spec {p}
    {scalar : Scalar.denote p}
    {Pgen : (affineCurve p).Point}
    (h_gen :
      (Point.generator : Point.denote p) =
        encodeCurvePoint Pgen) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::embedded_curve_ops::fixed_base_scalar_mul».call h![] h![scalar])
      (fun r =>
        r =
          encodeCurvePoint
            (Scalar.valueNat scalar • Pgen)) := by
  exact fixed_base_scalar_mul_concrete_spec (p := p) (scalar := scalar)
    (Pgen := Pgen) (h_gen := h_gen)
