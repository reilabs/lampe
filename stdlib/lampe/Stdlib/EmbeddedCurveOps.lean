import «std-1.0.0-beta.14».Extracted
import Lampe
import Stdlib.Field.Bn254
import Stdlib.Hash.Mod

namespace Lampe.Stdlib.EmbeddedCurveOps

open «std-1.0.0-beta.14»

/-!
### Spec layering convention

Following the `BoundedVec` pattern (see
`Stdlib.Collections.BoundedVec.Methods`), each Noir function whose
return shape admits a high-level semantic statement has **two specs**:

- A **`private theorem foo_concrete_spec`** — faithfully restates the
  imperative Noir source (e.g. `r = Scalar.eq self other`,
  `r = Lampe.Crypto.EmbeddedCurve.add self other`). Used as a proof
  building-block when chaining bigger specs together; not part of the
  public interface.
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

@[simp] theorem type_eq_crypto_pointTp : Point.type = Lampe.Crypto.EmbeddedCurve.pointTp := rfl

def mk {p} (x y : Fp p) (isInfinite : Bool) : Point.denote p :=
  Lampe.Crypto.EmbeddedCurve.mkPoint x y isInfinite

def x {p} (self : Point.denote p) : Fp p := Lampe.Crypto.EmbeddedCurve.pointX self

def y {p} (self : Point.denote p) : Fp p := Lampe.Crypto.EmbeddedCurve.pointY self

def isInfinite {p} (self : Point.denote p) : Bool :=
  Lampe.Crypto.EmbeddedCurve.pointIsInfinite self

def infinity {p} : Point.denote p := Lampe.Crypto.EmbeddedCurve.pointAtInfinity

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
    (P : (Lampe.Crypto.EmbeddedCurve.affineCurve p).Point) :
    Point.neg (Lampe.Crypto.EmbeddedCurve.encodeCurvePoint P) =
      Lampe.Crypto.EmbeddedCurve.encodeCurvePoint (-P) := by
  rcases P with _ | @⟨x, y, hNs⟩
  · show Point.neg (Lampe.Crypto.EmbeddedCurve.encodeCurvePoint
          (0 : (Lampe.Crypto.EmbeddedCurve.affineCurve p).Point)) =
        Lampe.Crypto.EmbeddedCurve.encodeCurvePoint
          (-(0 : (Lampe.Crypto.EmbeddedCurve.affineCurve p).Point))
    rw [neg_zero]
    simp [Point.neg, Lampe.Crypto.EmbeddedCurve.encodeCurvePoint,
      Lampe.Crypto.EmbeddedCurve.pointAtInfinity,
      Lampe.Crypto.EmbeddedCurve.mkPoint,
      Point.x, Point.y, Point.isInfinite, Point.mk,
      Lampe.Crypto.EmbeddedCurve.pointX,
      Lampe.Crypto.EmbeddedCurve.pointY,
      Lampe.Crypto.EmbeddedCurve.pointIsInfinite]
  · simp [Point.neg, Point.x, Point.y, Point.isInfinite, Point.mk,
      Lampe.Crypto.EmbeddedCurve.encodeCurvePoint,
      Lampe.Crypto.EmbeddedCurve.mkPoint,
      Lampe.Crypto.EmbeddedCurve.pointX,
      Lampe.Crypto.EmbeddedCurve.pointY,
      Lampe.Crypto.EmbeddedCurve.pointIsInfinite,
      WeierstrassCurve.Affine.Point.neg,
      Lampe.Crypto.EmbeddedCurve.affineCurve_negY]

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

@[simp] theorem type_eq_crypto_scalarTp : Scalar.type = Lampe.Crypto.EmbeddedCurve.scalarTp := rfl

def mk {p} (lo hi : Fp p) : Scalar.denote p := (lo, hi, ())

def lo {p} (self : Scalar.denote p) : Fp p := Lampe.Crypto.EmbeddedCurve.scalarLo self

def hi {p} (self : Scalar.denote p) : Fp p := Lampe.Crypto.EmbeddedCurve.scalarHi self

def valueNat {p} (self : Scalar.denote p) : Nat :=
  (Scalar.lo self).val + Lampe.Stdlib.Field.Bn254.pow128 * (Scalar.hi self).val

/-- Bridge: stdlib `Scalar.valueNat` agrees with the crypto-side
`scalarValueNat`. The two definitions are equal modulo unfolding the
two `pow128` constants, neither of which is `@[reducible]`. -/
theorem valueNat_eq_scalarValueNat {p} (self : Scalar.denote p) :
    Scalar.valueNat self = Lampe.Crypto.EmbeddedCurve.scalarValueNat self := by
  simp [Scalar.valueNat, Scalar.lo, Scalar.hi,
    Lampe.Crypto.EmbeddedCurve.scalarValueNat,
    Lampe.Stdlib.Field.Bn254.pow128, Lampe.Crypto.EmbeddedCurve.pow128]

/-- The canonical-representative predicate: each limb fits in 128 bits.
This is the well-formedness condition under which `Scalar.eq` agrees
with `Scalar.valueNat` equality. -/
def Canonical {p} (self : Scalar.denote p) : Prop :=
  (Scalar.lo self).val < Lampe.Stdlib.Field.Bn254.pow128 ∧
  (Scalar.hi self).val < Lampe.Stdlib.Field.Bn254.pow128

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
  (List.range i).foldl
    (fun acc j => acc + byteAtField bytes (offset.toNat + 31 - j) * (256 : Fp p) ^ j)
    0

def fromBytesHiAcc {p} (bytes : Tp.denote p ((Tp.u 8).array (64 : U 32)))
    (offset : U 32) (i : Nat) : Fp p :=
  (List.range i).foldl
    (fun acc j => acc + byteAtField bytes (offset.toNat + 15 - j) * (256 : Fp p) ^ j)
    0

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
      lo.val + Lampe.Stdlib.Field.Bn254.pow128 * hi.val := by
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
  simp [fromBytesLoAcc, List.range_succ]

theorem fromBytesHiAcc_succ {p}
    {bytes : Tp.denote p ((Tp.u 8).array (64 : U 32))} {offset : U 32} {i : Nat} :
    fromBytesHiAcc bytes offset (i + 1) =
      fromBytesHiAcc bytes offset i +
        byteAtField bytes (offset.toNat + 15 - i) * (256 : Fp p) ^ i := by
  simp [fromBytesHiAcc, List.range_succ]

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
    {P : (Lampe.Crypto.EmbeddedCurve.affineCurve p).Point}
    (hself : self = Lampe.Crypto.EmbeddedCurve.encodeCurvePoint P) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::ops::arith::Neg».neg h![] Point.type h![] h![] h![self])
      (fun r => r = Lampe.Crypto.EmbeddedCurve.encodeCurvePoint (-P)) := by
  have hEq : Point.neg self = Lampe.Crypto.EmbeddedCurve.encodeCurvePoint (-P) := by
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
  steps
  all_goals try exact ()
  subst_vars
  simp [Point.eq, Point.isInfinite, Point.x, Point.y]

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
    simp [Point.eq, Point.extEq, Point.canonicalizeInfinity, Point.infinity, Point.mk,
      Point.x, Point.y, Point.isInfinite, Lampe.Crypto.EmbeddedCurve.pointX,
      Lampe.Crypto.EmbeddedCurve.pointY, Lampe.Crypto.EmbeddedCurve.pointIsInfinite,
      Lampe.Crypto.EmbeddedCurve.pointAtInfinity, Lampe.Crypto.EmbeddedCurve.mkPoint,
      Prod.mk.injEq, Bool.and_eq_true, decide_eq_true_eq]
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
  steps
  all_goals try exact ()
  subst_vars
  simp [Scalar.eq, Scalar.hi, Scalar.lo, eq_comm]

private lemma scalar_valueNat_inj_canonical {p}
    {self other : Scalar.denote p}
    (hself : Scalar.Canonical self) (hother : Scalar.Canonical other)
    (h : Scalar.valueNat self = Scalar.valueNat other) :
    Scalar.lo self = Scalar.lo other ∧ Scalar.hi self = Scalar.hi other := by
  obtain ⟨hslo, hshi⟩ := hself
  obtain ⟨holo, hohi⟩ := hother
  simp [Scalar.valueNat] at h
  -- h : (lo self).val + pow128 * (hi self).val = (lo other).val + pow128 * (hi other).val
  -- with all four .val terms < pow128. Apply Nat-level uniqueness, then ZMod.val_injective.
  have hlo : (Scalar.lo self).val = (Scalar.lo other).val ∧
             (Scalar.hi self).val = (Scalar.hi other).val := by
    refine ⟨?_, ?_⟩
    · -- mod pow128 of both sides extracts lo
      have : ((Scalar.lo self).val + Lampe.Stdlib.Field.Bn254.pow128 * (Scalar.hi self).val)
              % Lampe.Stdlib.Field.Bn254.pow128 =
            ((Scalar.lo other).val + Lampe.Stdlib.Field.Bn254.pow128 * (Scalar.hi other).val)
              % Lampe.Stdlib.Field.Bn254.pow128 := by rw [h]
      simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hslo, Nat.mod_eq_of_lt holo] at this
      exact this
    · -- div pow128 of both sides extracts hi
      have hpos : 0 < Lampe.Stdlib.Field.Bn254.pow128 := by
        simp [Lampe.Stdlib.Field.Bn254.pow128]
      have hdiv : ((Scalar.lo self).val + Lampe.Stdlib.Field.Bn254.pow128 * (Scalar.hi self).val)
              / Lampe.Stdlib.Field.Bn254.pow128 =
            ((Scalar.lo other).val + Lampe.Stdlib.Field.Bn254.pow128 * (Scalar.hi other).val)
              / Lampe.Stdlib.Field.Bn254.pow128 := by rw [h]
      rw [Nat.add_mul_div_left _ _ hpos, Nat.add_mul_div_left _ _ hpos,
          Nat.div_eq_of_lt hslo, Nat.div_eq_of_lt holo] at hdiv
      simpa using hdiv
  exact ⟨ZMod.val_injective _ hlo.1, ZMod.val_injective _ hlo.2⟩

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
    obtain ⟨hlo, hhi⟩ := scalar_valueNat_inj_canonical hself hother h
    exact ⟨hhi, hlo⟩

theorem embedded_curve_add_builtin_spec {p}
    {point1 point2 : Point.denote p} :
    STHoare p env ⟦⟧
      (.callBuiltin [Point.type, Point.type, .bool] (Point.type.array 1)
        Builtin.embeddedCurveAdd h![point1, point2, true])
      (fun r =>
        r =
          ⟨[Lampe.Crypto.EmbeddedCurve.add point1 point2], by simp⟩) := by
  simpa [Point.type_eq_crypto_pointTp, Builtin.embeddedCurveAdd, Builtin.embeddedCurveAddDesc,
      Builtin.embeddedCurveAddPoint1, Builtin.embeddedCurveAddPoint2] using
    (STHoare.genericTotalPureBuiltin_intro
      (p := p)
      (Γ := env)
      (b := Builtin.embeddedCurveAdd)
      (a := ())
      (sgn := fun (_ : Unit) =>
        ⟨[Lampe.Crypto.EmbeddedCurve.pointTp, Lampe.Crypto.EmbeddedCurve.pointTp, .bool],
          .array Lampe.Crypto.EmbeddedCurve.pointTp 1⟩)
      (desc := Builtin.embeddedCurveAddDesc)
      (args := h![point1, point2, true]) rfl)

theorem embedded_curve_add_inner_spec {p}
    {point1 point2 : Point.denote p} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::embedded_curve_ops::embedded_curve_add_inner».call
        h![] h![point1, point2])
      (fun r => r = Lampe.Crypto.EmbeddedCurve.add point1 point2) := by
  enter_decl
  steps [embedded_curve_add_builtin_spec]
  simpa

theorem embedded_curve_add_spec {p}
    {point1 point2 : Point.denote p} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::embedded_curve_ops::embedded_curve_add».call
        h![] h![point1, point2])
      (fun r => r = Lampe.Crypto.EmbeddedCurve.add point1 point2) := by
  enter_decl
  steps
  all_goals try exact ()
  apply STHoare.iteFalse_intro
  steps [embedded_curve_add_inner_spec]
  assumption

private theorem point_add_concrete_spec {p} {self other : Point.denote p} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::ops::arith::Add».add h![] Point.type h![] h![] h![self, other])
      (fun r => r = Lampe.Crypto.EmbeddedCurve.add self other) := by
  resolve_trait
  steps [embedded_curve_add_spec]
  assumption

/-- Canonical spec for `Add::add` on `EmbeddedCurvePoint`: under
encoded-input hypotheses, Noir's point addition agrees with Mathlib's
affine short-Weierstrass group law on `(affineCurve p).Point`. -/
theorem point_add_spec {p} {self other : Point.denote p}
    {P Q : (Lampe.Crypto.EmbeddedCurve.affineCurve p).Point}
    (hself : self = Lampe.Crypto.EmbeddedCurve.encodeCurvePoint P)
    (hother : other = Lampe.Crypto.EmbeddedCurve.encodeCurvePoint Q) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::ops::arith::Add».add h![] Point.type h![] h![] h![self, other])
      (fun r => r = Lampe.Crypto.EmbeddedCurve.encodeCurvePoint (P + Q)) := by
  steps [point_add_concrete_spec]
  subst_vars
  rw [Lampe.Crypto.EmbeddedCurve.add_encodeCurvePoint]

private theorem point_double_concrete_spec {p} {self : Point.denote p} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::embedded_curve_ops::EmbeddedCurvePoint::double».call h![] h![self])
      (fun r => r = Lampe.Crypto.EmbeddedCurve.add self self) := by
  enter_decl
  steps [embedded_curve_add_spec]
  assumption

/-- Canonical spec for `EmbeddedCurvePoint::double`: under an
encoded-input hypothesis, doubling agrees with Mathlib's `P + P`. -/
theorem point_double_spec {p} {self : Point.denote p}
    {P : (Lampe.Crypto.EmbeddedCurve.affineCurve p).Point}
    (hself : self = Lampe.Crypto.EmbeddedCurve.encodeCurvePoint P) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::embedded_curve_ops::EmbeddedCurvePoint::double».call h![] h![self])
      (fun r => r = Lampe.Crypto.EmbeddedCurve.encodeCurvePoint (P + P)) := by
  have hEq :
      Lampe.Crypto.EmbeddedCurve.add self self =
        Lampe.Crypto.EmbeddedCurve.encodeCurvePoint (P + P) := by
    subst hself
    exact Lampe.Crypto.EmbeddedCurve.add_encodeCurvePoint P P
  have h := point_double_concrete_spec (p := p) (self := self)
  rw [hEq] at h
  exact h

private theorem point_sub_concrete_spec {p} {self other : Point.denote p} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::ops::arith::Sub».sub h![] Point.type h![] h![] h![self, other])
      (fun r => r = Lampe.Crypto.EmbeddedCurve.add self (Point.neg other)) := by
  resolve_trait
  steps [point_neg_concrete_spec, point_add_concrete_spec]
  simpa [Point.neg]

/-- Canonical spec for `Sub::sub` on `EmbeddedCurvePoint`: under
encoded-input hypotheses, point subtraction agrees with Mathlib's
group `P - Q` (equivalently `P + (-Q)`). -/
theorem point_sub_spec {p} {self other : Point.denote p}
    {P Q : (Lampe.Crypto.EmbeddedCurve.affineCurve p).Point}
    (hself : self = Lampe.Crypto.EmbeddedCurve.encodeCurvePoint P)
    (hother : other = Lampe.Crypto.EmbeddedCurve.encodeCurvePoint Q) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::ops::arith::Sub».sub h![] Point.type h![] h![] h![self, other])
      (fun r => r = Lampe.Crypto.EmbeddedCurve.encodeCurvePoint (P + (-Q))) := by
  have hEq :
      Lampe.Crypto.EmbeddedCurve.add self (Point.neg other) =
        Lampe.Crypto.EmbeddedCurve.encodeCurvePoint (P + (-Q)) := by
    subst hself
    subst hother
    rw [Point.neg_encodeCurvePoint]
    exact Lampe.Crypto.EmbeddedCurve.add_encodeCurvePoint P (-Q)
  have h := point_sub_concrete_spec (p := p) (self := self) (other := other)
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
  steps
  simp [h_inf]
  apply STHoare.iteTrue_intro
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
  steps
  simp [h_fin]
  apply STHoare.iteFalse_intro
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

theorem scalar_from_field_spec {p} [Lampe.Stdlib.Field.Bn254.Prime p]
    {scalar : Fp p} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::embedded_curve_ops::EmbeddedCurveScalar::from_field».call
        h![] h![scalar])
      (fun r =>
        ∃∃ lo hi,
          r = Scalar.mk lo hi ∧
          lo.val < Lampe.Stdlib.Field.Bn254.pow128 ∧
          hi.val < Lampe.Stdlib.Field.Bn254.pow128 ∧
          scalar.val = lo.val + Lampe.Stdlib.Field.Bn254.pow128 * hi.val) := by
  enter_decl
  steps [Lampe.Stdlib.Field.Bn254.decompose_intro (p := p)]
  simp [SLP.exists_pure, beq_true, decide_eq_true_eq] at *
  sl
  all_goals aesop

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
  · simp [Scalar.fromBytesLoAcc, Scalar.fromBytesHiAcc]
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
      simp [Scalar.byteAtField, Builtin.CastTp.cast, hmod,
        List.getElem?_eq_getElem hidxlt, List.Vector.toList_getElem, vector_get_eq_getElem]
    · rw [Scalar.fromBytesHiAcc_succ]
      have hmod := sub_add_mod_eq i 15 offset.toNat (by omega) (by omega)
      have hidxlt : offset.toNat + 15 - i < (List.Vector.toList bytes).length := by
        simp
        omega
      simp [Scalar.byteAtField, Builtin.CastTp.cast, hmod,
        List.getElem?_eq_getElem hidxlt, List.Vector.toList_getElem, vector_get_eq_getElem]
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
    injection this with hscalar
    simpa [eq_comm] using hscalar
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
  steps [Lampe.Stdlib.Hash.field_hash_spec (h_write_spec := h_hi_write),
    Lampe.Stdlib.Hash.field_hash_spec (h_write_spec := h_lo_write)]
  all_goals assumption

theorem multi_scalar_mul_builtin_spec {p N}
    {points : Tp.denote p (Point.type.array N)}
    {scalars : Tp.denote p (Scalar.type.array N)} :
    STHoare p env ⟦⟧
      (.callBuiltin [Point.type.array N, Scalar.type.array N, .bool] (Point.type.array 1)
        Builtin.multiScalarMul h![points, scalars, true])
      (fun r =>
        r =
          ⟨[Lampe.Crypto.EmbeddedCurve.multiScalarMul N points scalars], by simp⟩) := by
  simpa [Point.type_eq_crypto_pointTp, Scalar.type_eq_crypto_scalarTp, Builtin.multiScalarMul,
      Builtin.multiScalarMulDesc,
      Builtin.multiScalarMulPoints, Builtin.multiScalarMulScalars] using
    (STHoare.genericTotalPureBuiltin_intro
      (p := p)
      (Γ := env)
      (b := Builtin.multiScalarMul)
      (a := N)
      (sgn := fun n =>
        ⟨[.array Lampe.Crypto.EmbeddedCurve.pointTp n,
          .array Lampe.Crypto.EmbeddedCurve.scalarTp n, .bool],
          .array Lampe.Crypto.EmbeddedCurve.pointTp 1⟩)
      (desc := Builtin.multiScalarMulDesc)
      (args := h![points, scalars, true]) rfl)

private theorem multi_scalar_mul_concrete_spec {p N}
    {points : Tp.denote p (Point.type.array N)}
    {scalars : Tp.denote p (Scalar.type.array N)} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::embedded_curve_ops::multi_scalar_mul».call
        h![N] h![points, scalars])
      (fun r => r = Lampe.Crypto.EmbeddedCurve.multiScalarMul N points scalars) := by
  enter_decl
  steps
  apply STHoare.letIn_intro
    (Q := fun r : Tp.denote p (Point.type.array 1) =>
      ⟦r =
        (⟨[Lampe.Crypto.EmbeddedCurve.multiScalarMul N points scalars], by simp⟩ :
          Tp.denote p (Point.type.array 1))⟧)
  · exact multi_scalar_mul_builtin_spec (p := p) (N := N) (points := points) (scalars := scalars)
  · intro r
    steps
    subst_vars
    rfl

/-- Canonical spec for `multi_scalar_mul`: when each input point is
the encoding of a Mathlib `WeierstrassCurve.Affine.Point`, the MSM
result is the encoding of `Σᵢ scalarValueNat sᵢ • Pᵢ`. -/
theorem multi_scalar_mul_spec {p N}
    {points : Tp.denote p (Point.type.array N)}
    {scalars : Tp.denote p (Scalar.type.array N)}
    {Ps : List.Vector (Lampe.Crypto.EmbeddedCurve.affineCurve p).Point N.toNat}
    (h_enc :
      points.toList = Ps.toList.map Lampe.Crypto.EmbeddedCurve.encodeCurvePoint) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::embedded_curve_ops::multi_scalar_mul».call
        h![N] h![points, scalars])
      (fun r =>
        r = Lampe.Crypto.EmbeddedCurve.encodeCurvePoint
          ((scalars.toList.zip Ps.toList).foldr
            (fun sP acc => Scalar.valueNat sP.1 • sP.2 + acc) 0)) := by
  have hEq :
      Lampe.Crypto.EmbeddedCurve.multiScalarMul N points scalars =
        Lampe.Crypto.EmbeddedCurve.encodeCurvePoint
          ((scalars.toList.zip Ps.toList).foldr
            (fun sP acc => Scalar.valueNat sP.1 • sP.2 + acc) 0) := by
    unfold Lampe.Crypto.EmbeddedCurve.multiScalarMul
    rw [h_enc, Lampe.Crypto.EmbeddedCurve.multiScalarMulList_of_encoded]
    rfl
  have h := multi_scalar_mul_concrete_spec (p := p) (N := N)
    (points := points) (scalars := scalars)
  rw [hEq] at h
  exact h

private theorem fixed_base_scalar_mul_concrete_spec {p}
    {scalar : Scalar.denote p} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::embedded_curve_ops::fixed_base_scalar_mul».call h![] h![scalar])
      (fun r =>
        r =
          Lampe.Crypto.EmbeddedCurve.multiScalarMul (1 : U 32)
            (⟨[Point.generator], by simp⟩ : Tp.denote p (Point.type.array (1 : U 32)))
            (⟨[scalar], by simp⟩ : Tp.denote p (Scalar.type.array (1 : U 32)))) := by
  enter_decl
  steps [generator_spec, multi_scalar_mul_concrete_spec]
  simp_all

/-- Canonical spec for `fixed_base_scalar_mul`: provided the Grumpkin
generator `Point.generator` is the encoding of some Mathlib
`(affineCurve p).Point` `Pgen`, the result is the encoding of
`Scalar.valueNat scalar • Pgen`.

The hypothesis `h_gen` is a side condition because proving
`(affineCurve p).Nonsingular 1 <generator-y>` for an arbitrary `p`
requires knowing the concrete characteristic; downstream callers
that pin `p` to BN254 discharge it directly. -/
theorem fixed_base_scalar_mul_spec {p}
    {scalar : Scalar.denote p}
    {Pgen : (Lampe.Crypto.EmbeddedCurve.affineCurve p).Point}
    (h_gen :
      (Point.generator : Point.denote p) =
        Lampe.Crypto.EmbeddedCurve.encodeCurvePoint Pgen) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::embedded_curve_ops::fixed_base_scalar_mul».call h![] h![scalar])
      (fun r =>
        r =
          Lampe.Crypto.EmbeddedCurve.encodeCurvePoint
            (Scalar.valueNat scalar • Pgen)) := by
  have hEq :
      Lampe.Crypto.EmbeddedCurve.multiScalarMul (1 : U 32)
          (⟨[Point.generator], by simp⟩ : Tp.denote p (Point.type.array (1 : U 32)))
          (⟨[scalar], by simp⟩ : Tp.denote p (Scalar.type.array (1 : U 32))) =
        Lampe.Crypto.EmbeddedCurve.encodeCurvePoint
          (Scalar.valueNat scalar • Pgen) := by
    unfold Lampe.Crypto.EmbeddedCurve.multiScalarMul
    show Lampe.Crypto.EmbeddedCurve.multiScalarMulList [Point.generator] [scalar] = _
    rw [h_gen]
    have hMap :
        ([Lampe.Crypto.EmbeddedCurve.encodeCurvePoint Pgen]
          : List (Point.denote p)) =
          ([Pgen] : List (Lampe.Crypto.EmbeddedCurve.affineCurve p).Point).map
            Lampe.Crypto.EmbeddedCurve.encodeCurvePoint := rfl
    rw [hMap, Lampe.Crypto.EmbeddedCurve.multiScalarMulList_of_encoded]
    simp [List.zip, Scalar.valueNat_eq_scalarValueNat]
  have h := fixed_base_scalar_mul_concrete_spec (p := p) (scalar := scalar)
  rw [hEq] at h
  exact h
