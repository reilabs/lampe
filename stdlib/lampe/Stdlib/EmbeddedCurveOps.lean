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
  (Scalar.lo self).val + Lampe.Crypto.Bn254.pow128 * (Scalar.hi self).val

/-- Bridge: stdlib `Scalar.valueNat` agrees with the crypto-side
`scalarValueNat`. The two definitions are equal modulo unfolding the
two `pow128` constants, neither of which is `@[reducible]`. -/
theorem valueNat_eq_scalarValueNat {p} (self : Scalar.denote p) :
    Scalar.valueNat self = Lampe.Crypto.EmbeddedCurve.scalarValueNat self := by
  simp [Scalar.valueNat, Scalar.lo, Scalar.hi,
    Lampe.Crypto.EmbeddedCurve.scalarValueNat,
    Lampe.Crypto.Bn254.pow128, Lampe.Crypto.EmbeddedCurve.pow128]

/-- The canonical-representative predicate: each limb fits in 128 bits.
This is the well-formedness condition under which `Scalar.eq` agrees
with `Scalar.valueNat` equality. -/
def Canonical {p} (self : Scalar.denote p) : Prop :=
  (Scalar.lo self).val < Lampe.Crypto.Bn254.pow128 ∧
  (Scalar.hi self).val < Lampe.Crypto.Bn254.pow128

/-- The canonical 128-bit-limb decomposition of a field element: split
`f.val` as `(f.val % 2^128, f.val / 2^128)` and re-embed both halves
into `Fp p`. This is the unique `Scalar.Canonical` witness whose limbs
sum to `f` (see `Scalar.canonical_decomp_unique`). -/
def canonicalDecomp {p} (f : Fp p) : Scalar.denote p :=
  Scalar.mk
    ((f.val % Lampe.Crypto.Bn254.pow128 : Nat) : Fp p)
    ((f.val / Lampe.Crypto.Bn254.pow128 : Nat) : Fp p)

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
      lo.val + Lampe.Crypto.Bn254.pow128 * hi.val := by
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
  reduce_fn_body
  steps
  all_goals try exact ()
  subst_vars
  simp [Scalar.eq, Scalar.hi, Scalar.lo, eq_comm]
  rfl

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
      have : ((Scalar.lo self).val + Lampe.Crypto.Bn254.pow128 * (Scalar.hi self).val)
              % Lampe.Crypto.Bn254.pow128 =
            ((Scalar.lo other).val + Lampe.Crypto.Bn254.pow128 * (Scalar.hi other).val)
              % Lampe.Crypto.Bn254.pow128 := by rw [h]
      simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hslo, Nat.mod_eq_of_lt holo] at this
      exact this
    · -- div pow128 of both sides extracts hi
      have hpos : 0 < Lampe.Crypto.Bn254.pow128 := by
        simp [Lampe.Crypto.Bn254.pow128]
      have hdiv : ((Scalar.lo self).val + Lampe.Crypto.Bn254.pow128 * (Scalar.hi self).val)
              / Lampe.Crypto.Bn254.pow128 =
            ((Scalar.lo other).val + Lampe.Crypto.Bn254.pow128 * (Scalar.hi other).val)
              / Lampe.Crypto.Bn254.pow128 := by rw [h]
      rw [Nat.add_mul_div_left _ _ hpos, Nat.add_mul_div_left _ _ hpos,
          Nat.div_eq_of_lt hslo, Nat.div_eq_of_lt holo] at hdiv
      simpa using hdiv
  exact ⟨ZMod.val_injective _ hlo.1, ZMod.val_injective _ hlo.2⟩

/-! ### Canonical scalar decomposition: existence and uniqueness

The two lemmas below establish that, under `[Bn254.Prime p]`, every
field element `f : Fp p` admits a *unique* canonical limb decomposition
`(lo, hi)` with both limbs in `[0, 2^128)` and
`f = lo + 2^128 · hi`. Existence is constructive: `canonicalDecomp f`
is the standard split `(f.val % 2^128, f.val / 2^128)`. Uniqueness is
the Nat-level uniqueness of binary-expansion limbs.

-/

namespace Scalar

private lemma p_lt_pow128_sq {p} [Lampe.Crypto.Bn254.Prime p] :
    p.natVal < Lampe.Crypto.Bn254.pow128 *
      Lampe.Crypto.Bn254.pow128 := by
  have hmod : p.natVal =
      Lampe.Crypto.Bn254.plo +
        Lampe.Crypto.Bn254.pow128 * Lampe.Crypto.Bn254.phi :=
    Lampe.Crypto.Bn254.Prime.natVal_eq_limbs
  have hplo : Lampe.Crypto.Bn254.plo < Lampe.Crypto.Bn254.pow128 := by
    unfold Lampe.Crypto.Bn254.plo Lampe.Crypto.Bn254.pow128; decide
  have hphi : Lampe.Crypto.Bn254.phi < Lampe.Crypto.Bn254.pow128 := by
    unfold Lampe.Crypto.Bn254.phi Lampe.Crypto.Bn254.pow128; decide
  -- plo + pow128 * phi < pow128 + pow128 * (pow128 - 1) = pow128 * pow128
  have hphi_le : Lampe.Crypto.Bn254.phi + 1 ≤ Lampe.Crypto.Bn254.pow128 :=
    Nat.succ_le_of_lt hphi
  have h1 : Lampe.Crypto.Bn254.plo +
      Lampe.Crypto.Bn254.pow128 * Lampe.Crypto.Bn254.phi
        < Lampe.Crypto.Bn254.pow128 +
          Lampe.Crypto.Bn254.pow128 * Lampe.Crypto.Bn254.phi :=
    Nat.add_lt_add_right hplo _
  have h2 : Lampe.Crypto.Bn254.pow128 +
      Lampe.Crypto.Bn254.pow128 * Lampe.Crypto.Bn254.phi =
      Lampe.Crypto.Bn254.pow128 *
        (Lampe.Crypto.Bn254.phi + 1) := by ring
  have h3 : Lampe.Crypto.Bn254.pow128 *
      (Lampe.Crypto.Bn254.phi + 1) ≤
      Lampe.Crypto.Bn254.pow128 * Lampe.Crypto.Bn254.pow128 :=
    Nat.mul_le_mul_left _ hphi_le
  calc p.natVal = Lampe.Crypto.Bn254.plo +
                  Lampe.Crypto.Bn254.pow128 *
                    Lampe.Crypto.Bn254.phi := hmod
    _ < Lampe.Crypto.Bn254.pow128 +
        Lampe.Crypto.Bn254.pow128 *
          Lampe.Crypto.Bn254.phi := h1
    _ = Lampe.Crypto.Bn254.pow128 *
        (Lampe.Crypto.Bn254.phi + 1) := h2
    _ ≤ Lampe.Crypto.Bn254.pow128 *
        Lampe.Crypto.Bn254.pow128 := h3

/-- `canonicalDecomp f` satisfies `Scalar.Canonical`: both its low and
high limbs fit in 128 bits. -/
theorem canonicalDecomp_Canonical {p} [Lampe.Crypto.Bn254.Prime p]
    (f : Fp p) : Scalar.Canonical (Scalar.canonicalDecomp f) := by
  unfold Scalar.canonicalDecomp Scalar.Canonical Scalar.lo Scalar.hi
  refine ⟨?_, ?_⟩
  · -- (((f.val % pow128 : Nat) : Fp p)).val < pow128
    have hmod_lt : f.val % Lampe.Crypto.Bn254.pow128 <
        Lampe.Crypto.Bn254.pow128 := by
      apply Nat.mod_lt
      unfold Lampe.Crypto.Bn254.pow128; decide
    have hmod_lt_p : f.val % Lampe.Crypto.Bn254.pow128 < p.natVal :=
      lt_of_lt_of_le hmod_lt (le_of_lt (Lampe.Crypto.Bn254.pow128_lt_prime (p := p)))
    have : (((f.val % Lampe.Crypto.Bn254.pow128 : Nat) : Fp p)).val =
        f.val % Lampe.Crypto.Bn254.pow128 :=
      ZMod.val_natCast_of_lt hmod_lt_p
    simp only [Lampe.Crypto.EmbeddedCurve.scalarLo, Scalar.mk]
    rw [this]
    exact hmod_lt
  · -- (((f.val / pow128 : Nat) : Fp p)).val < pow128
    have hpos : 0 < Lampe.Crypto.Bn254.pow128 := by
      unfold Lampe.Crypto.Bn254.pow128; decide
    have hf : f.val < p.natVal := f.val_lt
    have hp_lt_sq : p.natVal < Lampe.Crypto.Bn254.pow128 *
        Lampe.Crypto.Bn254.pow128 := p_lt_pow128_sq (p := p)
    have hf_lt_sq : f.val < Lampe.Crypto.Bn254.pow128 *
        Lampe.Crypto.Bn254.pow128 := lt_trans hf hp_lt_sq
    have hdiv_lt : f.val / Lampe.Crypto.Bn254.pow128 <
        Lampe.Crypto.Bn254.pow128 :=
      Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hf_lt_sq)
    have hdiv_lt_p : f.val / Lampe.Crypto.Bn254.pow128 < p.natVal :=
      lt_of_lt_of_le hdiv_lt (le_of_lt (Lampe.Crypto.Bn254.pow128_lt_prime (p := p)))
    have hval : (((f.val / Lampe.Crypto.Bn254.pow128 : Nat) : Fp p)).val =
        f.val / Lampe.Crypto.Bn254.pow128 :=
      ZMod.val_natCast_of_lt hdiv_lt_p
    simp only [Lampe.Crypto.EmbeddedCurve.scalarHi, Scalar.mk]
    rw [hval]
    exact hdiv_lt

/-- The canonical decomposition is a decomposition: its limbs sum (in
`Fp p`) to the original field element. -/
theorem canonicalDecomp_decomposes {p} [Lampe.Crypto.Bn254.Prime p]
    (f : Fp p) :
    f = Scalar.lo (Scalar.canonicalDecomp f) +
        ((Lampe.Crypto.Bn254.pow128 : Nat) : Fp p) *
          Scalar.hi (Scalar.canonicalDecomp f) := by
  unfold Scalar.canonicalDecomp Scalar.lo Scalar.hi
  simp only [Lampe.Crypto.EmbeddedCurve.scalarLo,
    Lampe.Crypto.EmbeddedCurve.scalarHi, Scalar.mk]
  -- Lift the Nat identity `f.val = f.val % pow128 + pow128 * (f.val / pow128)`
  -- to `Fp p`.
  have hNat : f.val =
      f.val % Lampe.Crypto.Bn254.pow128 +
        Lampe.Crypto.Bn254.pow128 *
          (f.val / Lampe.Crypto.Bn254.pow128) := by
    have := Nat.div_add_mod f.val Lampe.Crypto.Bn254.pow128
    omega
  have hf : ((f.val : Nat) : Fp p) = f := ZMod.natCast_zmod_val f
  calc f = ((f.val : Nat) : Fp p) := hf.symm
    _ = ((f.val % Lampe.Crypto.Bn254.pow128 +
          Lampe.Crypto.Bn254.pow128 *
            (f.val / Lampe.Crypto.Bn254.pow128) : Nat) : Fp p) := by rw [← hNat]
    _ = ((f.val % Lampe.Crypto.Bn254.pow128 : Nat) : Fp p) +
          ((Lampe.Crypto.Bn254.pow128 *
              (f.val / Lampe.Crypto.Bn254.pow128) : Nat) : Fp p) := by push_cast; ring
    _ = ((f.val % Lampe.Crypto.Bn254.pow128 : Nat) : Fp p) +
          ((Lampe.Crypto.Bn254.pow128 : Nat) : Fp p) *
            ((f.val / Lampe.Crypto.Bn254.pow128 : Nat) : Fp p) := by push_cast; ring

/-- Nat-level bound: under the `from_field_unsafe` canonical-range
disjunction together with `Scalar.Canonical`, the Nat sum
`lo.val + pow128 * hi.val` lies in `[0, p)` — i.e. matches `f.val`
without modular wrap. Used by `canonical_decomp_unique` below.

The disjunction is essential: branch 1 (`hi = phi ∧ lo.val < plo`) forces
the sum into `[pow128 * phi, p)`; branch 2 (`hi.val < phi`) plus
canonical `lo` forces it into `[0, pow128 * phi)`. Either way, `< p`. -/
private lemma valueNat_lt_p_of_canonical_disj {p}
    [Lampe.Crypto.Bn254.Prime p] {s : Scalar.denote p}
    (hcanon : Scalar.Canonical s)
    (hdisj : ((Scalar.hi s) = ((Lampe.Crypto.Bn254.phi : Nat) : Fp p)
              ∧ (Scalar.lo s).val < Lampe.Crypto.Bn254.plo)
            ∨ (Scalar.hi s).val < Lampe.Crypto.Bn254.phi) :
    (Scalar.lo s).val + Lampe.Crypto.Bn254.pow128 * (Scalar.hi s).val < p.natVal := by
  obtain ⟨hslo, hshi⟩ := hcanon
  have hmod : p.natVal =
      Lampe.Crypto.Bn254.plo +
        Lampe.Crypto.Bn254.pow128 * Lampe.Crypto.Bn254.phi :=
    Lampe.Crypto.Bn254.Prime.natVal_eq_limbs
  have hphi_lt_pow : Lampe.Crypto.Bn254.phi <
      Lampe.Crypto.Bn254.pow128 := by
    unfold Lampe.Crypto.Bn254.phi Lampe.Crypto.Bn254.pow128; decide
  -- (phi : Fp p).val = phi (since phi < pow128 < p).
  have hphi_val : ((Lampe.Crypto.Bn254.phi : Nat) : Fp p).val =
      Lampe.Crypto.Bn254.phi := by
    have hphi_lt_p : Lampe.Crypto.Bn254.phi < p.natVal := by
      have := Lampe.Crypto.Bn254.pow128_lt_prime (p := p)
      omega
    exact ZMod.val_natCast_of_lt hphi_lt_p
  rcases hdisj with ⟨hhi_eq, hlo_lt_plo⟩ | hhi_lt_phi
  · -- Branch 1: lo.val < plo, hi.val = phi.
    have hhi_val : (Scalar.hi s).val = Lampe.Crypto.Bn254.phi := by
      rw [hhi_eq]; exact hphi_val
    rw [hhi_val]
    omega
  · -- Branch 2: hi.val < phi (so + 1 ≤ phi), with lo.val < pow128.
    have hbound : (Scalar.lo s).val +
        Lampe.Crypto.Bn254.pow128 * (Scalar.hi s).val <
        Lampe.Crypto.Bn254.pow128 *
          ((Scalar.hi s).val + 1) := by
      have hexp : Lampe.Crypto.Bn254.pow128 *
          ((Scalar.hi s).val + 1) =
          Lampe.Crypto.Bn254.pow128 +
            Lampe.Crypto.Bn254.pow128 * (Scalar.hi s).val := by ring
      rw [hexp]; omega
    have hmul_le : Lampe.Crypto.Bn254.pow128 *
        ((Scalar.hi s).val + 1) ≤
        Lampe.Crypto.Bn254.pow128 * Lampe.Crypto.Bn254.phi :=
      Nat.mul_le_mul_left _ hhi_lt_phi
    have hle_p : Lampe.Crypto.Bn254.pow128 *
        Lampe.Crypto.Bn254.phi ≤ p.natVal := by
      rw [hmod]; omega
    linarith

/-- The two main consequences used by uniqueness, packaged as the
`Scalar.valueNat`-vs-`Fp p`-val bridge: under disjunction + canonical, the
prover's Nat sum equals `f.val`. -/
private lemma valueNat_eq_val_of_canonical_disj {p}
    [Lampe.Crypto.Bn254.Prime p] {f : Fp p} {s : Scalar.denote p}
    (hcanon : Scalar.Canonical s)
    (hdisj : ((Scalar.hi s) = ((Lampe.Crypto.Bn254.phi : Nat) : Fp p)
              ∧ (Scalar.lo s).val < Lampe.Crypto.Bn254.plo)
            ∨ (Scalar.hi s).val < Lampe.Crypto.Bn254.phi)
    (hdecomp : f = Scalar.lo s +
      ((Lampe.Crypto.Bn254.pow128 : Nat) : Fp p) * Scalar.hi s) :
    Scalar.valueNat s = f.val := by
  have hpow_val : ((Lampe.Crypto.Bn254.pow128 : Nat) : Fp p).val =
      Lampe.Crypto.Bn254.pow128 := Lampe.Crypto.Bn254.pow128_val (p := p)
  have hsum_lt_p : (Scalar.lo s).val +
      Lampe.Crypto.Bn254.pow128 * (Scalar.hi s).val < p.natVal :=
    valueNat_lt_p_of_canonical_disj hcanon hdisj
  have hmul_lt : Lampe.Crypto.Bn254.pow128 * (Scalar.hi s).val < p.natVal := by
    have := Nat.le_add_left
      (Lampe.Crypto.Bn254.pow128 * (Scalar.hi s).val) (Scalar.lo s).val
    omega
  have hmul_lt' : ((Lampe.Crypto.Bn254.pow128 : Nat) : Fp p).val *
      (Scalar.hi s).val < p.natVal := by rw [hpow_val]; exact hmul_lt
  have hmul_val : (((Lampe.Crypto.Bn254.pow128 : Nat) : Fp p) * Scalar.hi s).val =
      Lampe.Crypto.Bn254.pow128 * (Scalar.hi s).val := by
    rw [ZMod.val_mul_of_lt hmul_lt', hpow_val]
  have hsum_lt : (Scalar.lo s).val +
      (((Lampe.Crypto.Bn254.pow128 : Nat) : Fp p) * Scalar.hi s).val < p.natVal := by
    rw [hmul_val]; exact hsum_lt_p
  have hsum_val : ((Scalar.lo s) +
      ((Lampe.Crypto.Bn254.pow128 : Nat) : Fp p) * Scalar.hi s).val =
      (Scalar.lo s).val +
        (((Lampe.Crypto.Bn254.pow128 : Nat) : Fp p) * Scalar.hi s).val :=
    ZMod.val_add_of_lt hsum_lt
  have hf_val : f.val = (Scalar.lo s).val +
      Lampe.Crypto.Bn254.pow128 * (Scalar.hi s).val := by
    have := congrArg ZMod.val hdecomp
    rw [hsum_val, hmul_val] at this
    exact this
  unfold Scalar.valueNat
  omega

/-- **Canonical-limb uniqueness**: any decomposition `s` of a field
element `f` that is `Scalar.Canonical` AND satisfies the
`from_field_unsafe` canonical-range disjunction agrees with
`canonicalDecomp f`.

Combined with `canonicalDecomp_Canonical` and `canonicalDecomp_decomposes`,
this is the existence-and-uniqueness statement
`∃! s, Scalar.Canonical s ∧ disj s ∧ f = s.lo + 2^128 · s.hi` from the
MSM canonicalization plan.

The canonical-range disjunction is essential — *both* `Scalar.Canonical`
limbs alone do not suffice for uniqueness over BN254 (where
`pow128^2 ≈ 4·p`, so a canonical pair can decompose `0` either as
`(0, 0)` or as `(plo, phi)`). The disjunction breaks the tie. -/
theorem canonical_decomp_unique {p} [Lampe.Crypto.Bn254.Prime p]
    {f : Fp p} {s : Scalar.denote p}
    (hcanon : Scalar.Canonical s)
    (hdisj : ((Scalar.hi s) = ((Lampe.Crypto.Bn254.phi : Nat) : Fp p)
              ∧ (Scalar.lo s).val < Lampe.Crypto.Bn254.plo)
            ∨ (Scalar.hi s).val < Lampe.Crypto.Bn254.phi)
    (hdecomp : f = Scalar.lo s +
      ((Lampe.Crypto.Bn254.pow128 : Nat) : Fp p) * Scalar.hi s) :
    s = Scalar.canonicalDecomp f := by
  -- Both s and canonicalDecomp f are canonical decomps of f whose Nat sums
  -- lie in [0, p). Hence their Nat sums equal f.val, so they agree as
  -- `valueNat`. Then `scalar_valueNat_inj_canonical` gives equal limbs.
  have hcanon' : Scalar.Canonical (Scalar.canonicalDecomp f) :=
    Scalar.canonicalDecomp_Canonical f
  have hf_decomp : f = Scalar.lo (Scalar.canonicalDecomp f) +
      ((Lampe.Crypto.Bn254.pow128 : Nat) : Fp p) *
        Scalar.hi (Scalar.canonicalDecomp f) :=
    Scalar.canonicalDecomp_decomposes f
  -- canonicalDecomp's limbs satisfy the disjunction: its Nat sum equals f.val < p,
  -- which by hN1_eq forces either hi = phi ∧ lo < plo (when f.val ≥ pow128*phi)
  -- or hi.val < phi (when f.val < pow128*phi).
  have hd_disj :
      ((Scalar.hi (Scalar.canonicalDecomp f)) =
          ((Lampe.Crypto.Bn254.phi : Nat) : Fp p)
        ∧ (Scalar.lo (Scalar.canonicalDecomp f)).val <
            Lampe.Crypto.Bn254.plo)
      ∨ (Scalar.hi (Scalar.canonicalDecomp f)).val <
            Lampe.Crypto.Bn254.phi := by
    -- Argue from f.val < p = plo + pow128*phi.
    have hmod : p.natVal =
        Lampe.Crypto.Bn254.plo +
          Lampe.Crypto.Bn254.pow128 * Lampe.Crypto.Bn254.phi :=
      Lampe.Crypto.Bn254.Prime.natVal_eq_limbs
    have hpow_pos : 0 < Lampe.Crypto.Bn254.pow128 := by
      unfold Lampe.Crypto.Bn254.pow128; decide
    have hf_lt : f.val < p.natVal := f.val_lt
    -- (lo, hi) = (f.val % pow128, f.val / pow128). Use Nat.div_add_mod.
    have hdm : f.val % Lampe.Crypto.Bn254.pow128 +
        Lampe.Crypto.Bn254.pow128 *
          (f.val / Lampe.Crypto.Bn254.pow128) = f.val := by
      have := Nat.div_add_mod f.val Lampe.Crypto.Bn254.pow128
      omega
    -- Identify lo.val and hi.val on the canonicalDecomp side.
    have hlo_val : (Scalar.lo (Scalar.canonicalDecomp f)).val =
        f.val % Lampe.Crypto.Bn254.pow128 := by
      unfold Scalar.canonicalDecomp Scalar.lo Scalar.mk
      simp only [Lampe.Crypto.EmbeddedCurve.scalarLo]
      have hmod_lt_p : f.val % Lampe.Crypto.Bn254.pow128 < p.natVal := by
        have := Nat.mod_lt f.val hpow_pos
        have := Lampe.Crypto.Bn254.pow128_lt_prime (p := p)
        omega
      exact ZMod.val_natCast_of_lt hmod_lt_p
    have hhi_val : (Scalar.hi (Scalar.canonicalDecomp f)).val =
        f.val / Lampe.Crypto.Bn254.pow128 := by
      unfold Scalar.canonicalDecomp Scalar.hi Scalar.mk
      simp only [Lampe.Crypto.EmbeddedCurve.scalarHi]
      have hp_sq := p_lt_pow128_sq (p := p)
      have hf_lt_sq : f.val < Lampe.Crypto.Bn254.pow128 *
          Lampe.Crypto.Bn254.pow128 := lt_trans hf_lt hp_sq
      have hdiv_lt : f.val / Lampe.Crypto.Bn254.pow128 <
          Lampe.Crypto.Bn254.pow128 :=
        Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hf_lt_sq)
      have hdiv_lt_p : f.val / Lampe.Crypto.Bn254.pow128 < p.natVal := by
        have := Lampe.Crypto.Bn254.pow128_lt_prime (p := p)
        omega
      exact ZMod.val_natCast_of_lt hdiv_lt_p
    -- Now case-split on whether f.val < pow128 * phi.
    by_cases hcase : f.val < Lampe.Crypto.Bn254.pow128 *
        Lampe.Crypto.Bn254.phi
    · right
      rw [hhi_val]
      -- f.val < pow128 * phi ⟹ f.val / pow128 < phi.
      exact Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hcase)
    · left
      push_neg at hcase
      -- f.val ≥ pow128 * phi and f.val < p = plo + pow128*phi.
      -- So f.val = pow128*phi + r where r ∈ [0, plo).
      have hr_lo : f.val - Lampe.Crypto.Bn254.pow128 *
          Lampe.Crypto.Bn254.phi < Lampe.Crypto.Bn254.plo := by
        omega
      -- f.val / pow128 = phi when pow128*phi ≤ f.val < pow128*(phi+1),
      -- and the upper bound is f.val < pow128*phi + pow128 (follows from r < plo < pow128).
      have hplo_lt_pow : Lampe.Crypto.Bn254.plo <
          Lampe.Crypto.Bn254.pow128 := by
        unfold Lampe.Crypto.Bn254.plo Lampe.Crypto.Bn254.pow128; decide
      have hf_lt' : f.val < Lampe.Crypto.Bn254.pow128 *
          (Lampe.Crypto.Bn254.phi + 1) := by
        have : Lampe.Crypto.Bn254.pow128 *
            (Lampe.Crypto.Bn254.phi + 1) =
            Lampe.Crypto.Bn254.pow128 *
              Lampe.Crypto.Bn254.phi +
            Lampe.Crypto.Bn254.pow128 := by ring
        omega
      have hdiv_eq : f.val / Lampe.Crypto.Bn254.pow128 =
          Lampe.Crypto.Bn254.phi := by
        apply Nat.div_eq_of_lt_le
        · rw [Nat.mul_comm]; exact hcase
        · rw [Nat.mul_comm]; exact hf_lt'
      refine ⟨?_, ?_⟩
      · -- Goal: hi (canonicalDecomp f) = (↑phi : Fp p). Since hi := ((f.val / pow128 : Nat) : Fp p)
        -- and f.val / pow128 = phi.
        unfold Scalar.canonicalDecomp Scalar.hi Scalar.mk
        simp only [Lampe.Crypto.EmbeddedCurve.scalarHi]
        rw [hdiv_eq]
      · -- Goal: (lo (canonicalDecomp f)).val < plo.
        rw [hlo_val]
        -- f.val % pow128 = f.val - pow128*phi (since pow128*phi ≤ f.val < pow128*(phi+1)).
        have hmod_eq : f.val % Lampe.Crypto.Bn254.pow128 =
            f.val - Lampe.Crypto.Bn254.pow128 *
              Lampe.Crypto.Bn254.phi := by
          have hsub : f.val = (f.val - Lampe.Crypto.Bn254.pow128 *
              Lampe.Crypto.Bn254.phi) + Lampe.Crypto.Bn254.pow128 *
              Lampe.Crypto.Bn254.phi := by omega
          conv_lhs => rw [hsub]
          rw [Nat.add_mul_mod_self_left,
              Nat.mod_eq_of_lt (lt_of_lt_of_le hr_lo (le_of_lt hplo_lt_pow))]
        omega
  -- Both sides have equal valueNat (= f.val).
  have hs_val_eq : Scalar.valueNat s = f.val :=
    valueNat_eq_val_of_canonical_disj hcanon hdisj hdecomp
  have hd_val_eq : Scalar.valueNat (Scalar.canonicalDecomp f) = f.val :=
    valueNat_eq_val_of_canonical_disj hcanon' hd_disj hf_decomp
  -- Combine: valueNat agrees, so limbs agree.
  have hv_eq : Scalar.valueNat s = Scalar.valueNat (Scalar.canonicalDecomp f) := by
    rw [hs_val_eq, hd_val_eq]
  obtain ⟨hlo_eq, hhi_eq⟩ := scalar_valueNat_inj_canonical hcanon hcanon' hv_eq
  -- s and canonicalDecomp f are 3-tuples (lo, hi, ()); equality of lo, hi gives equality.
  obtain ⟨slo, shi, ⟨⟩⟩ := s
  simp only [Scalar.lo, Scalar.hi, Lampe.Crypto.EmbeddedCurve.scalarLo,
    Lampe.Crypto.EmbeddedCurve.scalarHi] at hlo_eq hhi_eq
  show ((slo, shi, PUnit.unit) : Scalar.denote p) = Scalar.canonicalDecomp f
  rw [hlo_eq, hhi_eq]
  rfl

end Scalar

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
    {point1 point2 : Point.denote p}
    (hOnCurve :
      (Lampe.Crypto.EmbeddedCurve.curvePoint? point1).isSome ∧
        (Lampe.Crypto.EmbeddedCurve.curvePoint? point2).isSome) :
    STHoare p env ⟦⟧
      (.callBuiltin [Point.type, Point.type, .bool] (Point.type.array 1)
        Builtin.embeddedCurveAdd h![point1, point2, true])
      (fun r =>
        r =
          (⟨[Lampe.Crypto.EmbeddedCurve.encodeCurvePoint
                ((Lampe.Crypto.EmbeddedCurve.curvePoint? point1).get hOnCurve.1 +
                  (Lampe.Crypto.EmbeddedCurve.curvePoint? point2).get hOnCurve.2)],
              by simp⟩ : Tp.denote p (Point.type.array 1))) := by
  unfold Builtin.embeddedCurveAdd
  show STHoare p env _
    (.callBuiltin [Lampe.Crypto.EmbeddedCurve.pointTp, Lampe.Crypto.EmbeddedCurve.pointTp, .bool]
      (Lampe.Crypto.EmbeddedCurve.pointTp.array 1) _ h![point1, point2, true]) _
  apply STHoare.pureBuiltin_intro_consequence (a := ())
  any_goals rfl
  rintro ⟨h1, h2⟩
  rfl

theorem embedded_curve_add_inner_spec {p}
    {point1 point2 : Point.denote p}
    (hOnCurve :
      (Lampe.Crypto.EmbeddedCurve.curvePoint? point1).isSome ∧
        (Lampe.Crypto.EmbeddedCurve.curvePoint? point2).isSome) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::embedded_curve_ops::embedded_curve_add_inner».call
        h![] h![point1, point2])
      (fun r =>
        r = Lampe.Crypto.EmbeddedCurve.encodeCurvePoint
          ((Lampe.Crypto.EmbeddedCurve.curvePoint? point1).get hOnCurve.1 +
            (Lampe.Crypto.EmbeddedCurve.curvePoint? point2).get hOnCurve.2)) := by
  enter_decl
  steps [embedded_curve_add_builtin_spec (hOnCurve := hOnCurve)]
  simpa

theorem embedded_curve_add_spec {p}
    {point1 point2 : Point.denote p}
    (hOnCurve :
      (Lampe.Crypto.EmbeddedCurve.curvePoint? point1).isSome ∧
        (Lampe.Crypto.EmbeddedCurve.curvePoint? point2).isSome) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::embedded_curve_ops::embedded_curve_add».call
        h![] h![point1, point2])
      (fun r =>
        r = Lampe.Crypto.EmbeddedCurve.encodeCurvePoint
          ((Lampe.Crypto.EmbeddedCurve.curvePoint? point1).get hOnCurve.1 +
            (Lampe.Crypto.EmbeddedCurve.curvePoint? point2).get hOnCurve.2)) := by
  enter_decl
  steps
  all_goals try exact ()
  apply STHoare.iteFalse_intro
  steps [embedded_curve_add_inner_spec (hOnCurve := hOnCurve)]
  assumption

private theorem point_add_concrete_spec {p} {self other : Point.denote p}
    (hOnCurve :
      (Lampe.Crypto.EmbeddedCurve.curvePoint? self).isSome ∧
        (Lampe.Crypto.EmbeddedCurve.curvePoint? other).isSome) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::ops::arith::Add».add h![] Point.type h![] h![] h![self, other])
      (fun r =>
        r = Lampe.Crypto.EmbeddedCurve.encodeCurvePoint
          ((Lampe.Crypto.EmbeddedCurve.curvePoint? self).get hOnCurve.1 +
            (Lampe.Crypto.EmbeddedCurve.curvePoint? other).get hOnCurve.2)) := by
  resolve_trait
  steps [embedded_curve_add_spec (hOnCurve := hOnCurve)]
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
  have hOnCurve :
      (Lampe.Crypto.EmbeddedCurve.curvePoint? self).isSome ∧
        (Lampe.Crypto.EmbeddedCurve.curvePoint? other).isSome := by
    subst hself
    subst hother
    simp
  have h := point_add_concrete_spec (p := p) (self := self) (other := other)
    (hOnCurve := hOnCurve)
  have hEq :
      Lampe.Crypto.EmbeddedCurve.encodeCurvePoint
          ((Lampe.Crypto.EmbeddedCurve.curvePoint? self).get hOnCurve.1 +
            (Lampe.Crypto.EmbeddedCurve.curvePoint? other).get hOnCurve.2) =
        Lampe.Crypto.EmbeddedCurve.encodeCurvePoint (P + Q) := by
    subst hself
    subst hother
    congr 1 <;> simp
  rw [hEq] at h
  exact h

private theorem point_double_concrete_spec {p} {self : Point.denote p}
    (hOnCurve : (Lampe.Crypto.EmbeddedCurve.curvePoint? self).isSome) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::embedded_curve_ops::EmbeddedCurvePoint::double».call h![] h![self])
      (fun r =>
        r = Lampe.Crypto.EmbeddedCurve.encodeCurvePoint
          ((Lampe.Crypto.EmbeddedCurve.curvePoint? self).get hOnCurve +
            (Lampe.Crypto.EmbeddedCurve.curvePoint? self).get hOnCurve)) := by
  enter_decl
  steps [embedded_curve_add_spec (hOnCurve := ⟨hOnCurve, hOnCurve⟩)]
  assumption

/-- Canonical spec for `EmbeddedCurvePoint::double`: under an
encoded-input hypothesis, doubling agrees with Mathlib's `P + P`. -/
theorem point_double_spec {p} {self : Point.denote p}
    {P : (Lampe.Crypto.EmbeddedCurve.affineCurve p).Point}
    (hself : self = Lampe.Crypto.EmbeddedCurve.encodeCurvePoint P) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::embedded_curve_ops::EmbeddedCurvePoint::double».call h![] h![self])
      (fun r => r = Lampe.Crypto.EmbeddedCurve.encodeCurvePoint (P + P)) := by
  have hOnCurve : (Lampe.Crypto.EmbeddedCurve.curvePoint? self).isSome := by
    subst hself
    simp
  have h := point_double_concrete_spec (p := p) (self := self) (hOnCurve := hOnCurve)
  have hEq :
      Lampe.Crypto.EmbeddedCurve.encodeCurvePoint
          ((Lampe.Crypto.EmbeddedCurve.curvePoint? self).get hOnCurve +
            (Lampe.Crypto.EmbeddedCurve.curvePoint? self).get hOnCurve) =
        Lampe.Crypto.EmbeddedCurve.encodeCurvePoint (P + P) := by
    subst hself
    congr 1 <;> simp
  rw [hEq] at h
  exact h

private theorem point_sub_concrete_spec {p} {self other : Point.denote p}
    (hOnCurve :
      (Lampe.Crypto.EmbeddedCurve.curvePoint? self).isSome ∧
        (Lampe.Crypto.EmbeddedCurve.curvePoint? (Point.neg other)).isSome) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::ops::arith::Sub».sub h![] Point.type h![] h![] h![self, other])
      (fun r =>
        r = Lampe.Crypto.EmbeddedCurve.encodeCurvePoint
          ((Lampe.Crypto.EmbeddedCurve.curvePoint? self).get hOnCurve.1 +
            (Lampe.Crypto.EmbeddedCurve.curvePoint? (Point.neg other)).get hOnCurve.2)) := by
  resolve_trait
  steps [point_neg_concrete_spec, point_add_concrete_spec (hOnCurve := hOnCurve)]
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
  have hOnCurve :
      (Lampe.Crypto.EmbeddedCurve.curvePoint? self).isSome ∧
        (Lampe.Crypto.EmbeddedCurve.curvePoint? (Point.neg other)).isSome := by
    subst hself
    subst hother
    refine ⟨by simp, ?_⟩
    rw [Point.neg_encodeCurvePoint]
    simp
  have h := point_sub_concrete_spec (p := p) (self := self) (other := other)
    (hOnCurve := hOnCurve)
  have hEq :
      Lampe.Crypto.EmbeddedCurve.encodeCurvePoint
          ((Lampe.Crypto.EmbeddedCurve.curvePoint? self).get hOnCurve.1 +
            (Lampe.Crypto.EmbeddedCurve.curvePoint? (Point.neg other)).get hOnCurve.2) =
        Lampe.Crypto.EmbeddedCurve.encodeCurvePoint (P + (-Q)) := by
    subst hself
    subst hother
    simp only [Point.neg_encodeCurvePoint]
    congr 1 <;> simp
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

theorem scalar_from_field_spec {p} [Lampe.Crypto.Bn254.Prime p]
    {scalar : Fp p} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::embedded_curve_ops::EmbeddedCurveScalar::from_field».call
        h![] h![scalar])
      (fun r =>
        ∃∃ lo hi,
          r = Scalar.mk lo hi ∧
          lo.val < Lampe.Crypto.Bn254.pow128 ∧
          hi.val < Lampe.Crypto.Bn254.pow128 ∧
          scalar.val = lo.val + Lampe.Crypto.Bn254.pow128 * hi.val) := by
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
      have hvidxlt : offset.toNat + 31 - i < 64 := by
        simpa using hidxlt
      have hge :
          (List.Vector.toList bytes)[offset.toNat + 31 - i]? =
            some (bytes[offset.toNat + 31 - i]'hvidxlt) := by
        rw [List.getElem?_eq_getElem hidxlt, List.Vector.toList_getElem]
        rfl
      simp only [Scalar.byteAtField, Builtin.CastTp.cast, hmod,
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
      simp only [Scalar.byteAtField, Builtin.CastTp.cast, hmod,
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
    (h : ∀ i, (Lampe.Crypto.EmbeddedCurve.curvePoint? (points.get i)).isSome) :
    (Lampe.Crypto.EmbeddedCurve.affineCurve p).Point :=
  ∑ i, Lampe.Crypto.EmbeddedCurve.scalarValueNat (scalars.get i) •
    (Lampe.Crypto.EmbeddedCurve.curvePoint? (points.get i)).get (h i)

theorem multi_scalar_mul_builtin_spec {p N}
    {points : Tp.denote p (Point.type.array N)}
    {scalars : Tp.denote p (Scalar.type.array N)}
    (hOnCurve : ∀ i, (Lampe.Crypto.EmbeddedCurve.curvePoint? (points.get i)).isSome) :
    STHoare p env ⟦⟧
      (.callBuiltin [Point.type.array N, Scalar.type.array N, .bool] (Point.type.array 1)
        Builtin.multiScalarMul h![points, scalars, true])
      (fun r =>
        r =
          (⟨[Lampe.Crypto.EmbeddedCurve.encodeCurvePoint
                (msmAccFinRange points scalars hOnCurve)],
              by simp⟩ : Tp.denote p (Point.type.array 1))) := by
  unfold Builtin.multiScalarMul
  show STHoare p env _
    (.callBuiltin [Lampe.Crypto.EmbeddedCurve.pointTp.array N,
        Lampe.Crypto.EmbeddedCurve.scalarTp.array N, .bool]
      (Lampe.Crypto.EmbeddedCurve.pointTp.array 1) _ h![points, scalars, true]) _
  apply STHoare.pureBuiltin_intro_consequence (a := N)
  any_goals rfl
  intro h
  rfl

private theorem multi_scalar_mul_concrete_spec {p N}
    {points : Tp.denote p (Point.type.array N)}
    {scalars : Tp.denote p (Scalar.type.array N)}
    (hOnCurve : ∀ i, (Lampe.Crypto.EmbeddedCurve.curvePoint? (points.get i)).isSome) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::embedded_curve_ops::multi_scalar_mul».call
        h![N] h![points, scalars])
      (fun r =>
        r = Lampe.Crypto.EmbeddedCurve.encodeCurvePoint
          (msmAccFinRange points scalars hOnCurve)) := by
  enter_decl
  steps
  apply STHoare.letIn_intro
    (Q := fun r : Tp.denote p (Point.type.array 1) =>
      ⟦r =
        (⟨[Lampe.Crypto.EmbeddedCurve.encodeCurvePoint
              (msmAccFinRange points scalars hOnCurve)],
            by simp⟩ : Tp.denote p (Point.type.array 1))⟧)
  · exact multi_scalar_mul_builtin_spec (p := p) (N := N)
      (points := points) (scalars := scalars) (hOnCurve := hOnCurve)
  · intro r
    steps
    subst_vars
    rfl

/-- Helper: if `points.toList = Ps.toList.map encodeCurvePoint`, then `points.get i =
encodeCurvePoint (Ps.get i)` for every `i`. -/
private lemma points_get_eq_encode {p : Prime} {N : U 32}
    {points : Tp.denote p (Point.type.array N)}
    {Ps : List.Vector (Lampe.Crypto.EmbeddedCurve.affineCurve p).Point N.toNat}
    (h_enc : points.toList = Ps.toList.map Lampe.Crypto.EmbeddedCurve.encodeCurvePoint)
    (i : Fin N.toNat) :
    points.get i = Lampe.Crypto.EmbeddedCurve.encodeCurvePoint (Ps.get i) := by
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
  rw [List.getElem?_eq_getElem (by simp [hi_Ps])] at h'
  simp [List.getElem_map] at h'
  exact h'

/-- Bridging lemma: when each point is exactly the encoding of `Ps i`,
the MSM accumulator equals the canonical sum
`∑ i, Scalar.valueNat (scalars i) • Ps i`. -/
private lemma msmAccFinRange_eq_sum {p : Prime} {N : U 32}
    {points : Tp.denote p (Point.type.array N)}
    {scalars : Tp.denote p (Scalar.type.array N)}
    {Ps : List.Vector (Lampe.Crypto.EmbeddedCurve.affineCurve p).Point N.toNat}
    (h_enc : points.toList = Ps.toList.map Lampe.Crypto.EmbeddedCurve.encodeCurvePoint)
    (hOnCurve : ∀ i, (Lampe.Crypto.EmbeddedCurve.curvePoint? (points.get i)).isSome) :
    msmAccFinRange points scalars hOnCurve =
      ∑ i, Scalar.valueNat (scalars.get i) • Ps.get i := by
  unfold msmAccFinRange
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hSome :
      Lampe.Crypto.EmbeddedCurve.curvePoint? (points.get i) = some (Ps.get i) := by
    rw [points_get_eq_encode h_enc i]; simp
  rw [Option.get_of_eq_some _ hSome, ← Scalar.valueNat_eq_scalarValueNat]

/-- Canonical spec for `multi_scalar_mul`: when each input point is
the encoding of a Mathlib `WeierstrassCurve.Affine.Point`, the MSM
result is the encoding of `∑ᵢ Scalar.valueNat (scalars i) • Ps i`. -/
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
          (∑ i, Scalar.valueNat (scalars.get i) • Ps.get i)) := by
  have hOnCurve :
      ∀ i, (Lampe.Crypto.EmbeddedCurve.curvePoint? (points.get i)).isSome := by
    intro i
    rw [points_get_eq_encode h_enc i]
    simp
  have h := multi_scalar_mul_concrete_spec (p := p) (N := N)
    (points := points) (scalars := scalars) (hOnCurve := hOnCurve)
  rw [msmAccFinRange_eq_sum h_enc hOnCurve] at h
  exact h

private theorem fixed_base_scalar_mul_concrete_spec {p}
    {scalar : Scalar.denote p}
    {Pgen : (Lampe.Crypto.EmbeddedCurve.affineCurve p).Point}
    (h_gen :
      (Point.generator : Point.denote p) =
        Lampe.Crypto.EmbeddedCurve.encodeCurvePoint Pgen) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::embedded_curve_ops::fixed_base_scalar_mul».call h![] h![scalar])
      (fun r =>
        r = Lampe.Crypto.EmbeddedCurve.encodeCurvePoint
          (Lampe.Crypto.EmbeddedCurve.scalarValueNat scalar • Pgen)) := by
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
        (Lampe.Crypto.EmbeddedCurve.curvePoint?
          (List.Vector.get pointsVec i)).isSome := by
    intro i
    have hgi : List.Vector.get pointsVec i = Point.generator := by
      rcases i with ⟨k, hk⟩
      have hk' : k < 1 := by simpa using hk
      interval_cases k
      rfl
    have hcp :
        Lampe.Crypto.EmbeddedCurve.curvePoint? (List.Vector.get pointsVec i) =
          Lampe.Crypto.EmbeddedCurve.curvePoint? Point.generator :=
      congrArg _ hgi
    rw [hcp, h_gen]
    simp
  steps [generator_spec,
    multi_scalar_mul_concrete_spec (p := p) (N := (1 : U 32))
      (points := pointsVec)
      (scalars := scalarsVec)
      (hOnCurve := hOnCurve)]
  -- The hypothesis a✝ states v = encodeCurvePoint (msmAccFinRange pointsVec scalarsVec hOnCurve).
  -- Reduce via the bridge lemma + `Fin.sum_univ_one` for the singleton.
  have hmsm :
      msmAccFinRange pointsVec scalarsVec hOnCurve =
        Lampe.Crypto.EmbeddedCurve.scalarValueNat scalar • Pgen := by
    let Ps : List.Vector (Lampe.Crypto.EmbeddedCurve.affineCurve p).Point ((1 : U 32).toNat) :=
      ⟨[Pgen], rfl⟩
    have h_enc : pointsVec.toList = Ps.toList.map Lampe.Crypto.EmbeddedCurve.encodeCurvePoint := by
      show [Point.generator] = [Lampe.Crypto.EmbeddedCurve.encodeCurvePoint Pgen]
      rw [h_gen]; rfl
    rw [msmAccFinRange_eq_sum (Ps := Ps) h_enc hOnCurve]
    show (∑ i : Fin 1, Scalar.valueNat (scalarsVec.get i) • Ps.get i) = _
    rw [Fin.sum_univ_one]
    show Scalar.valueNat scalar • Pgen =
      Lampe.Crypto.EmbeddedCurve.scalarValueNat scalar • Pgen
    rw [Scalar.valueNat_eq_scalarValueNat]
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
  have h := fixed_base_scalar_mul_concrete_spec (p := p) (scalar := scalar)
    (Pgen := Pgen) (h_gen := h_gen)
  rw [Scalar.valueNat_eq_scalarValueNat]
  exact h
