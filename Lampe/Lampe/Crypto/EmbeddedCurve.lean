import Lampe.Tp
import Lampe.Crypto.Bn254
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
  .tuple (some "«std-1.0.0-beta.25::embedded_curve_ops::EmbeddedCurvePoint»")
    [.field, .field, .bool]

@[reducible]
def scalarTp : Tp :=
  .tuple (some "«std-1.0.0-beta.25::embedded_curve_ops::EmbeddedCurveScalar»")
    [.field, .field]

@[reducible]
def Point (p : Prime) := Tp.denote p pointTp

@[reducible]
def Scalar (p : Prime) := Tp.denote p scalarTp

def pointX {p : Prime} (pt : Point p) : Fp p := pt.1
def pointY {p : Prime} (pt : Point p) : Fp p := pt.2.1
def pointIsInfinite {p : Prime} (pt : Point p) : Bool := pt.2.2.1

def Scalar.lo {p : Prime} (s : Scalar p) : Fp p := s.1
def Scalar.hi {p : Prime} (s : Scalar p) : Fp p := s.2.1

@[reducible]
def mkScalar {p : Prime} (lo hi : Fp p) : Scalar p := (lo, hi, ())

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

namespace Scalar

def valueNat {p : Prime} (s : Scalar p) : Nat :=
  s.lo.val + Lampe.pow128 * s.hi.val

/-- Per-scalar limb-range canonicality matching the in-circuit constraints
that Barretenberg's MSM gadget (`cycle_group::batch_mul`) emits on every
input scalar via `create_limbed_range_constraint`:

- `s.lo.val < 2^128` (`LO_BITS = 128`)
- `s.hi.val < 2^126` (`HI_BITS = 126`)

Together the bounds guarantee a *unique* limb decomposition of a value
below `2^254`. Note `2^254` exceeds the (≈ 254-bit) scalar modulus, so
this is limb-uniqueness, not modular canonicity: a value may still
represent a scalar above the modulus.

Justified against Barretenberg @ aztec-packages 7e94c2c0e32820e25e20d39a426d546dae56a34f:
* widths: LO_BITS = 128, HI_BITS = 126 (static_asserted), stdlib/primitives/group/cycle_scalar.hpp#L38-L44
* enforcement: `batch_mul` range-constrains each witness limb via `create_limbed_range_constraint`
  (variable-base: straus_scalar_slice.cpp#L58-L60; fixed-base: 128/126-bit plookup multitables,
  fixed_base_params.hpp#L30-L31; constant-infinity-point carve-out: cycle_group.cpp#L1266-L1275)
* caveat: scalars whose limbs are both circuit constants are trusted unchecked (Noir only validates
  constants against the 254-bit Field width); the bound is backend-enforced only for witness limbs. -/
def Canonical {p : Prime} (s : Scalar p) : Prop :=
  s.lo.val < Lampe.pow128 ∧ s.hi.val < 2 ^ 126

instance {p : Prime} (s : Scalar p) : Decidable (Canonical s) := by
  unfold Canonical
  exact instDecidableAnd

/-! ### Canonical scalar decomposition: existence and uniqueness

Under `[Bn254.Prime p]`, every field element `f : Fp p` admits a
*unique* canonical limb decomposition `(lo, hi)` that satisfies
`Canonical`, satisfies the canonical-range disjunction enforced
by the stdlib's `from_field_unsafe` (lexicographic comparison against
the prime's own limbs `(plo, phi)`), and sums to `f = lo + 2^128 · hi`.
Existence is constructive: `canonicalDecomp f` is the standard split
`(f.val % 2^128, f.val / 2^128)`. Uniqueness is the Nat-level
uniqueness of binary-expansion limbs.
-/

/-- The canonical 128-bit-limb decomposition of a field element: split
`f.val` as `(f.val % 2^128, f.val / 2^128)` and re-embed both halves
into `Fp p`. This is the unique `Canonical` witness whose limbs
sum to `f` (see `canonicalDecomp_unique`). -/
def canonicalDecomp {p : Prime} (f : Fp p) : Scalar p :=
  mkScalar
    ((f.val % Lampe.pow128 : Nat) : Fp p)
    ((f.val / Lampe.pow128 : Nat) : Fp p)

/-- Limb-value injectivity on canonical scalars: two `Canonical`
scalars with the same `valueNat` have identical limbs. -/
lemma valueNat_inj_canonical {p : Prime} {s t : Scalar p}
    (hs : Canonical s) (ht : Canonical t)
    (h : valueNat s = valueNat t) :
    s.lo = t.lo ∧ s.hi = t.hi := by
  obtain ⟨hslo, hshi⟩ := hs
  obtain ⟨htlo, hthi⟩ := ht
  simp [valueNat] at h
  -- h : (lo s).val + pow128 * (hi s).val = (lo t).val + pow128 * (hi t).val
  -- with both .val low limbs < pow128. Apply Nat-level uniqueness, then
  -- ZMod.val_injective.
  have hval : (lo s).val = (lo t).val ∧
      (hi s).val = (hi t).val := by
    refine ⟨?_, ?_⟩
    · -- mod pow128 of both sides extracts lo
      have : ((lo s).val + Lampe.pow128 * (hi s).val) % Lampe.pow128 =
          ((lo t).val + Lampe.pow128 * (hi t).val) % Lampe.pow128 := by
        rw [h]
      simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hslo,
        Nat.mod_eq_of_lt htlo] at this
      exact this
    · -- div pow128 of both sides extracts hi
      have hpos : 0 < Lampe.pow128 := by
        simp [Lampe.pow128]
      have hdiv : ((lo s).val + Lampe.pow128 * (hi s).val) / Lampe.pow128 =
          ((lo t).val + Lampe.pow128 * (hi t).val) / Lampe.pow128 := by
        rw [h]
      rw [Nat.add_mul_div_left _ _ hpos, Nat.add_mul_div_left _ _ hpos,
          Nat.div_eq_of_lt hslo, Nat.div_eq_of_lt htlo] at hdiv
      simpa using hdiv
  exact ⟨ZMod.val_injective _ hval.1, ZMod.val_injective _ hval.2⟩

private lemma p_lt_pow128_sq {p : Prime} [Bn254.Prime p] :
    p.natVal < Lampe.pow128 * Lampe.pow128 := by
  have hmod : p.natVal = Bn254.plo + Lampe.pow128 * Bn254.phi :=
    Bn254.Prime.natVal_eq_limbs
  have hplo : Bn254.plo < Lampe.pow128 := by
    unfold Bn254.plo Lampe.pow128
    decide
  have hphi : Bn254.phi < Lampe.pow128 := by
    unfold Bn254.phi Lampe.pow128
    decide
  -- plo + pow128 * phi < pow128 + pow128 * (pow128 - 1) = pow128 * pow128
  have hphi_le : Bn254.phi + 1 ≤ Lampe.pow128 :=
    Nat.succ_le_of_lt hphi
  have h1 : Bn254.plo + Lampe.pow128 * Bn254.phi
      < Lampe.pow128 + Lampe.pow128 * Bn254.phi :=
    Nat.add_lt_add_right hplo _
  have h2 : Lampe.pow128 + Lampe.pow128 * Bn254.phi =
      Lampe.pow128 * (Bn254.phi + 1) := by ring
  have h3 : Lampe.pow128 * (Bn254.phi + 1) ≤ Lampe.pow128 * Lampe.pow128 :=
    Nat.mul_le_mul_left _ hphi_le
  calc p.natVal = Bn254.plo + Lampe.pow128 * Bn254.phi := hmod
    _ < Lampe.pow128 + Lampe.pow128 * Bn254.phi := h1
    _ = Lampe.pow128 * (Bn254.phi + 1) := h2
    _ ≤ Lampe.pow128 * Lampe.pow128 := h3

/-- `canonicalDecomp f` satisfies `Canonical`: the low limb fits
in 128 bits and the high limb in 126 bits. -/
theorem canonicalDecomp_Canonical {p : Prime} [Bn254.Prime p]
    (f : Fp p) : Canonical (canonicalDecomp f) := by
  unfold canonicalDecomp Canonical lo hi
  refine ⟨?_, ?_⟩
  · -- (((f.val % pow128 : Nat) : Fp p)).val < pow128
    have hmod_lt : f.val % Lampe.pow128 < Lampe.pow128 := by
      apply Nat.mod_lt
      unfold Lampe.pow128
      decide
    have hmod_lt_p : f.val % Lampe.pow128 < p.natVal :=
      lt_of_lt_of_le hmod_lt (le_of_lt (Bn254.pow128_lt_prime (p := p)))
    have : (((f.val % Lampe.pow128 : Nat) : Fp p)).val = f.val % Lampe.pow128 :=
      ZMod.val_natCast_of_lt hmod_lt_p
    rw [this]
    exact hmod_lt
  · -- (((f.val / pow128 : Nat) : Fp p)).val < 2 ^ 126.
    -- f.val < p = plo + pow128 * phi < pow128 * 2^126, so
    -- f.val / pow128 < 2^126 — matches the gadget's `HI_BITS = 126`.
    have hpos : 0 < Lampe.pow128 := by
      unfold Lampe.pow128
      decide
    have hf : f.val < p.natVal := f.val_lt
    have hmod : p.natVal = Bn254.plo + Lampe.pow128 * Bn254.phi :=
      Bn254.Prime.natVal_eq_limbs
    have hplo_lt_pow : Bn254.plo < Lampe.pow128 := by
      unfold Bn254.plo Lampe.pow128
      decide
    have hphi_lt_2_126 : Bn254.phi < 2 ^ 126 := by
      unfold Bn254.phi
      decide
    have hphi_succ_le : Bn254.phi + 1 ≤ 2 ^ 126 :=
      Nat.succ_le_of_lt hphi_lt_2_126
    -- f.val < p ≤ pow128 * (phi + 1) ≤ pow128 * 2^126.
    have hp_lt_mul : p.natVal < Lampe.pow128 * (Bn254.phi + 1) := by
      have hexp : Lampe.pow128 * (Bn254.phi + 1) =
          Lampe.pow128 + Lampe.pow128 * Bn254.phi := by ring
      omega
    have hp_lt_2_126 : p.natVal < Lampe.pow128 * 2 ^ 126 :=
      lt_of_lt_of_le hp_lt_mul (Nat.mul_le_mul_left _ hphi_succ_le)
    have hf_lt_2_126 : f.val < Lampe.pow128 * 2 ^ 126 :=
      lt_trans hf hp_lt_2_126
    have hdiv_lt : f.val / Lampe.pow128 < 2 ^ 126 :=
      Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hf_lt_2_126)
    -- The weaker `< pow128` bound (used to map into Fp via val_natCast_of_lt).
    have h2_126_lt_pow128 : (2 : Nat) ^ 126 < Lampe.pow128 := by
      unfold Lampe.pow128
      decide
    have hdiv_lt_pow : f.val / Lampe.pow128 < Lampe.pow128 :=
      lt_trans hdiv_lt h2_126_lt_pow128
    have hdiv_lt_p : f.val / Lampe.pow128 < p.natVal :=
      lt_of_lt_of_le hdiv_lt_pow (le_of_lt (Bn254.pow128_lt_prime (p := p)))
    have hval : (((f.val / Lampe.pow128 : Nat) : Fp p)).val = f.val / Lampe.pow128 :=
      ZMod.val_natCast_of_lt hdiv_lt_p
    rw [hval]
    exact hdiv_lt

/-- The canonical decomposition is a decomposition: its limbs sum (in
`Fp p`) to the original field element. -/
theorem canonicalDecomp_decomposes {p : Prime} [Bn254.Prime p]
    (f : Fp p) :
    f = (canonicalDecomp f).lo +
        ((Lampe.pow128 : Nat) : Fp p) * (canonicalDecomp f).hi := by
  unfold canonicalDecomp lo hi
  -- Lift the Nat identity `f.val = f.val % pow128 + pow128 * (f.val / pow128)`
  -- to `Fp p`.
  have hNat : f.val =
      f.val % Lampe.pow128 + Lampe.pow128 * (f.val / Lampe.pow128) := by
    have := Nat.div_add_mod f.val Lampe.pow128
    omega
  have hf : ((f.val : Nat) : Fp p) = f := ZMod.natCast_zmod_val f
  calc f = ((f.val : Nat) : Fp p) := hf.symm
    _ = ((f.val % Lampe.pow128 +
          Lampe.pow128 * (f.val / Lampe.pow128) : Nat) : Fp p) := by rw [← hNat]
    _ = ((f.val % Lampe.pow128 : Nat) : Fp p) +
          ((Lampe.pow128 * (f.val / Lampe.pow128) : Nat) : Fp p) := by push_cast; ring
    _ = ((f.val % Lampe.pow128 : Nat) : Fp p) +
          ((Lampe.pow128 : Nat) : Fp p) *
            ((f.val / Lampe.pow128 : Nat) : Fp p) := by push_cast; ring

/-- Nat-level bound: under the `from_field_unsafe` canonical-range
disjunction together with `Canonical`, the Nat sum
`lo.val + pow128 * hi.val` lies in `[0, p)` — i.e. matches `f.val`
without modular wrap. Used by `canonicalDecomp_unique` below.

The disjunction is essential: branch 1 (`hi = phi ∧ lo.val < plo`) forces
the sum into `[pow128 * phi, p)`; branch 2 (`hi.val < phi`) plus
canonical `lo` forces it into `[0, pow128 * phi)`. Either way, `< p`. -/
private lemma valueNat_lt_p_of_canonical_disj {p : Prime}
    [Bn254.Prime p] {s : Scalar p}
    (hcanon : Canonical s)
    (hdisj : (s.hi = ((Bn254.phi : Nat) : Fp p)
              ∧ s.lo.val < Bn254.plo)
            ∨ s.hi.val < Bn254.phi) :
    s.lo.val + Lampe.pow128 * s.hi.val < p.natVal := by
  obtain ⟨hslo, hshi⟩ := hcanon
  have hmod : p.natVal = Bn254.plo + Lampe.pow128 * Bn254.phi :=
    Bn254.Prime.natVal_eq_limbs
  have hphi_lt_pow : Bn254.phi < Lampe.pow128 := by
    unfold Bn254.phi Lampe.pow128
    decide
  -- (phi : Fp p).val = phi (since phi < pow128 < p).
  have hphi_val : ((Bn254.phi : Nat) : Fp p).val = Bn254.phi := by
    have hphi_lt_p : Bn254.phi < p.natVal := by
      have := Bn254.pow128_lt_prime (p := p)
      omega
    exact ZMod.val_natCast_of_lt hphi_lt_p
  rcases hdisj with ⟨hhi_eq, hlo_lt_plo⟩ | hhi_lt_phi
  · -- Branch 1: lo.val < plo, hi.val = phi.
    have hhi_val : (hi s).val = Bn254.phi := by
      rw [hhi_eq]
      exact hphi_val
    rw [hhi_val]
    omega
  · -- Branch 2: hi.val < phi (so + 1 ≤ phi), with lo.val < pow128.
    have hbound : (lo s).val + Lampe.pow128 * (hi s).val <
        Lampe.pow128 * ((hi s).val + 1) := by
      have hexp : Lampe.pow128 * ((hi s).val + 1) =
          Lampe.pow128 + Lampe.pow128 * (hi s).val := by ring
      rw [hexp]
      omega
    have hmul_le : Lampe.pow128 * ((hi s).val + 1) ≤
        Lampe.pow128 * Bn254.phi :=
      Nat.mul_le_mul_left _ hhi_lt_phi
    have hle_p : Lampe.pow128 * Bn254.phi ≤ p.natVal := by
      rw [hmod]
      omega
    linarith

/-- The two main consequences used by uniqueness, packaged as the
`valueNat`-vs-`Fp p`-val bridge: under disjunction + canonical,
the prover's Nat sum equals `f.val`. -/
private lemma valueNat_eq_val_of_canonical_disj {p : Prime}
    [Bn254.Prime p] {f : Fp p} {s : Scalar p}
    (hcanon : Canonical s)
    (hdisj : (s.hi = ((Bn254.phi : Nat) : Fp p)
              ∧ s.lo.val < Bn254.plo)
            ∨ s.hi.val < Bn254.phi)
    (hdecomp : f = s.lo + ((Lampe.pow128 : Nat) : Fp p) * s.hi) :
    valueNat s = f.val := by
  have hpow_val : ((Lampe.pow128 : Nat) : Fp p).val = Lampe.pow128 :=
    Bn254.pow128_val (p := p)
  have hsum_lt_p : (lo s).val + Lampe.pow128 * (hi s).val < p.natVal :=
    valueNat_lt_p_of_canonical_disj hcanon hdisj
  have hmul_lt : Lampe.pow128 * (hi s).val < p.natVal := by
    have := Nat.le_add_left (Lampe.pow128 * (hi s).val) (lo s).val
    omega
  have hmul_lt' : ((Lampe.pow128 : Nat) : Fp p).val * (hi s).val < p.natVal := by
    rw [hpow_val]
    exact hmul_lt
  have hmul_val : (((Lampe.pow128 : Nat) : Fp p) * hi s).val =
      Lampe.pow128 * (hi s).val := by
    rw [ZMod.val_mul_of_lt hmul_lt', hpow_val]
  have hsum_lt : (lo s).val +
      (((Lampe.pow128 : Nat) : Fp p) * hi s).val < p.natVal := by
    rw [hmul_val]
    exact hsum_lt_p
  have hsum_val : (lo s + ((Lampe.pow128 : Nat) : Fp p) * hi s).val =
      (lo s).val + (((Lampe.pow128 : Nat) : Fp p) * hi s).val :=
    ZMod.val_add_of_lt hsum_lt
  have hf_val : f.val = (lo s).val + Lampe.pow128 * (hi s).val := by
    have := congrArg ZMod.val hdecomp
    rw [hsum_val, hmul_val] at this
    exact this
  unfold valueNat
  omega

/-- **Canonical-limb uniqueness**: any decomposition `s` of a field
element `f` that is `Canonical` AND satisfies the
`from_field_unsafe` canonical-range disjunction agrees with
`canonicalDecomp f`.

Combined with `canonicalDecomp_Canonical` and `canonicalDecomp_decomposes`,
this is the existence-and-uniqueness statement
`∃! s, Canonical s ∧ disj s ∧ f = s.lo + 2^128 · s.hi` from the
MSM canonicalization plan.

The canonical-range disjunction is essential — *both* `Canonical`
limbs alone do not suffice for uniqueness over BN254 (where
`pow128^2 ≈ 4·p`, so a canonical pair can decompose `0` either as
`(0, 0)` or as `(plo, phi)`). The disjunction breaks the tie. -/
theorem canonicalDecomp_unique {p : Prime} [Bn254.Prime p]
    {f : Fp p} {s : Scalar p}
    (hcanon : Canonical s)
    (hdisj : (s.hi = ((Bn254.phi : Nat) : Fp p)
              ∧ s.lo.val < Bn254.plo)
            ∨ s.hi.val < Bn254.phi)
    (hdecomp : f = s.lo + ((Lampe.pow128 : Nat) : Fp p) * s.hi) :
    s = canonicalDecomp f := by
  -- Both s and canonicalDecomp f are canonical decomps of f whose Nat sums
  -- lie in [0, p). Hence their Nat sums equal f.val, so they agree as
  -- `valueNat`. Then `valueNat_inj_canonical` gives equal limbs.
  have hcanon' : Canonical (canonicalDecomp f) :=
    canonicalDecomp_Canonical f
  have hf_decomp : f = lo (canonicalDecomp f) +
      ((Lampe.pow128 : Nat) : Fp p) * hi (canonicalDecomp f) :=
    canonicalDecomp_decomposes f
  -- canonicalDecomp's limbs satisfy the disjunction: its Nat sum equals f.val < p,
  -- which forces either hi = phi ∧ lo < plo (when f.val ≥ pow128*phi)
  -- or hi.val < phi (when f.val < pow128*phi).
  have hd_disj :
      (hi (canonicalDecomp f) = ((Bn254.phi : Nat) : Fp p)
        ∧ (lo (canonicalDecomp f)).val < Bn254.plo)
      ∨ (hi (canonicalDecomp f)).val < Bn254.phi := by
    -- Argue from f.val < p = plo + pow128*phi.
    have hmod : p.natVal = Bn254.plo + Lampe.pow128 * Bn254.phi :=
      Bn254.Prime.natVal_eq_limbs
    have hpow_pos : 0 < Lampe.pow128 := by
      unfold Lampe.pow128
      decide
    have hf_lt : f.val < p.natVal := f.val_lt
    -- (lo, hi) = (f.val % pow128, f.val / pow128). Use Nat.div_add_mod.
    have hdm : f.val % Lampe.pow128 + Lampe.pow128 * (f.val / Lampe.pow128) = f.val := by
      have := Nat.div_add_mod f.val Lampe.pow128
      omega
    -- Identify lo.val and hi.val on the canonicalDecomp side.
    have hlo_val : (lo (canonicalDecomp f)).val = f.val % Lampe.pow128 := by
      unfold canonicalDecomp lo mkScalar
      have hmod_lt_p : f.val % Lampe.pow128 < p.natVal := by
        have := Nat.mod_lt f.val hpow_pos
        have := Bn254.pow128_lt_prime (p := p)
        omega
      exact ZMod.val_natCast_of_lt hmod_lt_p
    have hhi_val : (hi (canonicalDecomp f)).val = f.val / Lampe.pow128 := by
      unfold canonicalDecomp hi mkScalar
      have hp_sq := p_lt_pow128_sq (p := p)
      have hf_lt_sq : f.val < Lampe.pow128 * Lampe.pow128 := lt_trans hf_lt hp_sq
      have hdiv_lt : f.val / Lampe.pow128 < Lampe.pow128 :=
        Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hf_lt_sq)
      have hdiv_lt_p : f.val / Lampe.pow128 < p.natVal := by
        have := Bn254.pow128_lt_prime (p := p)
        omega
      exact ZMod.val_natCast_of_lt hdiv_lt_p
    -- Now case-split on whether f.val < pow128 * phi.
    by_cases hcase : f.val < Lampe.pow128 * Bn254.phi
    · right
      rw [hhi_val]
      -- f.val < pow128 * phi ⟹ f.val / pow128 < phi.
      exact Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hcase)
    · left
      replace hcase : Lampe.pow128 * Bn254.phi ≤ f.val := Nat.le_of_not_lt hcase
      -- f.val ≥ pow128 * phi and f.val < p = plo + pow128*phi.
      -- So f.val = pow128*phi + r where r ∈ [0, plo).
      have hr_lo : f.val - Lampe.pow128 * Bn254.phi < Bn254.plo := by
        omega
      -- f.val / pow128 = phi when pow128*phi ≤ f.val < pow128*(phi+1),
      -- and the upper bound is f.val < pow128*phi + pow128 (follows from r < plo < pow128).
      have hplo_lt_pow : Bn254.plo < Lampe.pow128 := by
        unfold Bn254.plo Lampe.pow128
        decide
      have hf_lt' : f.val < Lampe.pow128 * (Bn254.phi + 1) := by
        have : Lampe.pow128 * (Bn254.phi + 1) =
            Lampe.pow128 * Bn254.phi + Lampe.pow128 := by ring
        omega
      have hdiv_eq : f.val / Lampe.pow128 = Bn254.phi := by
        apply Nat.div_eq_of_lt_le
        · rw [Nat.mul_comm]
          exact hcase
        · rw [Nat.mul_comm]
          exact hf_lt'
      refine ⟨?_, ?_⟩
      · -- Goal: hi (canonicalDecomp f) = (↑phi : Fp p). Since
        -- hi := ((f.val / pow128 : Nat) : Fp p) and f.val / pow128 = phi.
        unfold canonicalDecomp hi mkScalar
        rw [hdiv_eq]
      · -- Goal: (lo (canonicalDecomp f)).val < plo.
        rw [hlo_val]
        -- f.val % pow128 = f.val - pow128*phi (since pow128*phi ≤ f.val < pow128*(phi+1)).
        have hmod_eq : f.val % Lampe.pow128 = f.val - Lampe.pow128 * Bn254.phi := by
          have hsub : f.val = (f.val - Lampe.pow128 * Bn254.phi) +
              Lampe.pow128 * Bn254.phi := by omega
          conv_lhs => rw [hsub]
          rw [Nat.add_mul_mod_self_left,
              Nat.mod_eq_of_lt (lt_of_lt_of_le hr_lo (le_of_lt hplo_lt_pow))]
        omega
  -- Both sides have equal valueNat (= f.val).
  have hs_val_eq : valueNat s = f.val :=
    valueNat_eq_val_of_canonical_disj hcanon hdisj hdecomp
  have hd_val_eq : valueNat (canonicalDecomp f) = f.val :=
    valueNat_eq_val_of_canonical_disj hcanon' hd_disj hf_decomp
  -- Combine: valueNat agrees, so limbs agree.
  have hv_eq : valueNat s = valueNat (canonicalDecomp f) := by
    rw [hs_val_eq, hd_val_eq]
  obtain ⟨hlo_eq, hhi_eq⟩ := valueNat_inj_canonical hcanon hcanon' hv_eq
  -- s and canonicalDecomp f are 3-tuples (lo, hi, ()); equality of lo, hi
  -- gives equality.
  obtain ⟨slo, shi, ⟨⟩⟩ := s
  simp only [lo, hi] at hlo_eq hhi_eq
  show ((slo, shi, PUnit.unit) : Scalar p) = canonicalDecomp f
  rw [hlo_eq, hhi_eq]

end Scalar

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
