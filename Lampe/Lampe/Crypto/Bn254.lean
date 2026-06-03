import Lampe.Data.Field

/-!
# BN254 scalar-field — pure mathematical facts

Pure-math defs and lemmas about the BN254 scalar-field prime (the order
of the BN254 curve subgroup, a 254-bit prime), independent of Noir
extracted bindings. Anything that depends on a concrete `Lampe.Prime`
value or on the extracted Noir env lives downstream:

- the concrete `bn254Prime : Lampe.Prime` and its `Bn254.Prime` instance
  live in `Lampe.Crypto.Bn254.Prime` (Pratt certificate + Lucas witness),
- the Noir-extracted STHoare specs (`plo_spec`, `phi_spec`,
  `decompose_intro`, `assert_gt_intro`, …) live in
  `Lampe.Stdlib.Field.Bn254`.

This file defines the `Bn254.Prime` typeclass against which the
algebraic-side lemmas (`pow128_lt_prime`, `decompose_intro` shape,
`assert_gt_intro` shape, …) are stated, plus a `BitsGT 129` instance so
downstream specs need no `[Bn254.Prime p] [BitsGT p 129]` plumbing.
-/

namespace Lampe.Crypto.Bn254

open Lampe

/-- BN254 scalar-field prime literal (order of the curve subgroup). -/
def r_scalar : Nat :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

/-- Low limb of the BN254 scalar-field prime: `r_scalar mod 2^128`. -/
def plo : Nat := 53438638232309528389504892708671455233

/-- High limb of the BN254 scalar-field prime: `r_scalar / 2^128`. -/
def phi : Nat := 64323764613183177041862057485226039389

/-- Limb base `2^128`. -/
def pow128 : Nat := 2 ^ 128

/-- The numeric content of `Bn254.Prime`: the prime decomposes as
`plo + 2^128 * phi`. Equivalent to `p.natVal = r_scalar`. -/
private lemma r_scalar_eq_limbs : r_scalar = plo + pow128 * phi := by
  decide

/-- `p` is the BN254 scalar-field prime. Providing this instance discharges
every BN254-context precondition (limb decomposition, `Prime.BitsGT p 129`,
extracted-spec preconditions in `Stdlib.Field.Bn254`, …) without explicit
plumbing. -/
class Prime (p : Lampe.Prime) : Prop where
  natVal_eq_r_scalar : p.natVal = r_scalar

namespace Prime

/-- Limb form of the `Prime` contract, derived from `natVal_eq_r_scalar`. -/
lemma natVal_eq_limbs {p : Lampe.Prime} [inst : Prime p] :
    p.natVal = plo + pow128 * phi := by
  rw [inst.natVal_eq_r_scalar, r_scalar_eq_limbs]

/-- Legacy spelling, kept so downstream specs that wrote `Bn254.Prime.modulus_eq`
keep compiling without churn. -/
@[deprecated natVal_eq_limbs (since := "2026-06-02")]
lemma modulus_eq {p : Lampe.Prime} [Prime p] :
    p.natVal = plo + pow128 * phi := natVal_eq_limbs

end Prime

instance [inst : Prime p] : Lampe.Prime.BitsGT p 129 where
  prime_gt := by rw [inst.natVal_eq_r_scalar]; decide

lemma pow128_lt_prime {p} [Lampe.Prime.BitsGT p 129] : pow128 < p.natVal := by
  simpa [pow128] using (Lampe.Prime.BitsGT.lt_prime (prime := p) (bits := 128))

lemma pow128_val {p} [Lampe.Prime.BitsGT p 129] : ((pow128 : Nat) : Fp p).val = pow128 := by
  simpa [pow128] using (ZMod.val_natCast_of_lt (pow128_lt_prime (p := p)))

lemma val_add_one_of_lt {p} [Lampe.Prime.BitsGT p 129] {x : Fp p} (hx : x.val < pow128) :
    (x + 1).val = x.val + 1 := by
  have h1_val : (1 : Fp p).val = 1 := by
    have h1_lt : (1 : Nat) < p.natVal := by
      linarith [pow128_lt_prime (p := p)]
    simpa using (ZMod.val_natCast_of_lt h1_lt)
  have hx1_lt : x.val + 1 < p.natVal := by
    linarith [hx, pow128_lt_prime (p := p)]
  have hx1_lt' : x.val + (1 : Fp p).val < p.natVal := by
    simpa [h1_val] using hx1_lt
  simpa [h1_val] using (ZMod.val_add_of_lt hx1_lt')

lemma limbs_gt_of_hi_gt {a_lo a_hi b_lo b_hi : Nat}
    (hb_lo : b_lo < pow128) (hhi : b_hi < a_hi) :
    a_lo + pow128 * a_hi > b_lo + pow128 * b_hi := by
  have h_rhs : b_lo + pow128 * b_hi < pow128 * (b_hi + 1) := by
    have h1 : b_lo + pow128 * b_hi < pow128 + pow128 * b_hi :=
      Nat.add_lt_add_right hb_lo _
    simpa [Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h1
  have hpow : pow128 * (b_hi + 1) ≤ pow128 * a_hi := by
    exact Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hhi)
  have h_lhs_ge : pow128 * (b_hi + 1) ≤ a_lo + pow128 * a_hi := by
    exact le_trans hpow (Nat.le_add_left _ _)
  exact lt_of_lt_of_le h_rhs h_lhs_ge

lemma prime_sub_pow128_gt {p} [Lampe.Prime.BitsGT p 129] : p.natVal - pow128 > pow128 := by
  have hp : (2 ^ 129 : Nat) < p.natVal := by
    simpa using (Lampe.Prime.BitsGT.lt_prime (prime := p) (bits := 129))
  have hsum : pow128 + pow128 < p.natVal := by
    have : (2 ^ 129 : Nat) = pow128 + pow128 := by
      simp [pow128, Nat.pow_succ, two_mul]
    simpa [this] using hp
  exact (Nat.lt_sub_iff_add_lt).2 hsum

lemma sub_val_gt_pow128_of_lt {p} [Lampe.Prime.BitsGT p 129] {a b : Fp p}
    (ha : a.val < pow128) (hb : b.val ≤ pow128) (h : a.val < b.val) :
    (a - b).val > pow128 := by
  have hb_lt : b.val < p.natVal := lt_of_le_of_lt hb (pow128_lt_prime (p := p))
  have hbne : b ≠ 0 := by
    intro hbz
    subst hbz
    simpa using h
  haveI : NeZero b := ⟨hbne⟩
  have hneg : (-b).val = p.natVal - b.val := by
    simpa using (ZMod.val_neg_of_ne_zero b)
  have hsum_lt : a.val + (-b).val < p.natVal := by
    have hb_le : b.val ≤ p.natVal := le_of_lt hb_lt
    have hsum_lt' :
        a.val + (p.natVal - b.val) < b.val + (p.natVal - b.val) :=
      Nat.add_lt_add_right h _
    simpa [hneg, Nat.add_sub_of_le hb_le] using hsum_lt'
  have hval : (a - b).val = a.val + (-b).val := by
    simpa [sub_eq_add_neg] using (ZMod.val_add_of_lt hsum_lt)
  have hsum_eq : a.val + (-b).val = p.natVal - (b.val - a.val) := by
    have ha_le : a.val ≤ b.val := le_of_lt h
    have hb_le : b.val ≤ p.natVal := le_of_lt hb_lt
    have hd_le : b.val - a.val ≤ p.natVal := by
      exact le_trans (Nat.sub_le _ _) hb_le
    have hsum :
        a.val + (p.natVal - b.val) + (b.val - a.val) = p.natVal := by
      calc
        a.val + (p.natVal - b.val) + (b.val - a.val)
            = (a.val + (b.val - a.val)) + (p.natVal - b.val) := by
                simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        _ = b.val + (p.natVal - b.val) := by
                simp [Nat.add_sub_of_le ha_le]
        _ = p.natVal := by
                simp [Nat.add_sub_of_le hb_le]
    have hsum' :
        a.val + (p.natVal - b.val) + (b.val - a.val) =
          p.natVal - (b.val - a.val) + (b.val - a.val) := by
      calc
        a.val + (p.natVal - b.val) + (b.val - a.val) = p.natVal := hsum
        _ = p.natVal - (b.val - a.val) + (b.val - a.val) := by
            symm
            exact Nat.sub_add_cancel hd_le
    have hsum_eq' : a.val + (p.natVal - b.val) = p.natVal - (b.val - a.val) := by
      exact Nat.add_right_cancel hsum'
    simpa [hneg] using hsum_eq'
  have hdiff : b.val - a.val ≤ pow128 := by
    exact le_trans (Nat.sub_le _ _) hb
  have hgt : p.natVal - (b.val - a.val) > pow128 := by
    have hge : p.natVal - (b.val - a.val) ≥ p.natVal - pow128 := by
      exact Nat.sub_le_sub_left hdiff _
    linarith [prime_sub_pow128_gt (p := p), hge]
  calc
    (a - b).val = a.val + (-b).val := hval
    _ = p.natVal - (b.val - a.val) := hsum_eq
    _ > pow128 := hgt

lemma sub_val_lt_pow128_of_le {p} [Lampe.Prime.BitsGT p 129] {a b : Fp p}
    (ha : a.val < pow128) (hle : b.val ≤ a.val) :
    (a - b).val < pow128 := by
  haveI : NeZero p.natVal := by infer_instance
  have hval : (a - b).val = a.val - b.val := by
    exact ZMod.val_sub (a := a) (b := b) hle
  have : a.val - b.val < pow128 := by
    exact lt_of_le_of_lt (Nat.sub_le _ _) ha
  simpa [hval] using this

end Lampe.Crypto.Bn254
