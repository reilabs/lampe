import «std-1.0.0-beta.14».Extracted
import Lampe
import Stdlib.Field.Basic

/-!
# BN254 scalar-field Noir-extracted specs

This file binds the Noir-extracted BN254 scalar-field helpers (`PLO`,
`PHI`, `TWO_POW_128`, `decompose`, `assert_gt`, `assert_lt`, `lt`,
`gt`, `field_less_than`, `lte_hint`) to their algebraic semantics.

Pure-math defs and lemmas (`r_scalar`, `plo`, `phi`, `pow128`, the
`Bn254.Prime` typeclass, `decompose`-shape limb arithmetic) live in
`Lampe.Crypto.Bn254`. The concrete `Bn254.prime : Lampe.Prime` value
and its `Bn254.Prime` instance live in `Lampe.Crypto.Bn254.Prime`.
-/

namespace Lampe.Stdlib.Field.Bn254

open Lampe
open Lampe.Crypto
open «std-1.0.0-beta.14» (env)
open Lampe.Crypto.Bn254 (plo phi pow128 pow128_lt_prime pow128_val
  val_add_one_of_lt limbs_gt_of_hi_gt sub_val_gt_pow128_of_lt)

abbrev PLO := «std-1.0.0-beta.14::field::bn254::PLO»
abbrev PHI := «std-1.0.0-beta.14::field::bn254::PHI»
abbrev TWO_POW_128 := «std-1.0.0-beta.14::field::bn254::TWO_POW_128»

theorem plo_spec {p} :
    STHoare p env ⟦⟧
      (PLO.call h![] h![])
      (fun r => r = (plo : Fp p)) := by
  enter_decl
  steps
  rename_i hplo
  simpa [plo] using hplo

theorem phi_spec {p} :
    STHoare p env ⟦⟧
      (PHI.call h![] h![])
      (fun r => r = (phi : Fp p)) := by
  enter_decl
  steps
  rename_i hphi
  simpa [phi] using hphi

theorem two_pow_128_spec {p} :
    STHoare p env ⟦⟧
      (TWO_POW_128.call h![] h![])
      (fun r => r = (pow128 : Fp p)) := by
  enter_decl
  steps
  rename_i hpow
  simpa [pow128] using hpow

-- FIXME: steps requires this even tho it's an empty postcondition
theorem lte_hint_intro {p a b} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::field::bn254::lte_hint».call h![] h![a, b])
      (fun _ => ⟦⟧) := by
  enter_decl
  steps

-- FIXME: steps requires this even tho it's an empty postcondition
theorem decompose_hint_intro {p x} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::field::bn254::decompose_hint».call h![] h![x])
      (fun _ => ⟦⟧) := by
  enter_decl
  steps

theorem assert_gt_limbs_intro {p a b} [Prime.BitsGT p 129] :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::field::bn254::assert_gt_limbs».call h![] h![a, b])
      (fun _ => ⟦
        (a.1.val < pow128 ∧ a.2.1.val < pow128 ∧ b.1.val < pow128 ∧ b.2.1.val < pow128) →
          a.1.val + pow128 * a.2.1.val > b.1.val + pow128 * b.2.1.val
      ⟧) := by
  enter_decl
  steps [Lampe.Stdlib.Field.assert_max_bit_size_intro, two_pow_128_spec (p := p), lte_hint_intro]
  intro hbounds
  rcases hbounds with ⟨ha_lo, ha_hi, hb_lo, hb_hi⟩
  rename_i h_rlo_lt h_rhi_lt h_out h_out_eq
  clear h_out h_out_eq
  simp at *
  subst alo
  subst ahi
  subst blo
  subst bhi
  cases hborrow : borrow <;> simp [hborrow] at *
  · have hrlo_def : rlo = a.1 - b.1 - 1 := by
      assumption
    have hrhi_def : rhi = a.2.1 - b.2.1 := by
      assumption
    have hhi_ge : b.2.1.val ≤ a.2.1.val := by
      by_contra hgt
      have hlt : a.2.1.val < b.2.1.val := lt_of_not_ge hgt
      have hgt' := sub_val_gt_pow128_of_lt (p := p) ha_hi (le_of_lt hb_hi) hlt
      have hrhi_lt' : (a.2.1 - b.2.1).val < pow128 := by
        simpa [hrhi_def] using h_rhi_lt
      linarith [hrhi_lt', hgt']
    by_cases hhi_eq : b.2.1.val = a.2.1.val
    · have hblo1_val : (b.1 + 1).val = b.1.val + 1 :=
        val_add_one_of_lt (p := p) hb_lo
      have hblo1_le : (b.1 + 1).val ≤ pow128 := by
        have : b.1.val + 1 ≤ pow128 := Nat.succ_le_of_lt hb_lo
        simpa [hblo1_val] using this
      have hrlo_lt' : (a.1 - (b.1 + 1)).val < pow128 := by
        have : (a.1 - b.1 - 1).val < pow128 := by
          simpa [hrlo_def] using h_rlo_lt
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
      have hlo : b.1.val < a.1.val := by
        by_contra hge
        have hle : a.1.val ≤ b.1.val := le_of_not_gt hge
        have hlt : a.1.val < (b.1 + 1).val := by
          have : a.1.val < b.1.val + 1 := Nat.lt_succ_of_le hle
          simpa [hblo1_val] using this
        have hgt := sub_val_gt_pow128_of_lt (p := p) ha_lo hblo1_le hlt
        linarith
      have hgt : b.1.val + pow128 * b.2.1.val < a.1.val + pow128 * b.2.1.val :=
        Nat.add_lt_add_right hlo _
      simpa [hhi_eq, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hgt
    · have hhi_lt : b.2.1.val < a.2.1.val := lt_of_le_of_ne hhi_ge hhi_eq
      exact limbs_gt_of_hi_gt hb_lo hhi_lt
  · have hrhi_def : rhi = a.2.1 - b.2.1 - 1 := by
      assumption
    have hbhi1_val : (b.2.1 + 1).val = b.2.1.val + 1 :=
      val_add_one_of_lt (p := p) hb_hi
    have hbhi1_le : (b.2.1 + 1).val ≤ pow128 := by
      have : b.2.1.val + 1 ≤ pow128 := Nat.succ_le_of_lt hb_hi
      simpa [hbhi1_val] using this
    have hrhi_lt' : (a.2.1 - (b.2.1 + 1)).val < pow128 := by
      have : (a.2.1 - b.2.1 - 1).val < pow128 := by
        simpa [hrhi_def] using h_rhi_lt
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
    have hhi : b.2.1.val < a.2.1.val := by
      by_contra hge
      have hle : a.2.1.val ≤ b.2.1.val := le_of_not_gt hge
      have hlt : a.2.1.val < (b.2.1 + 1).val := by
        have : a.2.1.val < b.2.1.val + 1 := Nat.lt_succ_of_le hle
        simpa [hbhi1_val] using this
      have hgt := sub_val_gt_pow128_of_lt (p := p) ha_hi hbhi1_le hlt
      linarith
    exact limbs_gt_of_hi_gt hb_lo hhi

theorem decompose_intro {p x} [Bn254.Prime p] :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::field::bn254::decompose».call h![] h![x])
      (fun r =>
        ∃∃ xlo xhi,
          r = (xlo, xhi, ()) ∧
          xlo.val < pow128 ∧
          xhi.val < pow128 ∧
          x.val = xlo.val + pow128 * xhi.val) := by
  enter_decl
  steps
  · exact ()
  apply STHoare.iteFalse_intro
  steps [Lampe.Stdlib.Field.assert_max_bit_size_intro, assert_gt_limbs_intro (p := p),
    decompose_hint_intro (p := p), plo_spec (p := p), phi_spec (p := p), two_pow_128_spec (p := p)]
  simp [SLP.exists_pure, beq_true, decide_eq_true_eq] at *
  sl
  -- `sl` decomposes the tuple equality into per-component equalities. The combined
  -- equality is still in scope as an anonymous hypothesis of shape
  -- `_ = HList.toTuple ...`, definitionally `_ = (xlo, xhi, ())`.
  rename_i hxlo_eq hxhi_eq hxlo hxhi hxeq hlimbs
  rename _ = HList.toTuple _ _ _ => hret'
  have hxlo' : xlo.val < pow128 := by
    simpa [pow128] using hxlo
  have hxhi' : xhi.val < pow128 := by
    simpa [pow128] using hxhi
  have hxeq' : x = xlo + (pow128 : Fp p) * xhi := by
    simpa using hxeq
  have hplo_val : (plo : Fp p).val = plo := by
    have hplo_lt : plo < p.natVal := by
      have hplo_lt' : plo < pow128 := by decide
      linarith [hplo_lt', pow128_lt_prime (p := p)]
    simpa using (ZMod.val_natCast_of_lt hplo_lt)
  have hphi_val : (phi : Fp p).val = phi := by
    have hphi_lt : phi < p.natVal := by
      have hphi_lt' : phi < pow128 := by decide
      linarith [hphi_lt', pow128_lt_prime (p := p)]
    simpa using (ZMod.val_natCast_of_lt hphi_lt)
  have hplo : (plo : Fp p).val < pow128 := by
    have hplo_nat : plo < pow128 := by decide
    simpa [hplo_val] using hplo_nat
  have hphi : (phi : Fp p).val < pow128 := by
    have hphi_nat : phi < pow128 := by decide
    simpa [hphi_val] using hphi_nat
  have hlimbs' : (plo : Fp p).val < pow128 ∧ (phi : Fp p).val < pow128 ∧
      xlo.val < pow128 ∧ xhi.val < pow128 := by
    exact ⟨hplo, hphi, hxlo', hxhi'⟩
  have hlimbs_imp :
      (plo : Fp p).val < pow128 ∧ (phi : Fp p).val < pow128 ∧
        xlo.val < pow128 ∧ xhi.val < pow128 →
        (plo : Fp p).val + pow128 * (phi : Fp p).val >
          xlo.val + pow128 * xhi.val := by
    assumption
  have hgt : (plo : Fp p).val + pow128 * (phi : Fp p).val >
      xlo.val + pow128 * xhi.val := by
    exact hlimbs_imp hlimbs'
  have hgt' : plo + pow128 * phi > xlo.val + pow128 * xhi.val := by
    simpa [hplo_val, hphi_val] using hgt
  have hsum_lt : xlo.val + pow128 * xhi.val < p.natVal := by
    simpa [Bn254.Prime.natVal_eq_limbs] using hgt'
  have hmul_lt : pow128 * xhi.val < p.natVal := by
    exact lt_of_le_of_lt (Nat.le_add_left _ _) hsum_lt
  have hmul_lt' : (pow128 : Fp p).val * xhi.val < p.natVal := by
    simpa [pow128_val (p := p)] using hmul_lt
  have hsum_val : (xlo + (pow128 : Fp p) * xhi).val = xlo.val + pow128 * xhi.val := by
    have hmul_val' : ((pow128 : Fp p) * xhi).val = (pow128 : Fp p).val * xhi.val := by
      simpa using (ZMod.val_mul_of_lt hmul_lt')
    have hsum_lt' : xlo.val + ((pow128 : Fp p) * xhi).val < p.natVal := by
      simpa [hmul_val', pow128_val (p := p)] using hsum_lt
    simpa [hmul_val', pow128_val (p := p)] using
      (ZMod.val_add_of_lt (a := xlo) (b := (pow128 : Fp p) * xhi) hsum_lt')
  have hval_eq : x.val = xlo.val + pow128 * xhi.val := by
    have : x.val = (xlo + (pow128 : Fp p) * xhi).val := by
      simpa using congrArg ZMod.val hxeq'
    simpa [hsum_val] using this
  refine ⟨xhi, ?_⟩
  exact ⟨hret', hxlo', hxhi', hval_eq⟩

theorem assert_gt_intro {p a b} [Bn254.Prime p] :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::field::bn254::assert_gt».call h![] h![a, b])
      (fun _ => a.val > b.val) := by
  enter_decl
  steps
  · exact ()
  apply STHoare.iteFalse_intro
  steps [decompose_intro (p := p), assert_gt_limbs_intro (p := p)]
  simp at *
  rename_i _ a_lo a_hi ha_raw b_lo b_hi hb_raw _ hlimbs
  rcases ha_raw with ⟨ha_eq, ha_lo_lt, ha_hi_lt, ha_val⟩
  rcases hb_raw with ⟨hb_eq, hb_lo_lt, hb_hi_lt, hb_val⟩
  have hlimbs' :
      a_lo.val < pow128 →
        a_hi.val < pow128 →
          b_lo.val < pow128 →
            b_hi.val < pow128 →
              b_lo.val + pow128 * b_hi.val < a_lo.val + pow128 * a_hi.val := by
    simpa [ha_eq, hb_eq] using hlimbs
  have hgt : b_lo.val + pow128 * b_hi.val < a_lo.val + pow128 * a_hi.val := by
    exact hlimbs' ha_lo_lt ha_hi_lt hb_lo_lt hb_hi_lt
  linarith [ha_val, hb_val, hgt]

theorem assert_lt_intro {p a b} [Bn254.Prime p] :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::field::bn254::assert_lt».call h![] h![a, b])
      (fun _ => a.val < b.val) := by
  enter_decl
  steps [assert_gt_intro (p := p)]
  omega

theorem field_less_than_intro {p x y} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::field::field_less_than».call h![] h![x, y])
      (fun _ => ⟦⟧) := by
  enter_decl
  steps

theorem gt_intro {p a b} [Bn254.Prime p] :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::field::bn254::gt».call h![] h![a, b])
      (fun r => r = decide (a.val > b.val)) := by
  enter_decl
  steps
  · exact ()
  apply STHoare.iteFalse_intro
  steps
  apply STHoare.ite_intro
  · intro h_eq
    steps
    have h_eq' : a = b := by
      simpa [decide_eq_true_eq] using h_eq
    simp_all
  · intro h_eq
    steps [field_less_than_intro]
    apply STHoare.ite_intro
    · intro hlt
      steps [assert_gt_intro (p := p)]
      rename_i r hret
      have hgt_ba : b.val > a.val := by
        assumption
      have hnot : ¬ a.val > b.val := by
        exact Nat.not_lt.mpr (le_of_lt hgt_ba)
      simpa [hnot, decide_eq_false_iff_not] using hret
    · intro hlt
      steps [assert_gt_intro (p := p)]
      rename_i r hret
      have hgt_ab : a.val > b.val := by
        assumption
      simpa [hgt_ab, decide_eq_true_eq] using hret

theorem lt_intro {p a b} [Bn254.Prime p] :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::field::bn254::lt».call h![] h![a, b])
      (fun r => r = decide (a.val < b.val)) := by
  enter_decl
  steps [gt_intro (p := p)]
  rename_i r hret
  simpa using (hret : r = decide (b.val > a.val))
