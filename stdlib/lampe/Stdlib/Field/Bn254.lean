import «std-1.0.0-beta.12».Extracted
import Lampe
import Stdlib.Field.Basic

namespace Lampe.Stdlib.Field.Bn254

open Lampe
open «std-1.0.0-beta.12» (env)

abbrev PLO := «std-1.0.0-beta.12::field::bn254::PLO»
abbrev PHI := «std-1.0.0-beta.12::field::bn254::PHI»
abbrev TWO_POW_128 := «std-1.0.0-beta.12::field::bn254::TWO_POW_128»

def ploNat : Nat := 53438638232309528389504892708671455233

def phiNat : Nat := 64323764613183177041862057485226039389

def pow128 : Nat := 2 ^ 128

lemma pow128_lt_prime {p} [Prime.BitsGT p 129] : pow128 < p.natVal := by
  simpa [pow128] using (Prime.BitsGT.lt_prime (prime := p) (bits := 128))

lemma pow128_val {p} [Prime.BitsGT p 129] : ((pow128 : Nat) : Fp p).val = pow128 := by
  simpa [pow128] using (ZMod.val_natCast_of_lt (pow128_lt_prime (p := p)))

lemma val_add_one_of_lt {p} [Prime.BitsGT p 129] {x : Fp p} (hx : x.val < pow128) :
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

lemma prime_sub_pow128_gt {p} [Prime.BitsGT p 129] : p.natVal - pow128 > pow128 := by
  have hp : (2 ^ 129 : Nat) < p.natVal := by
    simpa using (Prime.BitsGT.lt_prime (prime := p) (bits := 129))
  have hsum : pow128 + pow128 < p.natVal := by
    have : (2 ^ 129 : Nat) = pow128 + pow128 := by
      simp [pow128, Nat.pow_succ, two_mul]
    simpa [this] using hp
  exact (Nat.lt_sub_iff_add_lt).2 hsum

lemma sub_val_gt_pow128_of_lt {p} [Prime.BitsGT p 129] {a b : Fp p}
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

lemma sub_val_lt_pow128_of_le {p} [Prime.BitsGT p 129] {a b : Fp p}
    (ha : a.val < pow128) (hle : b.val ≤ a.val) :
    (a - b).val < pow128 := by
  haveI : NeZero p.natVal := by infer_instance
  have hval : (a - b).val = a.val - b.val := by
    exact ZMod.val_sub (a := a) (b := b) hle
  have : a.val - b.val < pow128 := by
    exact lt_of_le_of_lt (Nat.sub_le _ _) ha
  simpa [hval] using this

theorem plo_spec {p} :
    STHoare p env ⟦⟧
      (PLO.call h![] h![])
      (fun r => r = (ploNat : Fp p)) := by
  enter_decl
  steps
  rename_i hplo
  simpa [ploNat] using hplo

theorem phi_spec {p} :
    STHoare p env ⟦⟧
      (PHI.call h![] h![])
      (fun r => r = (phiNat : Fp p)) := by
  enter_decl
  steps
  rename_i hphi
  simpa [phiNat] using hphi

theorem two_pow_128_spec {p} :
    STHoare p env ⟦⟧
      (TWO_POW_128.call h![] h![])
      (fun r => r = (pow128 : Fp p)) := by
  enter_decl
  steps
  rename_i hpow
  simpa [pow128] using hpow

theorem lte_hint_intro {p a b} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::field::bn254::lte_hint».call h![] h![a, b])
      (fun _ => ⟦⟧) := by
  enter_decl
  steps

theorem decompose_hint_intro {p x} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::field::bn254::decompose_hint».call h![] h![x])
      (fun _ => ⟦⟧) := by
  enter_decl
  steps

theorem assert_gt_limbs_intro {p a b} [Prime.BitsGT p 129] :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::field::bn254::assert_gt_limbs».call h![] h![a, b])
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
  simp [Builtin.indexTpl] at *
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

theorem decompose_intro {p x} [Prime.BitsGT p 129]
    (hmod : p.natVal = ploNat + pow128 * phiNat) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::field::bn254::decompose».call h![] h![x])
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
  rename_i r hret hxlo hxhi hxeq hlimbs
  have hret' : r = (xlo, xhi, ()) := by
    simpa using hret
  have hxlo' : xlo.val < pow128 := by
    simpa [pow128] using hxlo
  have hxhi' : xhi.val < pow128 := by
    simpa [pow128] using hxhi
  have hxeq' : x = xlo + (pow128 : Fp p) * xhi := by
    simpa using hxeq
  have hplo_val : (ploNat : Fp p).val = ploNat := by
    have hplo_lt : ploNat < p.natVal := by
      have hplo_lt' : ploNat < pow128 := by decide
      linarith [hplo_lt', pow128_lt_prime (p := p)]
    simpa using (ZMod.val_natCast_of_lt hplo_lt)
  have hphi_val : (phiNat : Fp p).val = phiNat := by
    have hphi_lt : phiNat < p.natVal := by
      have hphi_lt' : phiNat < pow128 := by decide
      linarith [hphi_lt', pow128_lt_prime (p := p)]
    simpa using (ZMod.val_natCast_of_lt hphi_lt)
  have hplo : (ploNat : Fp p).val < pow128 := by
    have hplo_nat : ploNat < pow128 := by decide
    simpa [hplo_val] using hplo_nat
  have hphi : (phiNat : Fp p).val < pow128 := by
    have hphi_nat : phiNat < pow128 := by decide
    simpa [hphi_val] using hphi_nat
  have hlimbs' : (ploNat : Fp p).val < pow128 ∧ (phiNat : Fp p).val < pow128 ∧
      xlo.val < pow128 ∧ xhi.val < pow128 := by
    exact ⟨hplo, hphi, hxlo', hxhi'⟩
  have hlimbs_imp :
      (ploNat : Fp p).val < pow128 ∧ (phiNat : Fp p).val < pow128 ∧
        xlo.val < pow128 ∧ xhi.val < pow128 →
        (ploNat : Fp p).val + pow128 * (phiNat : Fp p).val >
          xlo.val + pow128 * xhi.val := by
    assumption
  have hgt : (ploNat : Fp p).val + pow128 * (phiNat : Fp p).val >
      xlo.val + pow128 * xhi.val := by
    exact hlimbs_imp hlimbs'
  have hgt' : ploNat + pow128 * phiNat > xlo.val + pow128 * xhi.val := by
    simpa [hplo_val, hphi_val] using hgt
  have hsum_lt : xlo.val + pow128 * xhi.val < p.natVal := by
    simpa [hmod] using hgt'
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

theorem assert_gt_intro {p a b} [Prime.BitsGT p 129]
    (hmod : p.natVal = ploNat + pow128 * phiNat) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::field::bn254::assert_gt».call h![] h![a, b])
      (fun _ => a.val > b.val) := by
  enter_decl
  steps
  · exact ()
  apply STHoare.iteFalse_intro
  steps [decompose_intro (p := p) (hmod := hmod), assert_gt_limbs_intro (p := p)]
  simp [SLP.exists_pure] at *
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

theorem assert_lt_intro {p a b} [Prime.BitsGT p 129]
    (hmod : p.natVal = ploNat + pow128 * phiNat) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::field::bn254::assert_lt».call h![] h![a, b])
      (fun _ => a.val < b.val) := by
  enter_decl
  steps [assert_gt_intro (p := p) (hmod := hmod)]
  omega

theorem field_less_than_intro {p x y} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::field::field_less_than».call h![] h![x, y])
      (fun _ => ⟦⟧) := by
  enter_decl
  steps

theorem gt_intro {p a b} [Prime.BitsGT p 129]
    (hmod : p.natVal = ploNat + pow128 * phiNat) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::field::bn254::gt».call h![] h![a, b])
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
    simp_all [h_eq']
  · intro h_eq
    steps [field_less_than_intro]
    apply STHoare.ite_intro
    · intro hlt
      steps [assert_gt_intro (p := p) (hmod := hmod)]
      rename_i r hret
      have hgt_ba : b.val > a.val := by
        assumption
      have hnot : ¬ a.val > b.val := by
        exact Nat.not_lt.mpr (le_of_lt hgt_ba)
      simpa [hnot, decide_eq_false_iff_not] using hret
    · intro hlt
      steps [assert_gt_intro (p := p) (hmod := hmod)]
      rename_i r hret
      have hgt_ab : a.val > b.val := by
        assumption
      simpa [hgt_ab, decide_eq_true_eq] using hret

theorem lt_intro {p a b} [Prime.BitsGT p 129]
    (hmod : p.natVal = ploNat + pow128 * phiNat) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::field::bn254::lt».call h![] h![a, b])
      (fun r => r = decide (a.val < b.val)) := by
  enter_decl
  steps [gt_intro (p := p) (hmod := hmod)]
  rename_i r hret
  simpa using (hret : r = decide (b.val > a.val))
