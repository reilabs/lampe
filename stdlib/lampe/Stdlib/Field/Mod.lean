import «std-1.0.0-beta.12».Extracted
import Lampe

namespace Lampe.Stdlib.Field

open «std-1.0.0-beta.12» (env)

@[simp]
theorem BitVec.ofNatLT_eq_iff {m d n} {h : m < (2:ℕ) ^ d} {g: n < 2 ^ d}: BitVec.ofNatLT _ h = BitVec.ofNatLT _ g ↔ m = n := by
  apply Iff.intro
  · intro hp
    cases hp
    rfl
  · rintro rfl
    rfl'

theorem List.lt_append_of_lt [DecidableEq α] [LT α] [DecidableLT α] (l₁ l₂ l₃ l₄: List α):
    l₁.length = l₂.length → l₁ < l₂ → l₁ ++ l₃ < l₂ ++ l₄ := by
  intro hl hlt
  rw [List.lt_iff_exists] at hlt
  simp only [hl, List.take_length, lt_self_iff_false, and_false, exists_idem, false_or] at hlt
  rcases hlt with ⟨i, h, _⟩
  rw [List.lt_iff_exists]
  right
  exists i, (by simp only [List.length_append]; linarith), (by simp only [List.length_append]; linarith)
  apply And.intro
  · intro j hj
    have : j < l₁.length := by linarith
    have : j < l₂.length := by linarith
    simp_all
  · simp_all

instance : Std.Total (fun (x1: U s) x2 => ¬x1 < x2) := { total := by simp [BitVec.le_total] }
instance : Std.Antisymm (fun (x1: U s) x2 => ¬x1 < x2) where
  antisymm _ _ _ _ := by simp_all only [BitVec.not_lt]; apply BitVec.le_antisymm <;> assumption
  instance : Std.Irrefl (fun (x1: U s) x2 => x1 < x2) where
  irrefl _ := BitVec.lt_irrefl _

theorem U.cases_one (i : U 1) : i = 0 ∨ i = 1 := by
  fin_cases i <;> simp

@[simp]
theorem RadixVec.ofDigitsBE_cons {r: Radix} {d: Nat} {x: Digit r} {xs: List.Vector (Digit r) d}:
    RadixVec.ofDigitsBE (r:=r) (x ::ᵥ xs) = (x.val * r.val ^ d + RadixVec.ofDigitsBE xs) := by
  rfl

theorem ofDigitsBE_lt {r:Radix} {d: Nat} {l: List.Vector (Digit r) d}:
    (RadixVec.ofDigitsBE l).val < r.val ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    cases' l using List.Vector.casesOn with _ x xs
    simp only [RadixVec.ofDigitsBE_cons, List.length_cons, Nat.pow_succ, gt_iff_lt]
    have : r.val - 1 + 1 = r.val := by
      apply Nat.sub_one_add_one
      simp only [ne_eq, Nat.ne_zero_iff_zero_lt]
      exact lt_trans (by decide) r.prop
    calc
      _ ≤ (r - 1) * r.val ^ d + RadixVec.ofDigitsBE xs := by
        simp only [add_le_add_iff_right]
        rw [Nat.mul_le_mul_right_iff (by by_contra; simp_all)]
        apply Nat.le_of_lt_succ
        rw [Nat.succ_eq_add_one, this]
        exact x.prop
      _ < (r - 1) * r.val ^ d + r.val ^ d := by simp [*]
      _ = (↑r - 1) * ↑r ^ d + 1 * ↑r ^ d := by simp
      _ = _ := by rw [←Nat.add_mul, this, mul_comm]

theorem ofDigitsBE'_lt {r:Radix} {l: List (Digit r)}:
    RadixVec.ofDigitsBE' l < r ^ l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [RadixVec.ofDigitsBE'_cons, List.length_cons, Nat.pow_succ, gt_iff_lt]
    have : r.val - 1 + 1 = r.val := by
      apply Nat.sub_one_add_one
      simp only [ne_eq, Nat.ne_zero_iff_zero_lt]
      exact lt_trans (by decide) r.prop
    calc
      _ ≤ (r - 1) * r.val ^ xs.length + RadixVec.ofDigitsBE' xs := by
        simp only [add_le_add_iff_right]
        rw [Nat.mul_le_mul_right_iff (by by_contra; simp_all)]
        apply Nat.le_of_lt_succ
        rw [Nat.succ_eq_add_one, this]
        exact x.prop
      _ < (r - 1) * r.val ^ xs.length + r.val ^ xs.length := by linarith
      _ = (↑r - 1) * ↑r ^ xs.length + 1 * ↑r ^ xs.length := by simp
      _ = _ := by rw [←Nat.add_mul, this, mul_comm]

@[simp]
theorem ofDigitsBE_toDigitsBE {r: Radix} {n : RadixVec r d}: RadixVec.ofDigitsBE (RadixVec.toDigitsBE n) = n := by
  induction d with
  | zero =>
    cases' r with r hr
    cases' n with n hn
    have : n = 0 := by simp_all
    simp [RadixVec.toDigitsBE, RadixVec.ofDigitsBE, this]
  | succ d ih =>
    conv_rhs => rw [RadixVec.msd_lsds_decomposition (v:=n)]
    simp [RadixVec.ofDigitsBE, RadixVec.toDigitsBE, ih]

@[simp]
theorem toDigitsBE_ofDigitsBE {r: Radix} {v : List.Vector (Digit r) d}: RadixVec.toDigitsBE (RadixVec.ofDigitsBE v) = v := by
  induction' v using List.Vector.inductionOn
  · rfl
  · simp only [RadixVec.toDigitsBE, RadixVec.ofDigitsBE]
    congr
    · simp only [List.Vector.head_cons, List.Vector.tail_cons]
      simp only [RadixVec.msd]
      apply Fin.eq_of_val_eq
      simp only
      rw [Nat.mul_comm]
      rw [Nat.mul_add_div]
      · rw [Nat.div_eq_of_lt]
        · simp
        · exact ofDigitsBE_lt
      · cases r
        apply Nat.lt_of_succ_le
        apply Nat.one_le_pow
        linarith
    · rename_i h
      simp only [List.Vector.head_cons, List.Vector.tail_cons]
      simp only [RadixVec.lsds]
      conv_rhs => rw [←h]
      congr 2
      simp only [RadixVec.msd]
      conv_lhs =>
        arg 2
        arg 1
        rw [Nat.mul_comm]
      rw [Nat.mul_add_div]
      · rw [Nat.div_eq_of_lt]
        · simp
        · exact ofDigitsBE_lt
      · cases r
        apply Nat.lt_of_succ_le
        apply Nat.one_le_pow
        linarith

theorem ofDigitsBE'_toDigitsBE' {r: Radix} {n : Nat}: RadixVec.ofDigitsBE' (RadixVec.toDigitsBE' r n) = n := by
  simp only [RadixVec.toDigitsBE', RadixVec.ofDigitsBE']
  generalize_proofs hn hlen
  conv_rhs => change (Fin.mk n hn).val; rw [←ofDigitsBE_toDigitsBE (n := ⟨n, hn⟩)]
  congr <;> simp

theorem ofDigitsBE_mono {r: Radix} {l₁ l₂: List.Vector (Digit r) d}: l₁.toList < l₂.toList → RadixVec.ofDigitsBE l₁ < RadixVec.ofDigitsBE l₂ := by
  intro hp
  induction d with
  | zero =>
    cases List.Vector.eq_nil l₁
    cases List.Vector.eq_nil l₂
    simp at hp
  | succ d ih =>
    cases' l₁ with l₁ l₁_len
    cases' l₂ with l₂ l₂_len
    cases' hp
    · simp at l₁_len
    · rename_i h₁ l₁ h₂ l₂ hh
      rw [Fin.lt_def] at hh
      simp only [RadixVec.ofDigitsBE, List.Vector.head, Fin.mk_lt_mk]
      calc
        _ < h₁.val * r.val ^ d + r.val ^ d := by simp
        _ = (h₁.val + 1) * r.val ^ d := by linarith
        _ ≤ h₂ * r.val ^ d := by
          apply Nat.mul_le_mul_right
          linarith
        _ ≤ _ := by linarith
    · simp only [RadixVec.ofDigitsBE, List.Vector.head, Fin.mk_lt_mk, List.Vector.tail]
      rename_i _ l₁ l₂ hp
      simp only [List.length_cons, Nat.add_right_cancel_iff] at l₁_len l₂_len
      have : (List.Vector.toList ⟨l₁, l₁_len⟩ < List.Vector.toList ⟨l₂, l₂_len⟩) := hp

      have := ih this
      rw [Fin.lt_def] at this
      linarith

theorem ofDigitsBE'_mono {r: Radix} {l₁ l₂: List (Digit r)}: l₁.length = l₂.length → l₁ < l₂ → RadixVec.ofDigitsBE' l₁ < RadixVec.ofDigitsBE' l₂ := by
  intro hl hlt
  have := ofDigitsBE_mono (l₁ := ⟨l₁, hl⟩) (l₂ := ⟨l₂, rfl⟩) hlt
  rw [Fin.lt_def] at this
  simp only [RadixVec.ofDigitsBE']
  convert this

theorem ofDigitsBE'_toList {r : Radix} {l : List.Vector (Digit r) d}: RadixVec.ofDigitsBE' l.toList = (RadixVec.ofDigitsBE l).val := by
  simp only [RadixVec.ofDigitsBE']
  congr <;> simp

theorem to_be_bits_intro :
    STHoare p env ⟦⟧
    («std-1.0.0-beta.12::field::to_be_bits».call h![N] h![f])
    fun r => ∃∃(lt : f.val < (2 ^ N.toNat)), r = (RadixVec.toDigitsBE (d := N.toNat) (r := 2) ⟨f.val, by simp_all [OfNat.ofNat]⟩ |>.map BitVec.ofFin) := by
  rcases N with ⟨⟨N,_⟩⟩
  -- cases' N with N
  enter_decl
  steps
  · exact ()
  step_as (⟦⟧) (fun _ => RadixVec.ofDigitsBE' (bits.toList.map (fun i => (i.toFin : Digit 2))) < p.natVal)
  · apply STHoare.iteTrue_intro
    steps
    · exact ()
    rename' p => pbits
    by_cases h: bits.length = pbits.length
    · cases' bits with bits bitsLen
      simp only [BitVec.toNat_ofFin] at bitsLen
      cases bitsLen
      loop_inv nat fun i _ _ => (bits.take i ≤ pbits.take i) ⋆ [ok ↦ ⟨_, decide $ bits.take i < (pbits.take i)⟩]
      · simp
      · simp only [h]
        simp [BitVec.ofNatLT_eq_ofNat]
      · simp
      · intro i _ _
        steps
        by_cases h: bits.take i < pbits.take i
        · simp only [h]
          apply STHoare.iteFalse_intro
          have : bits.take (i + 1) < pbits.take (i + 1) := by
            repeat rw [List.take_succ_eq_append_getElem (by simp_all)]
            apply List.lt_append_of_lt
            · simp_all
            · assumption
          steps
          · apply List.le_of_lt
            assumption
          · simp_all
        · simp only [h]
          apply STHoare.iteTrue_intro
          rename bits.take i ≤ pbits.take i => hle
          have : bits.take i = pbits.take i := by
            rw [List.le_iff_lt_or_eq] at hle
            tauto
          steps
          by_cases hi : bits[i] = pbits[i]
          · convert STHoare.iteFalse_intro _
            · simp [List.Vector.get, hi]
            · rw [List.take_succ_eq_append_getElem (by assumption)]
              rw [List.take_succ_eq_append_getElem (by assumption)]
              rw [this, hi]
              steps
              · apply List.le_refl
              · congr
                simp [List.le_refl]
          · convert STHoare.iteTrue_intro _
            · simp [List.Vector.get, hi]
            · steps 7
              have hpbit : pbits[i] = 1 := by
                simp_all [Int.cast, IntCast.intCast]
              have hbit: bits[i] = 0 := by
                have := U.cases_one bits[i]
                simp_all
              have bitle : bits[i] < pbits[i] := by simp [hpbit, hbit]
              have : bits.take (i + 1) < pbits.take (i + 1) := by
                rw [List.take_succ_eq_append_getElem (by assumption)]
                rw [List.take_succ_eq_append_getElem (by assumption)]
                rw [this]
                apply List.append_left_lt
                rw [List.cons_lt_cons_iff]
                left
                exact bitle
              steps
              · apply List.le_of_lt this
              · congr
                simp [this]
      steps
      rename decide _ = true => hlt
      have : bits.length = pbits.length := by simp_all
      simp only [BitVec.toNat_ofFin, List.take_length, beq_true, decide_eq_true_eq] at hlt
      simp only [this, List.take_length] at hlt
      rw [←ofDigitsBE'_toDigitsBE' (r := 2) (n := p.natVal)]
      apply ofDigitsBE'_mono
      · simp_all
      · have : RadixVec.toDigitsBE' 2 p.natVal =
          List.map (fun (i : BitVec 1) => (i.toFin : Digit 2)) (List.map (fun (d : Digit 2) => BitVec.ofNatLT d.val d.prop) (RadixVec.toDigitsBE' 2 p.natVal)) := by
          simp only [List.map_map]
          rw [eq_comm]
          convert List.map_id _
        rw [this]
        apply List.map_lt
        · intro x y h
          rw [BitVec.lt_def] at h
          rw [Fin.lt_def]
          exact h
        · subst pbits
          exact hlt
    · loop_inv nat fun _ _ _ => [ok ↦ ⟨_, true⟩]
      · congr
        simp only [BitVec.toNat_ne, *, List.Vector.length, BitVec.natCast_eq_ofNat, BitVec.ofNat_toNat]
        simp_all
      · simp
      · intro _ _ _
        steps
        apply STHoare.iteFalse_intro
        steps
      steps
      have : bits.length < pbits.length := by
        apply lt_of_le_of_ne
        · simp only [BitVec.natCast_eq_ofNat, List.Vector.length, BitVec.ofNat_toNat, BitVec.setWidth_eq] at *
          simp_all
        · assumption
      calc
        _ < _ := ofDigitsBE'_lt
        _ ≤ 2 ^ (pbits.length - 1) := by
          apply Nat.pow_le_pow_right
          · decide
          · apply Nat.le_pred_of_lt
            simp_all
        _ = 2 ^ Nat.log 2 p.natVal := by
          subst pbits
          simp [RadixVec.toDigitsBE', OfNat.ofNat]
        _ ≤ _ := by apply Nat.pow_log_le_self; simp [Prime.natVal]
  steps
  rotate_left
  · rename_i v _
    subst_vars
    simp
    rw [ZMod.val_natCast]
    apply lt_of_le_of_lt (Nat.mod_le _ _)
    apply ofDigitsBE_lt
  · rename_i h v _
    subst_vars
    simp only [←List.Vector.toList_map, ofDigitsBE'_toList] at h
    conv_rhs =>
      enter [2, 1, 1]
      rw [ZMod.val_natCast]
      rw [Nat.mod_eq_of_lt h]
    apply List.Vector.eq
    rw [eq_comm]
    simp only [BitVec.toNat_ofFin, Fin.eta, toDigitsBE_ofDigitsBE,
      List.Vector.toList_map, List.map_map]
    convert List.map_id _
