import Mathlib.Tactic

namespace Lampe

abbrev Radix: Type := { n : Nat // n > 1 }

abbrev Digit (r : Radix) := Fin r.1
abbrev RadixVec (r : Radix) (d : Nat) := Fin (r ^ d)

namespace RadixVec

variable {r: Radix} {d : Nat}

def of (r : Radix) (v : Nat) : RadixVec r (Nat.log r.val v + 1) :=
  ⟨v, Nat.lt_pow_succ_log_self r.prop _⟩

def msd (v: RadixVec r (d + 1)): Digit r :=
  Fin.mk
    (v.val / (r.1 ^ d))
    (Nat.div_lt_of_lt_mul v.prop)

def lsds (v : RadixVec r (d + 1)) : RadixVec r d :=
  Fin.mk
    (v.val - msd v * r ^ d)
    (by
      simp only [msd]
      rw [Nat.div_mul_self_eq_mod_sub_self]
      have := Nat.mod_le v (r ^ d)
      have : v.val ≥ (v.val - v.val % r^d) := by apply Nat.sub_le
      zify [*]
      ring_nf
      convert Int.emod_lt _ _ using 1
      · simp
      · have : r.val ≠ 0 := by
          intro hp
          have := r.prop
          linarith
        simp [*]
    )

theorem msd_lsds_decomposition {v : RadixVec r (d + 1)}:
    v = ⟨v.msd.val * r^d + v.lsds.val, by
      simp only [msd, lsds]
      rw [Nat.div_mul_self_eq_mod_sub_self]
      have := Nat.mod_le v (r ^ d)
      have : v.val ≥ (v.val - v.val % r^d) := by apply Nat.sub_le
      zify [*]
      have := v.prop
      zify at this
      simp [*]
    ⟩ := by
  simp only [msd, lsds]
  apply Fin.eq_of_val_eq
  simp only
  rw [Nat.div_mul_self_eq_mod_sub_self]
  have := Nat.mod_le v (r ^ d)
  have : v.val ≥ (v - v % r^d) := by apply Nat.sub_le
  zify [*]
  simp

theorem msd_lsds_decomposition_unique {v : RadixVec r (d + 1)} {msd' : Digit r} {lsds' : RadixVec r d} {h}:
    v = ⟨msd'.val * r^d + lsds'.val, h⟩ ↔ msd' = v.msd ∧ lsds' = v.lsds := by
  apply Iff.intro
  · rintro rfl
    apply And.intro
    · simp only [msd]
      apply Fin.eq_of_val_eq
      simp only
      rw [mul_comm, Nat.mul_add_div, Nat.div_eq_of_lt, Nat.add_zero]
      · exact lsds'.prop
      · have := r.prop
        have := Nat.one_le_pow d r.val (by linarith)
        linarith
    · simp only [lsds, msd]
      apply Fin.eq_of_val_eq
      simp only
      rw [mul_comm, Nat.mul_add_div, Nat.div_eq_of_lt, mul_comm]
      · simp
      · exact lsds'.prop
      · have := r.prop
        have := Nat.one_le_pow d r.val (by linarith)
        linarith
  · rintro ⟨rfl, rfl⟩
    apply msd_lsds_decomposition

def toDigitsBE {d} (v : RadixVec r d): List.Vector (Digit r) d := match d with
| 0 => List.Vector.nil
| _ + 1 => v.msd ::ᵥ toDigitsBE v.lsds

def ofLimbsBE {d} (r : Nat) (v : List.Vector ℕ d): ℕ := match d with
| 0 => 0
| d + 1 => v.head * r^d + ofLimbsBE r v.tail

def ofDigitsBE {d} {r : Radix} (v : List.Vector (Digit r) d): RadixVec r d := ⟨ofLimbsBE r.val (v.map (fun d => d.val)), by
  induction d with
  | zero => simp [ofLimbsBE]
  | succ d ih =>
    simp only [ofLimbsBE, List.Vector.head_map, List.Vector.tail_map]
    calc
      _ < v.head.val * r.val^d + r.val^d := by
        have := ih v.tail
        linarith
      _ = (v.head.val + 1) * r.val^d := by linarith
      _ ≤ r * r.val^d := by
        have := Nat.succ_le_of_lt v.head.prop
        apply Nat.mul_le_mul_right
        assumption
      _ = _ := by simp [Nat.pow_succ, Nat.mul_comm]
⟩

-- def ofDigitsBE {d} (v : List.Vector (Digit r) d): RadixVec r d := match d with
-- | 0 => ⟨0, by simp⟩
-- | d + 1 => ⟨v.head.val * r^d + (ofDigitsBE v.tail).val, by
--   have : r.val^(d+1) = (r - 1) * r^d + r^d := by
--     have : r.val = r - 1 + 1 := by
--       have : r.val ≥ 1 := by linarith [r.prop]
--       rw [Nat.sub_add_cancel this]
--     rw [pow_succ]
--     conv_lhs => arg 2; rw [this]
--     conv_lhs => rw [Nat.mul_add]
--     simp [mul_comm]
--   rw [this]
--   apply Nat.add_lt_add_of_le_of_lt
--   · apply Nat.mul_le_mul
--     · apply Nat.le_of_lt_succ
--       have : r.val = r - 1 + 1 := by
--         have : r.val ≥ 1 := by linarith [r.prop]
--         rw [Nat.sub_add_cancel this]
--       simp [←this]
--     · apply le_refl
--   · exact Fin.prop _
-- ⟩

def ofDigitsBE' (l : List (Digit r)): Nat :=
  (RadixVec.ofDigitsBE ⟨l, rfl⟩).val

@[simp]
theorem ofDigitsBE'_nil : ofDigitsBE' (r:=r) [] = 0 := by rfl

@[simp]
theorem ofDigitsBE'_cons : ofDigitsBE' (r:=r) (x :: xs) = x * r ^ xs.length + ofDigitsBE' xs := by
  rfl

@[simp]
theorem ofDigitsBE'_append :
    ofDigitsBE' (r:=r) (xs ++ ys) = ofDigitsBE' xs * r ^ ys.length + ofDigitsBE' ys := by
  induction xs with
  | nil => simp
  | cons _ _ ih =>
    simp only [List.cons_append, ofDigitsBE'_cons, List.length_append, ih,
      Nat.pow_add, Nat.add_mul
    ]
    linarith

def toDigitsBE' (r: Radix) (n : Nat): List (Digit r) :=
  toDigitsBE ⟨n, Nat.lt_pow_succ_log_self r.prop _⟩ |>.toList

instance : OfNat Radix 2 where
  ofNat := ⟨2, by simp⟩

lemma ofDigitsBE_cons {r: Radix} {d: Nat} {x: Digit r} {xs: List.Vector (Digit r) d}:
  ofDigitsBE (r:=r) (x ::ᵥ xs)
  = (x.val * r.val ^ d + ofDigitsBE xs) := by
  rfl

@[simp]
theorem ofDigitsBE_cons' {r: Radix} {d: Nat} {x: Digit r} {xs: List.Vector (Digit r) d}:
  ofDigitsBE (r:=r) (x ::ᵥ xs) = ⟨x.val * r.val ^ d + ofDigitsBE xs, by
    calc
      _ < x.val * r.val ^ d + r.val ^ d := by simp
      _ = (x.val + 1) * r.val ^ d := by linarith
      _ ≤ r * r.val ^ d := by
        apply Nat.mul_le_mul_right
        have := x.prop
        linarith
      _ = _ := by simp [Nat.pow_succ, Nat.mul_comm]
  ⟩ := by
  rfl


theorem ofDigitsBE_lt {r:Radix} {d: Nat} {l: List.Vector (Digit r) d}:
    (ofDigitsBE l).val < r.val ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    cases' l using List.Vector.casesOn with _ x xs
    rw [ofDigitsBE_cons, Nat.pow_succ]
    have : r.val - 1 + 1 = r.val := by omega
    calc
      _ ≤ (r - 1) * r.val ^ d + ofDigitsBE xs := by
        rw [
          add_le_add_iff_right,
          Nat.mul_le_mul_right_iff (by by_contra; simp_all)
        ]
        apply Nat.le_of_lt_succ
        rw [Nat.succ_eq_add_one, this]
        exact x.prop
      _ < (r - 1) * r.val ^ d + r.val ^ d := by simp [*]
      _ = (↑r - 1) * ↑r ^ d + 1 * ↑r ^ d := by simp
      _ = _ := by rw [←Nat.add_mul, this, mul_comm]

theorem ofDigitsBE'_lt {r:Radix} {l: List (Digit r)}:
    ofDigitsBE' l < r ^ l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [ofDigitsBE'_cons, List.length_cons, Nat.pow_succ]
    have : r.val - 1 + 1 = r.val := by omega
    calc
      _ ≤ (r - 1) * r.val ^ xs.length + ofDigitsBE' xs := by
        rw [
          add_le_add_iff_right,
          Nat.mul_le_mul_right_iff (by by_contra; simp_all)
        ]
        apply Nat.le_of_lt_succ
        rw [Nat.succ_eq_add_one, this]
        exact x.prop
      _ < (r - 1) * r.val ^ xs.length + r.val ^ xs.length := by linarith
      _ = (↑r - 1) * ↑r ^ xs.length + 1 * ↑r ^ xs.length := by simp
      _ = _ := by rw [←Nat.add_mul, this, mul_comm]

theorem ofDigitsBE_toDigitsBE {r: Radix} {n : RadixVec r d}: ofDigitsBE (toDigitsBE n) = n := by
  induction d with
  | zero =>
    cases' r with r hr
    cases' n with n hn
    have : n = 0 := by simp_all
    simp [toDigitsBE, ofDigitsBE, ofLimbsBE, this]
  | succ d ih =>
    conv_rhs => rw [msd_lsds_decomposition (v:=n)]
    have := Fin.val_eq_of_eq $ ih (n := n.lsds)
    simpa [ofDigitsBE, toDigitsBE, ofLimbsBE]

theorem toDigitsBE_ofDigitsBE {r: Radix} {v : List.Vector (Digit r) d}: toDigitsBE (ofDigitsBE v) = v := by
  induction' v using List.Vector.inductionOn
  · rfl
  · simp only [toDigitsBE, ofDigitsBE_cons']
    congr
    · rw [msd]
      apply Fin.eq_of_val_eq
      simp only
      rw [Nat.mul_comm, Nat.mul_add_div]
      · rw [Nat.div_eq_of_lt]
        · simp
        · exact ofDigitsBE_lt
      · cases r
        apply Nat.lt_of_succ_le
        apply Nat.one_le_pow
        linarith
    · rename_i h
      simp only [lsds]
      conv_rhs => rw [←h]
      congr 1
      apply Fin.eq_of_val_eq
      simp only [msd]
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

theorem ofDigitsBE'_toDigitsBE' {r: Radix} {n : Nat}:
  ofDigitsBE' (toDigitsBE' r n) = n := by
  simp only [toDigitsBE', ofDigitsBE']
  generalize_proofs hn hlen
  conv_rhs => change (Fin.mk n hn).val; rw [←ofDigitsBE_toDigitsBE (n := ⟨n, hn⟩)]
  congr <;> simp

theorem ofDigitsBE_mono {r: Radix} {l₁ l₂: List.Vector (Digit r) d}:
  l₁.toList < l₂.toList → ofDigitsBE l₁ < ofDigitsBE l₂ := by
  intro hp
  induction d with
  | zero =>
    cases List.Vector.eq_nil l₁
    cases List.Vector.eq_nil l₂
    simp at hp
  | succ d ih =>
    cases' l₁ using List.Vector.casesOn with _ h₁
    cases' l₂ using List.Vector.casesOn with _ h₂
    cases' hp
    · rename_i t₁ t₂ hh
      rw [Fin.lt_def] at hh
      simp only [ofDigitsBE_cons', List.Vector.head, Fin.mk_lt_mk]
      calc
        _ < h₁.val * r.val ^ d + r.val ^ d := by simp
        _ = (h₁.val + 1) * r.val ^ d := by linarith
        _ ≤ h₂ * r.val ^ d := by
          apply Nat.mul_le_mul_right
          linarith
        _ ≤ _ := by linarith
    · simp only [ofDigitsBE_cons', List.Vector.head, Fin.mk_lt_mk, List.Vector.tail]
      rename_i _ _ hp
      have := ih hp
      rw [Fin.lt_def] at this
      linarith

theorem ofDigitsBE'_mono {r: Radix} {l₁ l₂: List (Digit r)}: l₁.length = l₂.length → l₁ < l₂ → ofDigitsBE' l₁ < ofDigitsBE' l₂ := by
  intro hl hlt
  have := ofDigitsBE_mono (l₁ := ⟨l₁, hl⟩) (l₂ := ⟨l₂, rfl⟩) hlt
  rw [Fin.lt_def] at this
  simp only [ofDigitsBE']
  convert this

theorem ofDigitsBE'_toList {r : Radix} {l : List.Vector (Digit r) d}: ofDigitsBE' l.toList = (ofDigitsBE l).val := by
  simp only [ofDigitsBE']
  congr <;> simp

theorem ofDigitsBE'_subtype_eq {r : Radix} {l : List.Vector (Digit r) d} (hlt : ofDigitsBE' l.toList < r.val^d) :
    (⟨ofDigitsBE' l.toList, hlt⟩ : RadixVec r d) = ofDigitsBE l := by
  ext
  exact ofDigitsBE'_toList

end RadixVec


-- /-- Extends the given list `a` up to length `len` with the default value of `α` -/
-- def extList (lst : List α) (len : Nat) (default : α) : List α
--   := lst ++ (List.replicate (len - lst.length) default)

-- @[reducible]
-- def decomposeToRadix (r : Nat) (v : Nat) (h : r > 1) : List Nat := match v with
-- | .zero => List.nil
-- | v' + 1 => List.cons ((v' + 1) % r) (decomposeToRadix r ((v' + 1) / r) h)
-- decreasing_by
--   rw [Nat.succ_eq_add_one, Nat.div_lt_iff_lt_mul]
--   rw [Nat.lt_mul_iff_one_lt_right]
--   tauto
--   exact Nat.succ_pos v'
--   rw [<-Nat.ne_zero_iff_zero_lt]
--   aesop

-- example : decomposeToRadix 10 123 (by linarith) = [3, 2, 1] := by rfl
-- example : decomposeToRadix 2 123 (by linarith) = [1, 1, 0, 1, 1, 1, 1] := by rfl

-- def composeFromRadix (r : Nat) (l : List Nat) : Nat := (l.reverse.foldl (fun acc d => acc * r + d) 0)

-- example : (composeFromRadix 10 [3, 2, 1]) = 123 := by rfl
-- example : (composeFromRadix 2 [1, 1, 0, 1, 1, 1, 1]) = 123 := by rfl

-- theorem decomposeToRadix_zero (r : Nat) (h : r > 1) :
--     decomposeToRadix r 0 h = [] := by
--   rfl

-- theorem composeFromRadix_nil (r : Nat) :
--     composeFromRadix r [] = 0 := by
--   rfl

-- theorem decomposeToRadix_in_fin (r v : Nat) (h : r > 1) :
--     ∀ {k}, k ∈ decomposeToRadix r v h → k < r := by
--   revert h
--   refine Nat.strong_induction_on v ?_
--   intro v ih h k hk
--   cases v with
--   | zero =>
--     rw [decomposeToRadix_zero] at hk
--     simp_all only [gt_iff_lt, not_lt_zero', not_isEmpty_of_nonempty, IsEmpty.forall_iff, imp_self, implies_true,
--       List.not_mem_nil]
--   | succ v =>
--     have hrpos : 0 < r := lt_trans Nat.zero_lt_one h
--     simp [decomposeToRadix, Nat.succ_eq_add_one] at hk ⊢
--     rcases hk with hk | hk
--     · exact Nat.mod_lt _ hrpos
--     · have hlt : (v + 1) / r < v + 1 := Nat.div_lt_self (Nat.succ_pos _) h
--       apply ih <;> assumption

-- theorem composeFromRadix_cons (r : Nat) (l : List Nat) :
--     composeFromRadix r (a :: l) = composeFromRadix r l * r + a := by
--   unfold composeFromRadix
--   simp only [List.reverse_cons, List.foldl_append, List.foldl, List.foldl_reverse,
--     Nat.add_left_cancel_iff]

-- theorem composeFromRadix_decomposeToRadix (r v : Nat) (h : r > 1) :
--     composeFromRadix r (decomposeToRadix r v h) = v := by
--   revert h
--   refine Nat.strong_induction_on v ?_
--   intro v ih h
--   cases v with
--   | zero =>
--     rw [decomposeToRadix_zero, composeFromRadix_nil]
--   | succ v =>
--     have hstepSucc : decomposeToRadix r (Nat.succ v) h = ((Nat.succ v) % r) :: decomposeToRadix r ((Nat.succ v) / r) h := rfl
--     have hstep : decomposeToRadix r (v + 1) h = ((v + 1) % r) :: decomposeToRadix r ((v + 1) / r) h := by simpa [Nat.succ_eq_add_one] using hstepSucc
--     have hlt : (v + 1) / r < v + 1 := Nat.div_lt_self (Nat.succ_pos _) h
--     have ih' : composeFromRadix r (decomposeToRadix r ((v + 1) / r) h) = (v + 1) / r := ih ((v + 1) / r) hlt h
--     calc
--       composeFromRadix r (decomposeToRadix r (v + 1) h)
--           = composeFromRadix r (((v + 1) % r) :: decomposeToRadix r ((v + 1) / r) h) := by
--             simp [hstep]
--         _ = composeFromRadix r (decomposeToRadix r ((v + 1) / r) h) * r + ((v + 1) % r) := by
--             simp [composeFromRadix_cons]
--         _ = ((v + 1) / r) * r + ((v + 1) % r) := by
--             simp [ih']
--         _ = v + 1 := by
--             have := Nat.mod_add_div (v + 1) r
--             simpa [Nat.add_comm, Nat.mul_comm] using this

-- theorem composeFromRadix_mono_forall₂_le (r : Nat) :
--     ∀ {x y : List Nat}, List.Forall₂ (fun a b => a ≤ b) x y →
--       composeFromRadix r x ≤ composeFromRadix r y := by
--   intro x y hxy
--   induction hxy with
--   | nil =>
--       simp [composeFromRadix_nil]
--   | @cons a b xs ys hab hrest ih =>
--       have hmul : composeFromRadix r xs * r ≤ composeFromRadix r ys * r :=
--         Nat.mul_le_mul_right _ ih
--       have hadd : composeFromRadix r xs * r + a ≤ composeFromRadix r ys * r + b :=
--         Nat.add_le_add hmul hab
--       simpa [composeFromRadix_cons] using hadd

-- theorem decomposeToRadix_length_lower_bound (r v : Nat) (h : 1 < r) :
--     (decomposeToRadix r v h).length > 0 → v ≥ r ^ ((decomposeToRadix r v h).length - 1) := by
--   intro h_len_pos
--   revert h h_len_pos
--   refine Nat.strong_induction_on v ?_
--   intro v ih h h_len_pos
--   cases v with
--   | zero =>
--     rw [decomposeToRadix_zero] at h_len_pos
--     simp at h_len_pos
--   | succ v =>
--     have h_rec : decomposeToRadix r (v + 1) h = ((v + 1) % r) :: decomposeToRadix r ((v + 1) / r) h := rfl
--     rw [h_rec] at h_len_pos ⊢
--     simp only [List.length_cons] at h_len_pos ⊢
--     cases Nat.eq_zero_or_pos (decomposeToRadix r ((v + 1) / r) h).length with
--     | inl h_zero =>
--       rw [h_zero]
--       simp
--     | inr h_pos =>
--       have h_div_lt : (v + 1) / r < v + 1 := Nat.div_lt_self (Nat.succ_pos _) h
--       have ih_div := ih ((v + 1) / r) h_div_lt h h_pos
--       calc v + 1
--           = r * ((v + 1) / r) + ((v + 1) % r) := (Nat.div_add_mod (v + 1) r).symm
--         _ ≥ r * ((v + 1) / r) + 0 := by
--               exact Nat.add_le_add_left (Nat.zero_le _) _
--         _ = r * ((v + 1) / r) := by
--               simp
--         _ ≥ r * r ^ ((decomposeToRadix r ((v + 1) / r) h).length - 1) := by
--               exact Nat.mul_le_mul_left r ih_div
--         _ = r ^ (1 + ((decomposeToRadix r ((v + 1) / r) h).length - 1)) := by
--               rw [Nat.pow_add, Nat.pow_one]
--         _ = r ^ (decomposeToRadix r ((v + 1) / r) h).length := by
--               have : 1 + ((decomposeToRadix r ((v + 1) / r) h).length - 1) = (decomposeToRadix r ((v + 1) / r) h).length := by
--                 omega
--               rw [this]
--         _ = r ^ ((decomposeToRadix r ((v + 1) / r) h).length + 1 - 1) := by
--               simp [Nat.add_sub_cancel]

-- theorem decomposeToRadix_length_upper_bound (r v : Nat) (h : 1 < r) :
--     v < r ^ (decomposeToRadix r v h).length := by
--   revert h
--   refine Nat.strong_induction_on v ?_
--   intro v ih h
--   cases v with
--   | zero =>
--     rw [decomposeToRadix_zero]
--     simp only [List.length_nil, Nat.pow_zero]
--     omega
--   | succ v =>
--     have h_rec : decomposeToRadix r (v + 1) h = ((v + 1) % r) :: decomposeToRadix r ((v + 1) / r) h := rfl
--     rw [h_rec]
--     simp only [List.length_cons]
--     have h_div_lt : (v + 1) / r < v + 1 := Nat.div_lt_self (Nat.succ_pos _) h
--     have ih_div := ih ((v + 1) / r) h_div_lt h
--     have h_mod : (v + 1) % r < r := Nat.mod_lt _ (Nat.zero_lt_of_lt h)
--     have h_div_le : (v + 1) / r + 1 ≤ r ^ (decomposeToRadix r ((v + 1) / r) h).length := by
--       omega
--     calc v + 1
--         = r * ((v + 1) / r) + ((v + 1) % r) := (Nat.div_add_mod (v + 1) r).symm
--       _ ≤ r * ((v + 1) / r) + (r - 1) := by
--             apply Nat.add_le_add_left
--             omega
--       _ = r * ((v + 1) / r + 1) - 1 := by
--             have hr_pos : r ≥ 2 := h
--             have : r - 1 ≥ 1 := by omega
--             have calc1 : r * ((v + 1) / r) + (r - 1) = r * ((v + 1) / r) + r - 1 := by omega
--             have calc2 : r * ((v + 1) / r) + r = r * ((v + 1) / r + 1) := by ring
--             rw [calc1, calc2]
--       _ ≤ r * r ^ (decomposeToRadix r ((v + 1) / r) h).length - 1 := by
--             have : r * ((v + 1) / r + 1) ≤ r * r ^ (decomposeToRadix r ((v + 1) / r) h).length := by
--               exact Nat.mul_le_mul_left r h_div_le
--             omega
--       _ < r * r ^ (decomposeToRadix r ((v + 1) / r) h).length := by
--             have : 0 < r * r ^ (decomposeToRadix r ((v + 1) / r) h).length := by
--               apply Nat.mul_pos
--               · omega
--               · apply Nat.pow_pos
--                 omega
--             omega
--       _ = r ^ ((decomposeToRadix r ((v + 1) / r) h).length + 1) := by
--             rw [Nat.pow_succ, Nat.mul_comm]

-- theorem decomposeToRadix_le_mono_len (r v₁ v₂ : Nat) (h : 1 < r)
--     (h_len : (decomposeToRadix r v₁ h).length < (decomposeToRadix r v₂ h).length) : v₁ < v₂ := by
--   have h_v₁_bound := decomposeToRadix_length_upper_bound r v₁ h
--   cases Nat.eq_zero_or_pos (decomposeToRadix r v₂ h).length with
--   | inl h_zero =>
--     rw [h_zero] at h_len
--     simp at h_len
--   | inr h_pos =>
--     have h_v₂_bound := decomposeToRadix_length_lower_bound r v₂ h h_pos
--     calc v₁
--         < r ^ (decomposeToRadix r v₁ h).length := h_v₁_bound
--       _ ≤ r ^ ((decomposeToRadix r v₂ h).length - 1) := by
--             apply Nat.pow_le_pow_right
--             · omega
--             · omega
--       _ ≤ v₂ := h_v₂_bound

-- theorem decomposeToRadix_le_mono (r v₁ v₂ : Nat) (h : r > 1) (h_le : v₁ ≤ v₂) :
--     (decomposeToRadix r v₁ h).length ≤ (decomposeToRadix r v₂ h).length := by
--   by_contra h_not_le
--   push_neg at h_not_le
--   have h_v₂_lt_v₁ : v₂ < v₁ := decomposeToRadix_le_mono_len r v₂ v₁ h h_not_le
--   omega

-- theorem composeFromRadix_upper_bound (r : Nat) (l : List Nat) (h_all : ∀ d ∈ l, d < r) :
--     composeFromRadix r l < r ^ l.length := by
--   induction l with
--   | nil => simp [composeFromRadix_nil]
--   | cons hd tl ih =>
--     rw [composeFromRadix_cons]
--     have hd_bound : hd < r := h_all hd (by simp)
--     have tl_all : ∀ d ∈ tl, d < r := by
--       intros d hd_in
--       exact h_all d (by simp [hd_in])
--     simp only [List.length_cons]
--     rw [pow_succ]
--     by_cases h_tl_empty : tl = []
--     · simp [h_tl_empty, composeFromRadix_nil]
--       omega
--     · have ih' : composeFromRadix r tl < r ^ tl.length := ih tl_all
--       have h1 : composeFromRadix r tl + 1 ≤ r ^ tl.length := by omega
--       calc composeFromRadix r tl * r + hd
--           < composeFromRadix r tl * r + r := by omega
--         _ = (composeFromRadix r tl + 1) * r := by ring
--         _ ≤ r ^ tl.length * r := by
--             exact Nat.mul_le_mul_right r h1

-- theorem composeFromRadix_lower_bound (r : Nat) (l : List Nat) (h_ne : l ≠ [])
--     (h_all : ∀ d ∈ l, d < r) (_hr : r > 1)
--     (h_no_trail : l.getLast h_ne ≠ 0) :
--     r ^ (l.length - 1) ≤ composeFromRadix r l := by
--   induction l with
--   | nil =>
--     simp at h_ne
--   | cons hd tl ih =>
--     rw [composeFromRadix_cons]
--     cases tl with
--     | nil =>
--       have h_hd_nonzero : hd ≠ 0 := by
--         simp [List.getLast] at h_no_trail
--         exact h_no_trail
--       simp [composeFromRadix_nil, List.length_cons]
--       omega
--     | cons hd2 tl2 =>
--       simp only [List.length_cons, Nat.add_sub_cancel]
--       have h_all_tl : ∀ d ∈ hd2 :: tl2, d < r := by
--         intros d hd_in
--         exact h_all d (by simp [hd_in])
--       have h_ne_tl : hd2 :: tl2 ≠ [] := by simp
--       have h_no_trail_tl : (hd2 :: tl2).getLast h_ne_tl ≠ 0 := by
--         have := h_no_trail
--         simp [List.getLast_cons] at this ⊢
--         exact this
--       have ih_tl := ih h_ne_tl h_all_tl h_no_trail_tl
--       simp only [List.length_cons] at ih_tl
--       have : (tl2.length + 1 - 1) = tl2.length := by omega
--       rw [this] at ih_tl
--       rw [pow_succ, mul_comm]
--       calc r * r ^ tl2.length
--           ≤ r * composeFromRadix r (hd2 :: tl2) := by
--               exact Nat.mul_le_mul_left r ih_tl
--         _ = composeFromRadix r (hd2 :: tl2) * r := by ring
--         _ ≤ composeFromRadix r (hd2 :: tl2) * r + hd := by omega

-- theorem composeFromRadix_le_mono_len (r : Nat) :
--     ∀ {l₁ l₂ : List Nat}, l₁.length < l₂.length →
--       (∀ d ∈ l₁, d < r) → (∀ d ∈ l₂, d < r) → r > 1 →
--       (∀ h : l₂ ≠ [], l₂.getLast h ≠ 0) →
--       composeFromRadix r l₁ < composeFromRadix r l₂ := by
--   intro l₁ l₂ h_len h₁ h₂ hr h_no_trail
--   have h_upper_l₁ : composeFromRadix r l₁ < r ^ l₁.length :=
--     composeFromRadix_upper_bound r l₁ h₁

--   have h_l₂_ne : l₂ ≠ [] := by
--     intro h_eq
--     simp [h_eq] at h_len

--   have h_lower_l₂ : r ^ (l₂.length - 1) ≤ composeFromRadix r l₂ :=
--     composeFromRadix_lower_bound r l₂ h_l₂_ne h₂ hr (h_no_trail h_l₂_ne)

--   have h_pow : r ^ l₁.length ≤ r ^ (l₂.length - 1) := by
--     have h_l₂_pos : 0 < l₂.length := by omega
--     have : l₁.length ≤ l₂.length - 1 := by omega
--     exact Nat.pow_le_pow_right (by omega : 1 ≤ r) this

--   calc composeFromRadix r l₁
--       < r ^ l₁.length := h_upper_l₁
--     _ ≤ r ^ (l₂.length - 1) := h_pow
--     _ ≤ composeFromRadix r l₂ := h_lower_l₂

-- theorem composeFromRadix_append (l₁ l₂  : List Nat) (r : Nat) :
--     composeFromRadix r (l₁ ++ l₂) =
--       composeFromRadix r l₁ + r ^ l₁.length * composeFromRadix r l₂ := by
--   induction l₁ with
--   | nil =>
--     simp [composeFromRadix_nil, List.nil_append]
--   | cons hd tl ih =>
--     simp only [List.cons_append, List.length_cons]
--     rw [composeFromRadix_cons, ih, composeFromRadix_cons]
--     rw [Nat.pow_succ]
--     ring

-- theorem composeFromRadix_split (r : Nat) (l : List Nat) (k : Nat) (hk : k ≤ l.length) :
--     composeFromRadix r l =
--       composeFromRadix r (l.take k) + r ^ k * composeFromRadix r (l.drop k) := by
--   suffices ∀ l₁ l₂ : List Nat, composeFromRadix r (l₁ ++ l₂) =
--       composeFromRadix r l₁ + r ^ l₁.length * composeFromRadix r l₂ by
--     conv_lhs => rw [← List.take_append_drop k l]
--     rw [this]
--     congr 1
--     rw [List.length_take]
--     simp [hk]
--   intros; apply composeFromRadix_append


-- /-- If the radix decomposition of `n₁` and `n₂` have the same length and agree on all more
-- significant positions, but differ at the next lesser digit then they differ (this is basically the
-- lexicographic ordering on lists in little-endian format).
-- -/
-- theorem decomposeToRadix_lexicographic_gt (r n₁ n₂ : Nat) (h : r > 1) (m : Nat) :
--     let d₁ := decomposeToRadix r n₁ h
--     let d₂ := decomposeToRadix r n₂ h
--     let N := d₁.length
--     d₁.length = d₂.length →
--     N - 1 - m < N →
--     (∀ i < m, ∀ (h₁ : N - 1 - i < d₁.length) (h₂ : N - 1 - i < d₂.length),
--       d₁[N - 1 - i]'h₁ = d₂[N - 1 - i]'h₂) →
--     ∀ (hm₁ : N - 1 - m < d₁.length) (hm₂ : N - 1 - m < d₂.length),
--       d₁[N - 1 - m]'hm₁ > d₂[N - 1 - m]'hm₂ →
--       n₁ > n₂ := by
--   intro d₁ d₂ N h_len_eq h_idx_valid h_agree hm₁ hm₂ h_diff
--   have hn₁ : n₁ = composeFromRadix r d₁ :=
--     (composeFromRadix_decomposeToRadix r n₁ h).symm
--   have hn₂ : n₂ = composeFromRadix r d₂ :=
--     (composeFromRadix_decomposeToRadix r n₂ h).symm
--   rw [hn₁, hn₂]

--   have hd₁_in : ∀ d ∈ d₁, d < r := fun _ => decomposeToRadix_in_fin r n₁ h
--   have hd₂_in : ∀ d ∈ d₂, d < r := fun _ => decomposeToRadix_in_fin r n₂ h

--   set k := N - 1 - m with hk_def

--   have h_low_bound₁ : composeFromRadix r (d₁.take k) < r ^ k := by
--     have : (d₁.take k).length ≤ k := List.length_take_le k d₁
--     have h_all : ∀ d ∈ d₁.take k, d < r := by
--       intros d hd
--       apply hd₁_in
--       exact List.mem_of_mem_take hd
--     cases Nat.eq_zero_or_pos k with
--     | inl hk0 =>
--       rw [hk0]
--       simp [composeFromRadix_nil]
--     | inr hkpos =>
--       by_cases h_len : (d₁.take k).length = 0
--       · have : d₁.take k = [] := List.length_eq_zero_iff.mp h_len
--         simp [this, composeFromRadix_nil]
--         exact Nat.pow_pos (by omega : 0 < r)
--       · push_neg at h_len
--         have h_len_pos : (d₁.take k).length > 0 := Nat.pos_of_ne_zero h_len
--         have h_ub := composeFromRadix_upper_bound r (d₁.take k) h_all
--         calc composeFromRadix r (d₁.take k)
--             < r ^ (d₁.take k).length := h_ub
--           _ ≤ r ^ k := by
--               apply Nat.pow_le_pow_right (by omega : 1 ≤ r)
--               exact this

--   have h_low_bound₂ : composeFromRadix r (d₂.take k) < r ^ k := by
--     have : (d₂.take k).length ≤ k := List.length_take_le k d₂
--     have h_all : ∀ d ∈ d₂.take k, d < r := by
--       intros d hd
--       apply hd₂_in
--       exact List.mem_of_mem_take hd
--     cases Nat.eq_zero_or_pos k with
--     | inl hk0 =>
--       rw [hk0]
--       simp [composeFromRadix_nil]
--     | inr hkpos =>
--       by_cases h_len : (d₂.take k).length = 0
--       · have : d₂.take k = [] := List.length_eq_zero_iff.mp h_len
--         simp [this, composeFromRadix_nil]
--         exact Nat.pow_pos (by omega : 0 < r)
--       · push_neg at h_len
--         have h_len_pos : (d₂.take k).length > 0 := Nat.pos_of_ne_zero h_len
--         have h_ub := composeFromRadix_upper_bound r (d₂.take k) h_all
--         calc composeFromRadix r (d₂.take k)
--             < r ^ (d₂.take k).length := h_ub
--           _ ≤ r ^ k := by
--               apply Nat.pow_le_pow_right (by omega : 1 ≤ r)
--               exact this

--   have hsplit₁ : composeFromRadix r d₁ =
--       composeFromRadix r (d₁.take k) + r ^ k * composeFromRadix r (d₁.drop k) := by
--     apply composeFromRadix_split
--     omega

--   have hsplit₂ : composeFromRadix r d₂ =
--       composeFromRadix r (d₂.take k) + r ^ k * composeFromRadix r (d₂.drop k) := by
--     apply composeFromRadix_split
--     omega

--   rw [hsplit₁, hsplit₂]

--   have h_high_gt : composeFromRadix r (d₁.drop k) > composeFromRadix r (d₂.drop k) := by
--     have h_drop_len : (d₁.drop k).length = (d₂.drop k).length := by
--       simp only [List.length_drop]
--       omega

--     have h_nonempty₁ : d₁.drop k ≠ [] := by
--       intro h
--       have := List.length_eq_zero_iff.mpr h
--       simp [List.length_drop] at this
--       omega

--     have h_nonempty₂ : d₂.drop k ≠ [] := by
--       intro h
--       have := List.length_eq_zero_iff.mpr h
--       simp [List.length_drop] at this
--       omega

--     obtain ⟨hd₁, tl₁, heq₁⟩ := List.exists_cons_of_ne_nil h_nonempty₁
--     obtain ⟨hd₂, tl₂, heq₂⟩ := List.exists_cons_of_ne_nil h_nonempty₂

--     have h_hd₁ : hd₁ = d₁[k] := by
--       have h1 : d₁[k] = d₁[k + 0]'hm₁ := by simp
--       have h2 : d₁[k + 0]'hm₁ = (d₁.drop k)[0]'(by rw [heq₁]; simp) := by
--         have : 0 < (d₁.drop k).length := by
--           apply List.length_pos_of_ne_nil
--           simp [heq₁]
--         have asdf := @List.getElem_drop Nat d₁ k 0 this
--         rw [asdf]
--       have h3 : (d₁.drop k)[0]'(by rw [heq₁]; simp) = (hd₁ :: tl₁)[0]'(by simp) := by simp [heq₁]
--       have h4 : (hd₁ :: tl₁)[0]'(by simp) = hd₁ := rfl
--       rw [h1, h2, h3, h4]

--     have h_hd₂ : hd₂ = d₂[k] := by
--       have h1 : d₂[k] = d₂[k + 0]'hm₂ := by simp
--       have h2 : d₂[k + 0]'hm₂ = (d₂.drop k)[0]'(by rw [heq₂]; simp) := by
--         have : 0 < (d₂.drop k).length := by
--           apply List.length_pos_of_ne_nil
--           simp [heq₂]
--         have asdf := @List.getElem_drop Nat d₂ k 0 this
--         rw [asdf]
--       have h3 : (d₂.drop k)[0]'(by rw [heq₂]; simp) = (hd₂ :: tl₂)[0]'(by simp) := by simp [heq₂]
--       have h4 : (hd₂ :: tl₂)[0]'(by simp) = hd₂ := rfl
--       rw [h1, h2, h3, h4]

--     have h_tails_eq : composeFromRadix r tl₁ = composeFromRadix r tl₂ := by
--       have h_tl_len : tl₁.length = tl₂.length := by
--         have : (hd₁ :: tl₁).length = (hd₂ :: tl₂).length := by
--           rw [← heq₁, ← heq₂, h_drop_len]
--         simp at this
--         exact this

--       by_cases hm_zero : m = 0
--       · have : k = N - 1 := by rw [hk_def]; simp [hm_zero]
--         have : k + 1 = N := by omega
--         have h_drop_len1 : (d₁.drop k).length = N - k := by
--           simp only [List.length_drop]
--           rfl
--         have : (d₁.drop k).length = 1 := by omega
--         rw [heq₁] at this
--         simp at this
--         have h_tl₁_empty : tl₁ = [] := by
--           cases tl₁
--           · rfl
--           · simp at this
--         have h_tl₂_empty : tl₂ = [] := by
--           have : tl₂.length = 0 := by rw [← h_tl_len, h_tl₁_empty]; simp
--           cases tl₂
--           · rfl
--           · simp at this
--         simp [h_tl₁_empty, h_tl₂_empty]
--       · have hm_pos : 0 < m := Nat.zero_lt_of_ne_zero hm_zero
--         -- From hm₁: N - 1 - m < N, derive that N ≥ m + 1
--         have h_N_ge : N ≥ m + 1 := by
--           have : k < N := h_idx_valid
--           have : k = N - 1 - m := hk_def
--           have h_bound : N - 1 ≥ m := by
--             by_contra h_not
--             push_neg at h_not
--             have : N - 1 - m = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt h_not)
--             rw [← hk_def] at this
--             rw [this] at h_idx_valid
--             have h_N_le_m : N ≤ m := by omega
--             have h_i_bound : m - 1 < m := by omega
--             have h_idx_eq : N - 1 - (m - 1) = N - m := by omega
--             have h_N_m_zero : N - m = 0 := by omega
--             have h_eq_01 : d₁[0]'(by omega : 0 < N) = d₂[0]'(by rw [← h_len_eq]; omega : 0 < d₂.length) := by
--               have := h_agree (m - 1) h_i_bound (by omega) (by omega)
--               simp [h_idx_eq, h_N_m_zero] at this
--               exact this
--             have h_gt_01 : d₁[0]'(by omega : 0 < N) > d₂[0]'(by rw [← h_len_eq]; omega : 0 < d₂.length) := by
--               have h_k_eq_0 : k = 0 := this
--               calc d₁[0]'(by omega : 0 < N)
--                   = d₁[k]'(by omega : k < N) := by simp [h_k_eq_0]
--                 _ > d₂[k]'(by rw [← h_len_eq]; omega : k < d₂.length) := h_diff
--                 _ = d₂[0]'(by rw [← h_len_eq]; omega : 0 < d₂.length) := by simp [h_k_eq_0]
--             omega
--           -- N - 1 ≥ m is equivalent to N ≥ m + 1 for natural numbers
--           omega

--         have h_tl₁_len : tl₁.length = m := by
--           have h_cons_len : (hd₁::tl₁).length = (d₁.drop k).length := by rw [← heq₁]
--           have h_drop_k_len : (d₁.drop k).length = N - k := by
--             simp [List.length_drop]
--             rfl
--           have h_calc : N - k = m + 1 := by omega
--           rw [h_drop_k_len, h_calc] at h_cons_len
--           simp [List.length_cons] at h_cons_len
--           omega

--         have h_tl_eq : tl₁ = tl₂ := by
--           apply List.ext_getElem h_tl_len
--           intro j _ _
--           have h_j_lt_m : j < m := by omega
--           have h_idx_eq : N - 1 - (m - 1 - j) = k + 1 + j := by omega -- for some reason omega doesn't work here

--           -- Now use h_agree to show equality
--           have h1 : tl₁[j] = d₁[k + 1 + j]'(by omega : k + 1 + j < N) := by
--             have h_bound : j + 1 < (hd₁ :: tl₁).length := by
--               simp [List.length_cons, h_tl₁_len]
--               omega
--             have : tl₁[j] = (hd₁ :: tl₁)[j + 1]'h_bound := by
--               simp [List.getElem_cons_succ]
--             rw [this]
--             have h_drop_bound : j + 1 < (d₁.drop k).length := by rw [heq₁]; exact h_bound
--             have : (hd₁ :: tl₁)[j + 1]'h_bound = (d₁.drop k)[j + 1]'h_drop_bound := by
--               congr 1
--               exact heq₁.symm
--             rw [this]
--             rw [List.getElem_drop]
--             congr 1
--             omega
--           have h2 : tl₂[j] = d₂[k + 1 + j]'(by omega : k + 1 + j < d₂.length) := by
--             have h_bound : j + 1 < (hd₂ :: tl₂).length := by
--               simp [List.length_cons, h_tl_len, h_tl₁_len]
--               omega
--             have : tl₂[j] = (hd₂ :: tl₂)[j + 1]'h_bound := by
--               simp [List.getElem_cons_succ]
--             rw [this]
--             have h_drop_bound : j + 1 < (d₂.drop k).length := by rw [heq₂]; exact h_bound
--             have : (hd₂ :: tl₂)[j + 1]'h_bound = (d₂.drop k)[j + 1]'h_drop_bound := by
--               congr 1
--               exact heq₂.symm
--             rw [this]
--             rw [List.getElem_drop]
--             congr 1
--             omega
--           rw [h1, h2]
--           have : d₁[k + 1 + j]'(by omega) = d₁[N - 1 - (m - 1 - j)]'(by omega) := by
--             congr 1; exact h_idx_eq.symm
--           rw [this]
--           have : d₂[k + 1 + j]'(by omega : k + 1 + j < d₂.length) = d₂[N - 1 - (m - 1 - j)]'(by omega) := by
--             congr 1; exact h_idx_eq.symm
--           rw [this]
--           exact h_agree (m - 1 - j) (by omega) (by omega) (by omega)
--         rw [h_tl_eq]


--     -- Now use composeFromRadix_cons
--     calc composeFromRadix r (d₁.drop k)
--         = composeFromRadix r (hd₁ :: tl₁) := by rw [← heq₁]
--       _ = composeFromRadix r tl₁ * r + hd₁ := composeFromRadix_cons r tl₁
--       _ = composeFromRadix r tl₂ * r + hd₁ := by rw [h_tails_eq]
--       _ = composeFromRadix r tl₂ * r + d₁[k] := by rw [h_hd₁]
--       _ > composeFromRadix r tl₂ * r + d₂[k] := by
--             have : d₁[k] > d₂[k] := h_diff
--             omega
--       _ = composeFromRadix r tl₂ * r + hd₂ := by rw [← h_hd₂]
--       _ = composeFromRadix r (hd₂ :: tl₂) := by rw [composeFromRadix_cons]
--       _ = composeFromRadix r (d₂.drop k) := by rw [heq₂]

--   have h_rk_pos : r ^ k > 0 := Nat.pow_pos (by omega : 0 < r)
--   have h_mul_gt : r ^ k * composeFromRadix r (d₁.drop k) > r ^ k * composeFromRadix r (d₂.drop k) := by
--     exact Nat.mul_lt_mul_of_pos_left h_high_gt h_rk_pos

--   have h_diff_bound : r ^ k * composeFromRadix r (d₁.drop k) ≥ r ^ k * composeFromRadix r (d₂.drop k) + r ^ k := by
--     have : composeFromRadix r (d₁.drop k) ≥ composeFromRadix r (d₂.drop k) + 1 := h_high_gt
--     calc r ^ k * composeFromRadix r (d₁.drop k)
--       _ ≥ r ^ k * (composeFromRadix r (d₂.drop k) + 1) := by
--             apply Nat.mul_le_mul_left
--             omega
--       _ = r ^ k * composeFromRadix r (d₂.drop k) + r ^ k := by ring

--   calc composeFromRadix r (d₁.take k) + r ^ k * composeFromRadix r (d₁.drop k)
--       ≥ r ^ k * composeFromRadix r (d₁.drop k) := by omega
--     _ ≥ r ^ k * composeFromRadix r (d₂.drop k) + r ^ k := h_diff_bound
--     _ > composeFromRadix r (d₂.take k) + r ^ k * composeFromRadix r (d₂.drop k) := by omega

end Lampe
