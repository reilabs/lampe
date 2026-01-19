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

end Lampe
