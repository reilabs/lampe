import Mathlib.Data.Vector.Snoc
import Mathlib.Tactic

def List.chunksExact {n α} d (l : List α) (h : List.length l = n * d) : List (List α) :=
  match n with
  | 0 => []
  | n + 1 =>
    l.take d :: List.chunksExact (n := n) d (l.drop d) (by simp [h, Nat.succ_mul])

@[simp]
lemma List.chunksExact_length {h : List.length l = k * d} :
    (List.chunksExact d l h).length = k := by
  induction k generalizing l with
  | zero => simp [chunksExact]
  | succ k ih =>
    simp [chunksExact, ih]

lemma List.getElem_chunksExact {l : List α} {h : l.length = k * d} {hi} :
    (List.chunksExact d l h)[i]'hi =
      List.ofFn fun (j : Fin d) =>
        l[d * i + j.val]'(by
          simp [h]
          simp at hi
          cases j
          simp
          apply lt_of_lt_of_le (Nat.add_lt_add_left (by assumption) _)
          rw [←Nat.mul_succ, mul_comm]
          apply Nat.mul_le_mul_right
          linarith) := by
  simp at hi
  induction i generalizing l k with
  | zero =>
    have : k = k - 1 + 1 := by omega
    unfold chunksExact
    split
    · contradiction
    · apply List.ext_get
      · simp
        rename l.length = (_ + 1) * d => hl
        rw [hl]
        simp [Nat.succ_mul]
      · intro n _ _
        simp
  | succ n ih =>
    unfold chunksExact
    split
    · contradiction
    · simp
      rw [ih]
      simp [Nat.mul_succ]
      ext
      congr 1
      ring
      linarith

theorem List.Vector.reverse_map {α β : Type} {d : ℕ} (v : List.Vector α d) (f : α → β) :
    (v.map f).reverse = v.reverse.map f := by
  apply List.Vector.eq
  simp [List.Vector.toList_reverse]

namespace Lampe

abbrev Radix : Type := { n : Nat // n > 1 }

abbrev Digit (r : Radix) := Fin r.1
abbrev RadixVec (r : Radix) (d : Nat) := Fin (r ^ d)

abbrev R256 : Radix := ⟨256, by decide⟩

namespace RadixVec

variable {r : Radix} {d : Nat}

def of (r : Radix) (v : Nat) : RadixVec r (Nat.log r.val v + 1) :=
  ⟨v, Nat.lt_pow_succ_log_self r.prop _⟩

def msd (v : RadixVec r (d + 1)) : Digit r :=
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
      have : v.val ≥ (v.val - v.val % r ^ d) := by apply Nat.sub_le
      zify [*]
      ring_nf
      convert Int.emod_lt _ _ using 1
      · simp
      · have : r.val ≠ 0 := by
          intro hp
          have := r.prop
          linarith
        simp [*])

theorem msd_lsds_decomposition {v : RadixVec r (d + 1)} :
    v =
      ⟨v.msd.val * r ^ d + v.lsds.val, by
        simp only [msd, lsds]
        rw [Nat.div_mul_self_eq_mod_sub_self]
        have := Nat.mod_le v (r ^ d)
        have : v.val ≥ (v.val - v.val % r ^ d) := by apply Nat.sub_le
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
  have : v.val ≥ (v - v % r ^ d) := by apply Nat.sub_le
  zify [*]
  simp

theorem msd_lsds_decomposition_unique {v : RadixVec r (d + 1)}
    {msd' : Digit r} {lsds' : RadixVec r d} {h} :
    v = ⟨msd'.val * r ^ d + lsds'.val, h⟩ ↔ msd' = v.msd ∧ lsds' = v.lsds := by
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

def toDigitsBE {d} (v : RadixVec r d) : List.Vector (Digit r) d :=
  match d with
  | 0 => List.Vector.nil
  | _ + 1 => v.msd ::ᵥ toDigitsBE v.lsds

def toDigitsLE {d} (v : RadixVec r d) : List.Vector (Digit r) d :=
  (toDigitsBE v).reverse

abbrev toBaseLE {d} (v : RadixVec r d) : List.Vector (Digit r) d :=
  toDigitsLE v

theorem toBaseLE_elem_lt {d} {v : RadixVec r d} {i : Fin d} :
    (toBaseLE (r := r) v).get i < r.val :=
  (toBaseLE v).get i |>.prop

def ofLimbsBE {d} (r : Nat) (v : List.Vector ℕ d) : ℕ :=
  match d with
  | 0 => 0
  | d + 1 => v.head * r ^ d + ofLimbsBE r v.tail

def ofLimbsBE' (r : Nat) (l : List ℕ) : ℕ :=
  ofLimbsBE r ⟨l, rfl⟩

def ofLimbsLE {d} (r : Nat) (v : List.Vector ℕ d) : ℕ :=
  ofLimbsBE r v.reverse

def ofLimbsLE' (r : Nat) (l : List ℕ) : ℕ :=
  ofLimbsBE' r l.reverse

@[simp]
theorem ofLimbsBE'_nil (r : Nat) : ofLimbsBE' r [] = 0 := by
  rfl

@[simp]
theorem ofLimbsBE'_cons (r : Nat) (x : Nat) (xs : List Nat) :
    ofLimbsBE' r (x :: xs) = x * r ^ xs.length + ofLimbsBE' r xs := by
  rfl

theorem ofLimbsBE'_append (r : Nat) (xs ys : List Nat) :
    ofLimbsBE' r (xs ++ ys) = ofLimbsBE' r xs * r ^ ys.length + ofLimbsBE' r ys := by
  induction xs with
  | nil => simp
  | cons _ _ ih =>
    simp only [List.cons_append, ofLimbsBE'_cons, List.length_append, ih, Nat.pow_add, Nat.add_mul]
    linarith

theorem ofLimbsLE'_append (r : Nat) (xs ys : List Nat) :
    ofLimbsLE' r (xs ++ ys) = ofLimbsLE' r xs + r ^ xs.length * ofLimbsLE' r ys := by
  simp [ofLimbsLE', List.reverse_append, ofLimbsBE'_append, add_comm, add_left_comm, mul_comm]

def ofDigitsBE {d} {r : Radix} (v : List.Vector (Digit r) d) : RadixVec r d :=
  ⟨ofLimbsBE r.val (v.map (fun d => d.val)), by
    induction d with
    | zero => simp [ofLimbsBE]
    | succ d ih =>
      simp only [ofLimbsBE, List.Vector.head_map, List.Vector.tail_map]
      calc
        _ < v.head.val * r.val ^ d + r.val ^ d := by
          have := ih v.tail
          linarith
        _ = (v.head.val + 1) * r.val ^ d := by linarith
        _ ≤ r * r.val ^ d := by
          have := Nat.succ_le_of_lt v.head.prop
          apply Nat.mul_le_mul_right
          assumption
        _ = _ := by simp [Nat.pow_succ, Nat.mul_comm]
  ⟩

def ofDigitsLE {d} {r : Radix} (v : List.Vector (Digit r) d) : RadixVec r d :=
  ofDigitsBE v.reverse

abbrev ofBaseLE {d} {r : Radix} (v : List.Vector (Digit r) d) : RadixVec r d :=
  ofDigitsLE v

def ofDigitsBE' (l : List (Digit r)) : Nat :=
  (RadixVec.ofDigitsBE ⟨l, rfl⟩).val

def ofDigitsLE' (l : List (Digit r)) : Nat :=
  ofDigitsBE' l.reverse

def toBaseLENat' (r : Radix) (n : Nat) (v : Nat) : List.Vector (Digit r) n :=
  let rv : RadixVec r n := ⟨v % (r.val ^ n),
    Nat.mod_lt _ (Nat.pow_pos (Nat.lt_of_succ_le (Nat.one_le_of_lt r.prop)))⟩
  RadixVec.toDigitsLE rv

def ofBaseLENat' {r : Radix} {n : Nat} (v : List.Vector (Digit r) n) : Nat :=
  (RadixVec.ofDigitsLE v).val

@[simp]
theorem ofDigitsBE'_nil : ofDigitsBE' (r := r) [] = 0 := by
  rfl

@[simp]
theorem ofDigitsBE'_cons :
    ofDigitsBE' (r := r) (x :: xs) = x * r ^ xs.length + ofDigitsBE' xs := by
  rfl

@[simp]
theorem ofDigitsBE'_append :
    ofDigitsBE' (r := r) (xs ++ ys) = ofDigitsBE' xs * r ^ ys.length + ofDigitsBE' ys := by
  induction xs with
  | nil => simp
  | cons _ _ ih =>
    simp only [
      List.cons_append, ofDigitsBE'_cons, List.length_append, ih, Nat.pow_add,
      Nat.add_mul
    ]
    linarith

theorem ofDigitsBE'_toList {r : Radix} {l : List.Vector (Digit r) d} :
    ofDigitsBE' l.toList = (ofDigitsBE l).val := by
  simp only [ofDigitsBE']
  congr <;> simp

theorem ofDigitsLE'_append :
    ofDigitsLE' (r := r) (xs ++ ys) = ofDigitsLE' xs + r ^ xs.length * ofDigitsLE' ys := by
  simp [ofDigitsLE', List.reverse_append, ofDigitsBE'_append, add_comm, add_left_comm, mul_comm]

def toDigitsBE' (r : Radix) (n : Nat) : List (Digit r) :=
  toDigitsBE ⟨n, Nat.lt_pow_succ_log_self r.prop _⟩ |>.toList

def toDigitsLE' (r : Radix) (n : Nat) : List (Digit r) :=
  (toDigitsBE' r n).reverse

instance : OfNat Radix 2 where
  ofNat := ⟨2, by simp⟩

lemma ofDigitsBE_cons {r : Radix} {d : Nat} {x : Digit r}
    {xs : List.Vector (Digit r) d} :
    ofDigitsBE (r := r) (x ::ᵥ xs) = (x.val * r.val ^ d + ofDigitsBE xs) := by
  rfl

@[simp]
theorem ofDigitsBE_cons' {r : Radix} {d : Nat} {x : Digit r}
    {xs : List.Vector (Digit r) d} :
    ofDigitsBE (r := r) (x ::ᵥ xs) =
      ⟨x.val * r.val ^ d + ofDigitsBE xs, by
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

theorem ofDigitsBE_lt {r : Radix} {d : Nat} {l : List.Vector (Digit r) d} :
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

theorem ofDigitsBE'_lt {r : Radix} {l : List (Digit r)} :
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

theorem ofDigitsBE_toDigitsBE {r : Radix} {n : RadixVec r d} :
    ofDigitsBE (toDigitsBE n) = n := by
  induction d with
  | zero =>
    cases' r with r hr
    cases' n with n hn
    have : n = 0 := by simp_all
    simp [toDigitsBE, ofDigitsBE, ofLimbsBE, this]
  | succ d ih =>
    conv_rhs => rw [msd_lsds_decomposition (v := n)]
    have := Fin.val_eq_of_eq $ ih (n := n.lsds)
    simpa [ofDigitsBE, toDigitsBE, ofLimbsBE]

theorem ofDigitsLE_toDigitsLE {r : Radix} {n : RadixVec r d} :
    ofDigitsLE (toDigitsLE n) = n := by
  simp [ofDigitsLE, toDigitsLE, ofDigitsBE_toDigitsBE, List.Vector.reverse_reverse]

theorem ofBaseLE_val_toBaseLE {r : Radix} {n : RadixVec r d} :
    (ofBaseLE (r := r) (toBaseLE n)).val = n.val := by
  simpa using congrArg Fin.val (ofDigitsLE_toDigitsLE (n := n))

theorem toDigitsBE_ofDigitsBE {r : Radix} {v : List.Vector (Digit r) d} :
    toDigitsBE (ofDigitsBE v) = v := by
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

theorem toDigitsLE_ofDigitsLE {r : Radix} {v : List.Vector (Digit r) d} :
    toDigitsLE (ofDigitsLE v) = v := by
  simp [toDigitsLE, ofDigitsLE, toDigitsBE_ofDigitsBE, List.Vector.reverse_reverse]

theorem ofDigitsBE'_toDigitsBE' {r : Radix} {n : Nat} :
    ofDigitsBE' (toDigitsBE' r n) = n := by
  simp [toDigitsBE']
  generalize_proofs hn
  have hval : (ofDigitsBE (toDigitsBE ⟨n, hn⟩)).val = n := by
    simpa using congrArg Fin.val (ofDigitsBE_toDigitsBE (n := ⟨n, hn⟩))
  have hlist := ofDigitsBE'_toList (l := toDigitsBE (r := r) (d := _) ⟨n, hn⟩)
  simpa [hlist] using hval

theorem ofDigitsLE'_toDigitsLE' {r : Radix} {n : Nat} :
    ofDigitsLE' (toDigitsLE' r n) = n := by
  simp [ofDigitsLE', toDigitsLE', ofDigitsBE'_toDigitsBE']

theorem ofBaseLENat'_toBaseLENat' {r : Radix} {n : Nat} {v : Nat} :
    ofBaseLENat' (toBaseLENat' r n v) = v % r.val ^ n := by
  simp [toBaseLENat', ofBaseLENat', ofDigitsLE_toDigitsLE]

theorem ofBaseLENat'_toBaseLENat'_of_lt {r : Radix} {n : Nat} {v : Nat}
    (hv : v < r.val ^ n) :
    ofBaseLENat' (toBaseLENat' r n v) = v := by
  rw [ofBaseLENat'_toBaseLENat']
  exact Nat.mod_eq_of_lt hv

theorem ofDigitsBE_mono {r : Radix} {l₁ l₂ : List.Vector (Digit r) d} :
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

theorem ofDigitsBE'_mono {r : Radix} {l₁ l₂ : List (Digit r)} :
    l₁.length = l₂.length → l₁ < l₂ → ofDigitsBE' l₁ < ofDigitsBE' l₂ := by
  intro hl hlt
  have := ofDigitsBE_mono (l₁ := ⟨l₁, hl⟩) (l₂ := ⟨l₂, rfl⟩) hlt
  rw [Fin.lt_def] at this
  simp only [ofDigitsBE']
  convert this

theorem ofDigitsBE'_subtype_eq {r : Radix} {l : List.Vector (Digit r) d}
    (hlt : ofDigitsBE' l.toList < r.val ^ d) :
    (⟨ofDigitsBE' l.toList, hlt⟩ : RadixVec r d) = ofDigitsBE l := by
  ext
  exact ofDigitsBE'_toList

end RadixVec

def toBaseLE (B n v : Nat) : List Nat :=
  match n with
  | 0 => []
  | n + 1 => v % B :: toBaseLE B n (v / B)

@[simp]
lemma toBaseLE_len : (toBaseLE B n v).length = n := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    simp [toBaseLE, ih]

theorem toBaseLE_succ_snoc :
    toBaseLE B (n + 1) v = toBaseLE B n v ++ [(v / B ^ n) % B] := by
  induction n generalizing v with
  | zero =>
    simp [toBaseLE]
  | succ n ih =>
    rw [toBaseLE, ih, toBaseLE]
    simp
    congr 1
    simp [Nat.pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]

theorem toBaseLE_take : (toBaseLE B n v).take m = toBaseLE B (min m n) v := by
  induction m generalizing v n with
  | zero =>
    simp [Nat.zero_min, toBaseLE]
  | succ m ih =>
    cases n
    · simp [toBaseLE]
    · simp [toBaseLE, Nat.succ_min_succ, ih]

theorem toBaseLE_drop : (toBaseLE B n v).drop m = toBaseLE B (n - m) (v / B ^ m) := by
  by_cases h : m ≤ n
  · have : n = m + (n - m) := by simp [h]
    rw [this]
    generalize n - m = d
    clear this h n
    rw [add_comm]
    induction m generalizing v with
    | zero =>
      simp
    | succ m ih =>
      rw [←add_assoc]
      simp at ih
      simp [toBaseLE, ih, Nat.pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]
  · have t₁ : n - m = 0 := by
      rw [Nat.sub_eq_zero_of_le]
      linarith
    simp [t₁, toBaseLE]
    linarith

def ofBaseLE (B : Nat) (v : List Nat) : Nat :=
  v.foldr (fun bit rest => bit + B * rest) 0

theorem ofBaseLE_toBaseLE : ofBaseLE B (toBaseLE B D N) = N % B ^ D := by
  induction D generalizing N with
  | zero => simp [Nat.mod_one, toBaseLE, ofBaseLE]
  | succ D ih =>
    simp [ofBaseLE] at ih
    simp [toBaseLE, ofBaseLE]
    rw [ih, add_comm, Nat.pow_succ]
    conv => rhs; rw [mul_comm, Nat.mod_mul, add_comm]

theorem ofBaseLE_toBaseLE_of_lt (h : N < B ^ D) : ofBaseLE B (toBaseLE B D N) = N := by
  rw [ofBaseLE_toBaseLE, Nat.mod_eq_of_lt h]

theorem toBaseLE_pow {B D K N} :
    toBaseLE (B ^ D) K N =
      (toBaseLE B (K * D) N |>.chunksExact D (by simp; exact Or.inl rfl) |>.map (ofBaseLE B)) := by
  induction K generalizing N with
  | zero =>
    simp [toBaseLE, List.chunksExact]
  | succ K ih =>
    simp only [toBaseLE, ih, List.Vector.map_cons, Nat.succ_mul]
    congr 1
    · simp [toBaseLE_take, ofBaseLE_toBaseLE]
    · congr
      simp [toBaseLE_drop]

lemma toBaseLE_elem_lt {B n i j : Nat} [hnz : NeZero B] {h} :
    (toBaseLE B n i)[j]'h < B := by
  induction n generalizing i j with
  | zero =>
    simp [toBaseLE]
    contradiction
  | succ n ih =>
    simp [toBaseLE]
    cases j
    · simp
      apply Nat.mod_lt
      apply Nat.zero_lt_of_ne_zero
      exact hnz.ne
    · simp [ih]

lemma ofBaseLE_append :
    ofBaseLE B (a ++ b) = ofBaseLE B a + B ^ a.length * ofBaseLE B b := by
  induction a with
  | nil => simp [ofBaseLE]
  | cons h t ih =>
    simp only [ofBaseLE] at ih
    simp only [
      ofBaseLE, List.map, List.cons_append, List.foldr_cons, ih, List.length_cons, pow_succ
    ]
    ring

end Lampe
