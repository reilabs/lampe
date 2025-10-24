import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic

namespace Lampe

/-- Extends the given list `a` up to length `len` with the default value of `α` -/
def extList (lst : List α) (len : Nat) (default : α) : List α
  := lst ++ (List.replicate (len - lst.length) default)

@[reducible]
def decomposeToRadix (r : Nat) (v : Nat) (h : r > 1) : List Nat := match v with
| .zero => List.nil
| v' + 1 => List.cons ((v' + 1) % r) (decomposeToRadix r ((v' + 1) / r) h)
decreasing_by
  rw [Nat.succ_eq_add_one, Nat.div_lt_iff_lt_mul]
  rw [Nat.lt_mul_iff_one_lt_right]
  tauto
  exact Nat.succ_pos v'
  rw [<-Nat.ne_zero_iff_zero_lt]
  aesop

example : decomposeToRadix 10 123 (by linarith) = [3, 2, 1] := by rfl
example : decomposeToRadix 2 123 (by linarith) = [1, 1, 0, 1, 1, 1, 1] := by rfl

def composeFromRadix (r : Nat) (l : List Nat) : Nat := (l.reverse.foldl (fun acc d => acc * r + d) 0)

example : (composeFromRadix 10 [3, 2, 1]) = 123 := by rfl
example : (composeFromRadix 2 [1, 1, 0, 1, 1, 1, 1]) = 123 := by rfl

theorem decomposeToRadix_2_eq_bits (n : Nat) :
    decomposeToRadix 2 n (by decide) = n.bits.map (fun b => if b then 1 else 0) := by
  induction n using Nat.binaryRec with
  | z =>
    rw [Nat.zero_bits]
    rfl
  | f b n h =>
    cases b with
    | false =>
      rw [Nat.bit_false]
      match n with
      | .zero => unfold decomposeToRadix; simp
      | n@(k + 1) =>
        rename n = _ => n_def
        simp_all
        rw [← n_def]
        rw [← n_def] at h
        unfold decomposeToRadix
        have : ∃l, 2 * n = Nat.succ l := by
          simp [n_def]
        have ⟨l, hl⟩ := this
        simp [hl]
        refine ⟨?_, ?_⟩
        simp at hl
        simp [←hl]
        simp at hl
        rw [←hl]
        simp [h]
    | true =>
      simp
      unfold decomposeToRadix
      simp only [Nat.mul_add_mod_self_left, Nat.mod_succ, List.cons.injEq, true_and]
      rcases n.even_or_odd' with ⟨k, rfl | rfl⟩
      · conv in (2 * (2 * k) + 1) / 2 =>
        equals 2 * k =>
          grind
        assumption
      · conv in (2 * (2 * k + 1) + 1) / 2 =>
        equals 2 * k + 1 =>
          grind
        assumption

theorem decomposeToRadix_zero (r : Nat) (h : r > 1) :
    decomposeToRadix r 0 h = [] := by
  rfl

theorem composeFromRadix_nil (r : Nat) :
    composeFromRadix r [] = 0 := by
  rfl

theorem decomposeToRadix_in_fin (r v : Nat) (h : r > 1) :
    ∀ {k}, k ∈ decomposeToRadix r v h → k < r := by
  revert h
  refine Nat.strong_induction_on v ?_
  intro v ih h k hk
  cases v with
  | zero =>
    rw [decomposeToRadix_zero] at hk
    simp_all only [gt_iff_lt, not_lt_zero', not_isEmpty_of_nonempty, IsEmpty.forall_iff, imp_self, implies_true,
      List.not_mem_nil]
  | succ v =>
    have hrpos : 0 < r := lt_trans Nat.zero_lt_one h
    simp [decomposeToRadix, Nat.succ_eq_add_one] at hk ⊢
    rcases hk with hk | hk
    · exact Nat.mod_lt _ hrpos
    · have hlt : (v + 1) / r < v + 1 := Nat.div_lt_self (Nat.succ_pos _) h
      apply ih <;> assumption

theorem composeFromRadix_cons (r : Nat) (l : List Nat) :
    composeFromRadix r (a :: l) = composeFromRadix r l * r + a := by
  unfold composeFromRadix
  simp only [List.reverse_cons, List.foldl_append, List.foldl, List.foldl_reverse,
    Nat.add_left_cancel_iff]

theorem composeFromRadix_decomposeToRadix_id (r v : Nat) (h : r > 1) :
    composeFromRadix r (decomposeToRadix r v h) = v := by
  revert h
  refine Nat.strong_induction_on v ?_
  intro v ih h
  cases v with
  | zero =>
    rw [decomposeToRadix_zero, composeFromRadix_nil]
  | succ v =>
    have hstepSucc : decomposeToRadix r (Nat.succ v) h = ((Nat.succ v) % r) :: decomposeToRadix r ((Nat.succ v) / r) h := rfl
    have hstep : decomposeToRadix r (v + 1) h = ((v + 1) % r) :: decomposeToRadix r ((v + 1) / r) h := by simpa [Nat.succ_eq_add_one] using hstepSucc
    have hlt : (v + 1) / r < v + 1 := Nat.div_lt_self (Nat.succ_pos _) h
    have ih' : composeFromRadix r (decomposeToRadix r ((v + 1) / r) h) = (v + 1) / r := ih ((v + 1) / r) hlt h
    calc
      composeFromRadix r (decomposeToRadix r (v + 1) h)
          = composeFromRadix r (((v + 1) % r) :: decomposeToRadix r ((v + 1) / r) h) := by
            simp [hstep]
        _ = composeFromRadix r (decomposeToRadix r ((v + 1) / r) h) * r + ((v + 1) % r) := by
            simp [composeFromRadix_cons]
        _ = ((v + 1) / r) * r + ((v + 1) % r) := by
            simp [ih']
        _ = v + 1 := by
            have := Nat.mod_add_div (v + 1) r
            simpa [Nat.add_comm, Nat.mul_comm] using this

theorem composeFromRadix_mono_forall₂_le (r : Nat) :
    ∀ {x y : List Nat}, List.Forall₂ (fun a b => a ≤ b) x y →
      composeFromRadix r x ≤ composeFromRadix r y := by
  intro x y hxy
  induction hxy with
  | nil =>
      simp [composeFromRadix_nil]
  | @cons a b xs ys hab hrest ih =>
      have hmul : composeFromRadix r xs * r ≤ composeFromRadix r ys * r :=
        Nat.mul_le_mul_right _ ih
      have hadd : composeFromRadix r xs * r + a ≤ composeFromRadix r ys * r + b :=
        Nat.add_le_add hmul hab
      simpa [composeFromRadix_cons] using hadd

theorem decomposeToRadix_length_lower_bound (r v : Nat) (h : 1 < r) :
    (decomposeToRadix r v h).length > 0 → v ≥ r ^ ((decomposeToRadix r v h).length - 1) := by
  intro h_len_pos
  revert h h_len_pos
  refine Nat.strong_induction_on v ?_
  intro v ih h h_len_pos
  cases v with
  | zero =>
    rw [decomposeToRadix_zero] at h_len_pos
    simp at h_len_pos
  | succ v =>
    have h_rec : decomposeToRadix r (v + 1) h = ((v + 1) % r) :: decomposeToRadix r ((v + 1) / r) h := rfl
    rw [h_rec] at h_len_pos ⊢
    simp only [List.length_cons] at h_len_pos ⊢
    cases Nat.eq_zero_or_pos (decomposeToRadix r ((v + 1) / r) h).length with
    | inl h_zero =>
      rw [h_zero]
      simp
    | inr h_pos =>
      have h_div_lt : (v + 1) / r < v + 1 := Nat.div_lt_self (Nat.succ_pos _) h
      have ih_div := ih ((v + 1) / r) h_div_lt h h_pos
      calc v + 1
          = r * ((v + 1) / r) + ((v + 1) % r) := (Nat.div_add_mod (v + 1) r).symm
        _ ≥ r * ((v + 1) / r) + 0 := by
              exact Nat.add_le_add_left (Nat.zero_le _) _
        _ = r * ((v + 1) / r) := by
              simp
        _ ≥ r * r ^ ((decomposeToRadix r ((v + 1) / r) h).length - 1) := by
              exact Nat.mul_le_mul_left r ih_div
        _ = r ^ (1 + ((decomposeToRadix r ((v + 1) / r) h).length - 1)) := by
              rw [Nat.pow_add, Nat.pow_one]
        _ = r ^ (decomposeToRadix r ((v + 1) / r) h).length := by
              have : 1 + ((decomposeToRadix r ((v + 1) / r) h).length - 1) = (decomposeToRadix r ((v + 1) / r) h).length := by
                omega
              rw [this]
        _ = r ^ ((decomposeToRadix r ((v + 1) / r) h).length + 1 - 1) := by
              simp [Nat.add_sub_cancel]

theorem decomposeToRadix_length_upper_bound (r v : Nat) (h : 1 < r) :
    v < r ^ (decomposeToRadix r v h).length := by
  revert h
  refine Nat.strong_induction_on v ?_
  intro v ih h
  cases v with
  | zero =>
    rw [decomposeToRadix_zero]
    simp only [List.length_nil, Nat.pow_zero]
    omega
  | succ v =>
    have h_rec : decomposeToRadix r (v + 1) h = ((v + 1) % r) :: decomposeToRadix r ((v + 1) / r) h := rfl
    rw [h_rec]
    simp only [List.length_cons]
    have h_div_lt : (v + 1) / r < v + 1 := Nat.div_lt_self (Nat.succ_pos _) h
    have ih_div := ih ((v + 1) / r) h_div_lt h
    have h_mod : (v + 1) % r < r := Nat.mod_lt _ (Nat.zero_lt_of_lt h)
    have h_div_le : (v + 1) / r + 1 ≤ r ^ (decomposeToRadix r ((v + 1) / r) h).length := by
      omega
    calc v + 1
        = r * ((v + 1) / r) + ((v + 1) % r) := (Nat.div_add_mod (v + 1) r).symm
      _ ≤ r * ((v + 1) / r) + (r - 1) := by
            apply Nat.add_le_add_left
            omega
      _ = r * ((v + 1) / r + 1) - 1 := by
            have hr_pos : r ≥ 2 := h
            have : r - 1 ≥ 1 := by omega
            have calc1 : r * ((v + 1) / r) + (r - 1) = r * ((v + 1) / r) + r - 1 := by omega
            have calc2 : r * ((v + 1) / r) + r = r * ((v + 1) / r + 1) := by ring
            rw [calc1, calc2]
      _ ≤ r * r ^ (decomposeToRadix r ((v + 1) / r) h).length - 1 := by
            have : r * ((v + 1) / r + 1) ≤ r * r ^ (decomposeToRadix r ((v + 1) / r) h).length := by
              exact Nat.mul_le_mul_left r h_div_le
            omega
      _ < r * r ^ (decomposeToRadix r ((v + 1) / r) h).length := by
            have : 0 < r * r ^ (decomposeToRadix r ((v + 1) / r) h).length := by
              apply Nat.mul_pos
              · omega
              · apply Nat.pow_pos
                omega
            omega
      _ = r ^ ((decomposeToRadix r ((v + 1) / r) h).length + 1) := by
            rw [Nat.pow_succ, Nat.mul_comm]

theorem decomposeToRadix_le_mono_len (r v₁ v₂ : Nat) (h : 1 < r)
    (h_len : (decomposeToRadix r v₁ h).length < (decomposeToRadix r v₂ h).length) : v₁ < v₂ := by
  have h_v₁_bound := decomposeToRadix_length_upper_bound r v₁ h
  cases Nat.eq_zero_or_pos (decomposeToRadix r v₂ h).length with
  | inl h_zero =>
    rw [h_zero] at h_len
    simp at h_len
  | inr h_pos =>
    have h_v₂_bound := decomposeToRadix_length_lower_bound r v₂ h h_pos
    calc v₁
        < r ^ (decomposeToRadix r v₁ h).length := h_v₁_bound
      _ ≤ r ^ ((decomposeToRadix r v₂ h).length - 1) := by
            apply Nat.pow_le_pow_right
            · omega
            · omega
      _ ≤ v₂ := h_v₂_bound

theorem decomposeToRadix_le_mono (r v₁ v₂ : Nat) (h : r > 1) (h_le : v₁ ≤ v₂) :
    (decomposeToRadix r v₁ h).length ≤ (decomposeToRadix r v₂ h).length := by
  by_contra h_not_le
  push_neg at h_not_le
  have h_v₂_lt_v₁ : v₂ < v₁ := decomposeToRadix_le_mono_len r v₂ v₁ h h_not_le
  omega

theorem composeFromRadix_upper_bound (r : Nat) (l : List Nat) (h_all : ∀ d ∈ l, d < r) :
    composeFromRadix r l < r ^ l.length := by
  induction l with
  | nil => simp [composeFromRadix_nil]
  | cons hd tl ih =>
    rw [composeFromRadix_cons]
    have hd_bound : hd < r := h_all hd (by simp)
    have tl_all : ∀ d ∈ tl, d < r := by
      intros d hd_in
      exact h_all d (by simp [hd_in])
    simp only [List.length_cons]
    rw [pow_succ]
    by_cases h_tl_empty : tl = []
    · simp [h_tl_empty, composeFromRadix_nil]
      omega
    · have ih' : composeFromRadix r tl < r ^ tl.length := ih tl_all
      have h1 : composeFromRadix r tl + 1 ≤ r ^ tl.length := by omega
      calc composeFromRadix r tl * r + hd
          < composeFromRadix r tl * r + r := by omega
        _ = (composeFromRadix r tl + 1) * r := by ring
        _ ≤ r ^ tl.length * r := by
            exact Nat.mul_le_mul_right r h1

theorem composeFromRadix_lower_bound (r : Nat) (l : List Nat) (h_ne : l ≠ [])
    (h_all : ∀ d ∈ l, d < r) (_hr : r > 1)
    (h_no_trail : l.getLast h_ne ≠ 0) :
    r ^ (l.length - 1) ≤ composeFromRadix r l := by
  induction l with
  | nil =>
    simp at h_ne
  | cons hd tl ih =>
    rw [composeFromRadix_cons]
    cases tl with
    | nil =>
      have h_hd_nonzero : hd ≠ 0 := by
        simp [List.getLast] at h_no_trail
        exact h_no_trail
      simp [composeFromRadix_nil, List.length_cons]
      omega
    | cons hd2 tl2 =>
      simp only [List.length_cons, Nat.add_sub_cancel]
      have h_all_tl : ∀ d ∈ hd2 :: tl2, d < r := by
        intros d hd_in
        exact h_all d (by simp [hd_in])
      have h_ne_tl : hd2 :: tl2 ≠ [] := by simp
      have h_no_trail_tl : (hd2 :: tl2).getLast h_ne_tl ≠ 0 := by
        have := h_no_trail
        simp [List.getLast_cons] at this ⊢
        exact this
      have ih_tl := ih h_ne_tl h_all_tl h_no_trail_tl
      simp only [List.length_cons] at ih_tl
      have : (tl2.length + 1 - 1) = tl2.length := by omega
      rw [this] at ih_tl
      rw [pow_succ, mul_comm]
      calc r * r ^ tl2.length
          ≤ r * composeFromRadix r (hd2 :: tl2) := by
              exact Nat.mul_le_mul_left r ih_tl
        _ = composeFromRadix r (hd2 :: tl2) * r := by ring
        _ ≤ composeFromRadix r (hd2 :: tl2) * r + hd := by omega

theorem composeFromRadix_le_mono_len (r : Nat) :
    ∀ {l₁ l₂ : List Nat}, l₁.length < l₂.length →
      (∀ d ∈ l₁, d < r) → (∀ d ∈ l₂, d < r) → r > 1 →
      (∀ h : l₂ ≠ [], l₂.getLast h ≠ 0) →
      composeFromRadix r l₁ < composeFromRadix r l₂ := by
  intro l₁ l₂ h_len h₁ h₂ hr h_no_trail
  have h_upper_l₁ : composeFromRadix r l₁ < r ^ l₁.length :=
    composeFromRadix_upper_bound r l₁ h₁

  have h_l₂_ne : l₂ ≠ [] := by
    intro h_eq
    simp [h_eq] at h_len

  have h_lower_l₂ : r ^ (l₂.length - 1) ≤ composeFromRadix r l₂ :=
    composeFromRadix_lower_bound r l₂ h_l₂_ne h₂ hr (h_no_trail h_l₂_ne)

  have h_pow : r ^ l₁.length ≤ r ^ (l₂.length - 1) := by
    have h_l₂_pos : 0 < l₂.length := by omega
    have : l₁.length ≤ l₂.length - 1 := by omega
    exact Nat.pow_le_pow_right (by omega : 1 ≤ r) this

  calc composeFromRadix r l₁
      < r ^ l₁.length := h_upper_l₁
    _ ≤ r ^ (l₂.length - 1) := h_pow
    _ ≤ composeFromRadix r l₂ := h_lower_l₂

end Lampe
