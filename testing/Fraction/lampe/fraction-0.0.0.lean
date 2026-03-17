import «fraction-0.0.0».Extracted

open Lampe

set_option linter.unusedVariables false

/-
  signChangeFraction: flips the sign bit, leaves num/den unchanged.
-/
theorem signChangeFraction_spec {p} (s : Bool) (n d : U 32) :
    STHoare p «fraction-0.0.0».env ⟦⟧
      («fraction-0.0.0::signChangeFraction».call h![] h![(s, n, d, ())])
      (fun out => out = (!s, n, d, ())) := by
  enter_decl
  steps
  subst_vars; rfl

/-
  Applying signChangeFraction twice restores the original fraction.
-/
theorem signChangeFraction_involution {p} (s : Bool) (n d : U 32) :
    STHoare p «fraction-0.0.0».env ⟦⟧
      («fraction-0.0.0::signChangeFraction».call h![] h![(!s, n, d, ())])
      (fun out => out = (s, n, d, ())) := by
  have h := @signChangeFraction_spec p (!s) n d
  simp only [Bool.not_not] at h
  exact h

/-
  invertFraction: swaps num and den.
  pre: num ≠ 0
-/
theorem invertFraction_spec {p} (s : Bool) (n d : U 32) (hn : n ≠ 0) :
    STHoare p «fraction-0.0.0».env ⟦⟧
      («fraction-0.0.0::invertFraction».call h![] h![(s, n, d, ())])
      (fun out => out = (s, d, n, ())) := by
  enter_decl
  steps
  subst_vars; rfl

/-
  toFraction: constructor.
  pre: d ≠ 0
-/
theorem toFraction_spec {p} (s : Bool) (n d : U 32) (hd : d ≠ 0) :
    STHoare p «fraction-0.0.0».env ⟦⟧
      («fraction-0.0.0::toFraction».call h![] h![s, n, d])
      (fun out => out = (s, n, d, ())) := by
  enter_decl
  steps
  subst_vars; rfl

/-
  isInteger: returns true iff num = 0 or num % den = 0.
  Key: indexTpl is @[reducible], so `have : n = ↑0 := hcond` works after converting
  `decide (indexTpl ... = ↑0) = true/false` via decide_eq_true_eq/decide_eq_false_iff_not.
-/
theorem isInteger_spec {p} (s : Bool) (n d : U 32) :
    STHoare p «fraction-0.0.0».env ⟦⟧
      («fraction-0.0.0::isInteger».call h![] h![(s, n, d, ())])
      (fun out => out = (n == 0 || n % d == 0)) := by
  enter_decl
  steps
  apply STHoare.ite_intro <;> intro hcond
  · steps
    rw [decide_eq_true_eq] at hcond
    have hn : n = ↑0 := hcond
    simp_all [beq_iff_eq]
  · steps
    apply STHoare.ite_intro <;> intro hcond2
    · steps
      rw [decide_eq_false_iff_not] at hcond
      rw [decide_eq_true_eq] at hcond2
      have hn : n ≠ ↑0 := hcond
      have hnd : n % d = ↑0 := hcond2
      simp_all [beq_iff_eq]
    · steps
      rw [decide_eq_false_iff_not] at hcond hcond2
      have hn : n ≠ ↑0 := hcond
      have hnd : n % d ≠ ↑0 := hcond2
      simp_all [← beq_eq_false_iff_ne]

/-
  isNotInteger: returns true iff num ≠ 0 and num % den ≠ 0.
-/
theorem isNotInteger_spec {p} (s : Bool) (n d : U 32) :
    STHoare p «fraction-0.0.0».env ⟦⟧
      («fraction-0.0.0::isNotInteger».call h![] h![(s, n, d, ())])
      (fun out => out = (n != 0 && n % d != 0)) := by
  enter_decl
  steps
  apply STHoare.ite_intro <;> intro hcond
  · steps
    rw [decide_eq_true_eq] at hcond
    have hn : n = ↑0 := hcond
    simp_all [beq_iff_eq, bne_iff_ne]
  · steps
    apply STHoare.ite_intro <;> intro hcond2
    · steps
      rw [decide_eq_false_iff_not] at hcond
      rw [decide_eq_true_eq] at hcond2
      have hn : n ≠ ↑0 := hcond
      have hnd : n % d = ↑0 := hcond2
      simp_all [beq_iff_eq, bne_iff_ne]
    · steps
      rw [decide_eq_false_iff_not] at hcond hcond2
      have hn : n ≠ ↑0 := hcond
      have hnd : n % d ≠ ↑0 := hcond2
      simp_all [← bne_iff_ne]
