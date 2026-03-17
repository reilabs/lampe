
import «complexnr-0.0.0».Extracted

open Lampe

set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxRecDepth 4096

namespace «complexnr-0.0.0»

-- Lean-side type alias for Complex values: (real, imaginary, ())
private abbrev C (p : Prime) := Tp.denote p («complexnr-0.0.0::Complex».tp h![])

/-
  add(a, b): component-wise addition
  result.real = a.real + b.real
  result.imaginary = a.imaginary + b.imaginary
-/
theorem add_spec {p} (a b : C p) :
    STHoare p env ⟦⟧
      («complexnr-0.0.0::add».call h![] h![a, b])
      (fun r : C p => r.1 = a.1 + b.1 ∧ r.2.1 = a.2.1 + b.2.1) := by
  enter_decl
  steps
  subst_vars
  simp only [HList.toTuple]
  constructor <;> rfl

/-
  subtract(a, b): component-wise subtraction
  result.real = a.real - b.real
  result.imaginary = a.imaginary - b.imaginary
-/
theorem subtract_spec {p} (a b : C p) :
    STHoare p env ⟦⟧
      («complexnr-0.0.0::subtract».call h![] h![a, b])
      (fun r : C p => r.1 = a.1 - b.1 ∧ r.2.1 = a.2.1 - b.2.1) := by
  enter_decl
  steps
  subst_vars
  simp only [HList.toTuple]
  constructor <;> rfl

/-
  multiply(a, b): standard complex multiplication
  result.real = a.real * b.real - a.imaginary * b.imaginary
  result.imaginary = a.real * b.imaginary + a.imaginary * b.real
-/
theorem multiply_spec {p} (a b : C p) :
    STHoare p env ⟦⟧
      («complexnr-0.0.0::multiply».call h![] h![a, b])
      (fun r : C p =>
        r.1 = a.1 * b.1 - a.2.1 * b.2.1 ∧
        r.2.1 = a.1 * b.2.1 + a.2.1 * b.1) := by
  enter_decl
  steps
  subst_vars
  simp only [HList.toTuple]
  constructor <;> rfl

/-
  divide(a, b): division by conjugate normalization
  denominator = b.real² + b.imaginary²
  result.real = (a.real * b.real + a.imaginary * b.imaginary) / denominator
  result.imaginary = (a.imaginary * b.real - a.real * b.imaginary) / denominator
  Note: when denominator = 0 (i.e., b = 0), field division gives 0 by convention.
-/
theorem divide_spec {p} (a b : C p) :
    let denom := b.1 * b.1 + b.2.1 * b.2.1
    STHoare p env ⟦⟧
      («complexnr-0.0.0::divide».call h![] h![a, b])
      (fun r : C p =>
        r.1 = (a.1 * b.1 + a.2.1 * b.2.1) / denom ∧
        r.2.1 = (a.2.1 * b.1 - a.1 * b.2.1) / denom) := by
  intro denom
  enter_decl
  steps
  subst_vars
  simp only [HList.toTuple]
  constructor <;> rfl

/-
  scalar_multiply(c, s): scale both components by a field element
  result.real = c.real * s
  result.imaginary = c.imaginary * s
-/
theorem scalar_multiply_spec {p} (c : C p) (s : Fp p) :
    STHoare p env ⟦⟧
      («complexnr-0.0.0::scalar_multiply».call h![] h![c, s])
      (fun r : C p => r.1 = c.1 * s ∧ r.2.1 = c.2.1 * s) := by
  enter_decl
  steps
  subst_vars
  simp only [HList.toTuple]
  constructor <;> rfl

/-
  conjugate(c): negate the imaginary part
  result.real = c.real
  result.imaginary = -c.imaginary
-/
theorem conjugate_spec {p} (c : C p) :
    STHoare p env ⟦⟧
      («complexnr-0.0.0::conjugate».call h![] h![c])
      (fun r : C p => r.1 = c.1 ∧ r.2.1 = -c.2.1) := by
  enter_decl
  steps
  subst_vars
  simp only [HList.toTuple]
  constructor <;> rfl

/-
  squared_magnitude(c): c.real² + c.imaginary²
-/
theorem squared_magnitude_spec {p} (c : C p) :
    STHoare p env ⟦⟧
      («complexnr-0.0.0::squared_magnitude».call h![] h![c])
      (fun r : Fp p => r = c.1 * c.1 + c.2.1 * c.2.1) := by
  enter_decl
  steps
  subst_vars
  rfl

end «complexnr-0.0.0»
