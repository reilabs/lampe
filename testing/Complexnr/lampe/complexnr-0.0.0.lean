import «complexnr-0.0.0».Extracted

open Lampe

set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxRecDepth 4096

namespace «complexnr-0.0.0»

abbrev Complex (p : Prime) := Tp.denote p («complexnr-0.0.0::Complex».tp h![])

def Complex.real {p : Prime} (c : Complex p) : Fp p := c.1
def Complex.imag {p : Prime} (c : Complex p) : Fp p := c.2.1

theorem add_spec {p} (a b : Complex p) :
    STHoare p env ⟦⟧
      («complexnr-0.0.0::add».call h![] h![a, b])
      (fun r : Complex p => r.real = a.real + b.real ∧ r.imag = a.imag + b.imag) := by
  enter_decl
  steps
  subst_vars
  simp only [HList.toTuple]
  constructor <;> rfl

theorem subtract_spec {p} (a b : Complex p) :
    STHoare p env ⟦⟧
      («complexnr-0.0.0::subtract».call h![] h![a, b])
      (fun r : Complex p => r.real = a.real - b.real ∧ r.imag = a.imag - b.imag) := by
  enter_decl
  steps
  subst_vars
  simp only [HList.toTuple]
  constructor <;> rfl

theorem multiply_spec {p} (a b : Complex p) :
    STHoare p env ⟦⟧
      («complexnr-0.0.0::multiply».call h![] h![a, b])
      (fun r : Complex p =>
        r.real = a.real * b.real - a.imag * b.imag ∧
        r.imag = a.real * b.imag + a.imag * b.real) := by
  enter_decl
  steps
  subst_vars
  simp only [HList.toTuple]
  constructor <;> rfl

theorem divide_spec {p} (a b : Complex p) :
    let denom := b.real * b.real + b.imag * b.imag
    STHoare p env ⟦⟧
      («complexnr-0.0.0::divide».call h![] h![a, b])
      (fun r : Complex p =>
        r.real = (a.real * b.real + a.imag * b.imag) / denom ∧
        r.imag = (a.imag * b.real - a.real * b.imag) / denom) := by
  intro denom
  enter_decl
  steps
  subst_vars
  simp only [HList.toTuple]
  constructor <;> rfl

theorem scalar_multiply_spec {p} (c : Complex p) (s : Fp p) :
    STHoare p env ⟦⟧
      («complexnr-0.0.0::scalar_multiply».call h![] h![c, s])
      (fun r : Complex p => r.real = c.real * s ∧ r.imag = c.imag * s) := by
  enter_decl
  steps
  subst_vars
  simp only [HList.toTuple]
  constructor <;> rfl

theorem conjugate_spec {p} (c : Complex p) :
    STHoare p env ⟦⟧
      («complexnr-0.0.0::conjugate».call h![] h![c])
      (fun r : Complex p => r.real = c.real ∧ r.imag = -c.imag) := by
  enter_decl
  steps
  subst_vars
  simp only [HList.toTuple]
  constructor <;> rfl

theorem squared_magnitude_spec {p} (c : Complex p) :
    STHoare p env ⟦⟧
      («complexnr-0.0.0::squared_magnitude».call h![] h![c])
      (fun r : Fp p => r = c.real * c.real + c.imag * c.imag) := by
  enter_decl
  steps
  subst_vars
  rfl

end «complexnr-0.0.0»
