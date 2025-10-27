import «std-1.0.0-beta.12».Extracted
import Lampe

namespace Lampe.Stdlib.Lib

open «std-1.0.0-beta.12»

/-- 
Note that as printing is inherently an unconstrained-only operation, this theorem is not capable of
asserting actual properties about the printing operation. Instead it simply exists to make it easy
to step through print calls when verifying your programs.
-/
theorem println_spec {p T a}
  : STHoare p env ⟦⟧
    («std-1.0.0-beta.12::println».call h![T] h![a])
    (fun r => r = ()) := by
  enter_decl
  step_as (⟦⟧) (fun r => r = ())
  steps
  step_as (⟦⟧) (fun r => (r : Tp.denote p .unit) = ())
  · enter_decl
    steps
  · steps
    simp_all

/-- 
Note that as printing is inherently an unconstrained-only operation, this theorem is not capable of
asserting actual properties about the printing operation. Instead it simply exists to make it easy
to step through print calls when verifying your programs.
-/
theorem print_spec {p T a}
  : STHoare p env ⟦⟧
    («std-1.0.0-beta.12::print».call h![T] h![a])
    (fun r => r = ()) := by
  enter_decl
  step_as (⟦⟧) (fun r => r = ())
  steps
  step_as (⟦⟧) (fun r => (r : Tp.denote p .unit) = ())
  · enter_decl
    steps
  · steps
    simp_all

-- TODO (#108) verify_proof_with_type

