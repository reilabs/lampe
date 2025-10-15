import Lampe

/-!
Theorems for Lean's builtin types that are needed to prove the standard library functionality. 
-/

namespace Lampe.Stdlib

set_option Lampe.pp.Expr false
set_option Lampe.pp.STHoare false

theorem Ordering.then_of_ne_eq (hp: o₁ ≠ .eq) : Ordering.then o₁ o₂ = o₁ := by cases o₁ <;> simp_all
