import Lean
import Lampe

open Lean Elab Term

open Lampe

noir_def f1<>(x: u64) -> u64 := {
  x
}

noir_def f2<>(x: u64) -> u64 := {
  (f1<> as λ(u64) → u64)(x)
}

def env : Env := ⟨[f1, f2], []⟩

theorem f1_spec {p x} [Prime.BitsGT p 64]
  : STHoare p env ⟦⟧
    (f1.call h![] h![x])
    (fun r => r = x) := by
  enter_decl
  steps
  simp_all

theorem f2_spec {p x} [Prime.BitsGT p 128]
  : STHoare p env ⟦⟧
    (f2.call h![] h![x])
    (fun r => r = x) := by
  enter_decl
  steps [f1_spec (p := p)]
  simp_all

