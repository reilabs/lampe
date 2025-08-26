import Lampe

open Lampe

noir_def NEGONE<>() → Field := {
  -1 : Field
}

noir_def zero_by_another_name<>() → Field := {
  (#_fAdd returning Field)((NEGONE<> as λ() → Field)(), 1: Field)
}

def env : Env := ⟨[zero_by_another_name, NEGONE], []⟩

example : STHoare p env ⟦⟧ (zero_by_another_name.fn.body _ h![] |>.body h![])
  fun (v : Tp.denote p .field) => v = 0 := by
  simp only [zero_by_another_name]
  steps

  step_as (⟦⟧) (fun v => v = -1)
  · enter_decl
    steps
    simp_all

  steps
  simp_all

