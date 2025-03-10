import Lampe

open Lampe

nr_def «NEGONE»<>() -> Field {
  -1 : Field
}

nr_def «zero?»<>() -> Field {
  #fAdd((@NEGONE<> as λ() → Field)(), 1 : Field) : Field
}

def env := Env.mk [zero?, NEGONE] []

example : STHoare p env ⟦⟧ (zero?.fn.body _ h![] |>.body h![])
  fun (v : Tp.denote p .field) => v = 0 := by
  simp only [zero?]
  steps

  enter_block_as (⟦⟧) (fun v => v = -1)
  · enter_decl
    simp only [NEGONE]
    steps
    simp_all

  steps
  simp_all
