import Lampe

open Lampe

nr_def «NEGONE»<>() -> Field {
  -1 : Field
}

nr_def «zero?»<>() -> Field {
  #fAdd((@NEGONE<> as λ() → Field)(), 1 : Field) : Field
}

example : STHoare p Γ ⟦⟧ (zero?.fn.body _ h![] |>.body h![])
  fun (v : Tp.denote p .field) => v = 0 := by
  simp only [zero?, NEGONE]
  steps


  -- · apply STHoare.callDecl_intro
  --   sl



