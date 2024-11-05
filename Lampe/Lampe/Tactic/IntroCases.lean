import Mathlib.Tactic.CasesM

syntax "intro_cases": tactic
macro_rules | `(tactic|intro_cases) => `(tactic | (intros ; try casesm* _ ∧ _, ∃_, _))

initialize
  Lean.registerTraceClass `Lampe
