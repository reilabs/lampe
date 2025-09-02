import Lampe

open Lampe

noir_def hello<>() -> String<5 : u32> := {
  "hello"
}

def helloEnv : Env := .mk [hello] []
 /- testing enter_decl error reporting -/

/--
error: Unable to find a declaration in the environment with the right name
-/
#guard_msgs in
theorem enter_decl_error : STHoare p env ⟦⟧ (hello.call h![] h![])
    fun output => (String.mk output.toList) = "hello" := by
  enter_decl

/- testing enter_block_as error reporting -/

/--
error: failed to synthesize
  OfNat String 5
numerals are polymorphic in Lean, but the numeral `5` cannot be used in a context where the expected type is
  String
due to the absence of the instance above

Additional diagnostic information may be available using the `set_option diagnostics true` command.-/
#guard_msgs in
theorem enter_block_error : STHoare p helloEnv ⟦⟧ (hello.call h![] h![])
    fun output => (String.mk output.toList) = "hello" := by
  enter_decl
  step_as (⟦⟧) (fun (v : Tp.denote p (Tp.str 5)) => (String.mk v.toList) = 5)
  sorry

/- testing steps error messaging -/

/-- error: unknown identifier 'bad_lemma'-/
#guard_msgs in
theorem steps_error : STHoare p helloEnv ⟦⟧ (hello.call h![] h![])
    fun output => (String.mk output.toList) = "hello" := by
  enter_decl
  steps [bad_lemma]
  sorry

noir_def loop_fn<>() -> Field := {
  let mut t = 1 : Field;

  for _i in (0 : u32)..(5 : u32) do {
    t = (#_fMul returning Field)(t, 2 : Field);
  } ;
  t
}

def loopEnv : Env := .mk [loop_fn] []

/- testing loop_inv error reporting -/

/--
error: unknown identifier 'u'
---
error: unknown identifier 'u'
-/
#guard_msgs in
theorem loop_inv_error : STHoare p loopEnv ⟦⟧ (loop_fn.call h![] h![])
    fun output => output = (32 : Tp.denote p Tp.field) := by
  enter_decl
  steps
  loop_inv fun i _ _ => [u ↦ ⟨Tp.field, 3⟩] -- random mal-formed loop invariant to show it works
  all_goals sorry
