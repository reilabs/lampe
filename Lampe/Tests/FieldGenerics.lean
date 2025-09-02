import Lampe

open Lampe

noir_def A<>() → Field := {
  4294967297 : Field
}

noir_def foo<A: Field>() → Field := {
  fConst!(A: Field)
}

noir_def test<>() → Field := {
  let a = (foo<4294967297: Field> as λ() → Field)();
  a
}

def fgEnv : Env := ⟨[A, foo, test], []⟩

lemma A_intro : STHoare p fgEnv ⟦⟧ (A.call h![] h![]) fun r => r = (4294967297 : Fp p) := by
  enter_decl
  steps
  subst_vars
  rfl

lemma foo_intro : STHoare p fgEnv ⟦⟧ (foo.call h![gen] h![]) 
    fun output => output = (gen : Fp p) := by
  enter_decl
  steps [A_intro]
  subst_vars
  rfl

lemma test_intro : STHoare p fgEnv ⟦⟧ (test.call h![] h![]) 
    fun output => output = (4294967297 : Fp p) := by
  enter_decl
  steps [A_intro, foo_intro]
  subst_vars
  rfl
