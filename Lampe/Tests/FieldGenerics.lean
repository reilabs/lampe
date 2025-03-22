import Lampe

open Lampe

nr_def «A»<>() -> Field {
    4294967297 : Field
}


nr_def «foo»<@A : Field>() -> Field {
    f@A
}

nr_def «test»<>() -> Field {
    let a = (@foo<4294967297 : Field> as λ() → Field)();
    a
}

def env := Lampe.Env.mk [«A», «foo», «test»] []

lemma A_intro : STHoare p env ⟦⟧ (A.call h![] h![]) fun output => output = (4294967297 : Fp p) := by
    enter_decl
    steps
    subst_vars
    rfl

lemma foo_intro : STHoare p env ⟦⟧ (foo.call h![gen] h![]) fun output => output = (gen : Fp p) := by
    enter_decl
    steps [A_intro]
    subst_vars
    rfl

lemma test_intro : STHoare p env ⟦⟧ (test.call h![] h![]) fun output => output = (4294967297 : Fp p) := by
    enter_decl
    steps [A_intro, foo_intro]
    subst_vars
    rfl


