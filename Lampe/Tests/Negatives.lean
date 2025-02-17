import Lampe

open Lampe

nr_def «NEGONE»<>() -> Field {
  -1 : Field
}

nr_def «zero?»<>() -> Field {
  #fAdd((@NEGONE<> as λ() → Field)(), 1 : Field) : Field
}

def env := Env.mk [("zero?", zero?.fn), ("NEGONE", NEGONE.fn)] []

lemma SLP.pure_star_iff_and [LawfulHeap α] {H : SLP α} : (⟦P⟧ ⋆ H) st ↔ P ∧ H st := by
  simp [SLP.star, SLP.lift]
  apply Iff.intro
  · rintro ⟨st₁, st₂, hdis, hst, ⟨hp, rfl⟩, hH⟩
    simp only [LawfulHeap.empty_union] at hst
    cases hst
    simp_all
  · intro ⟨hP, hH⟩
    exists ∅, st
    simp_all

lemma STHoare.pure_left_of_imp (h : P → STHoare p Γ ⟦P⟧ E Q): STHoare p Γ ⟦P⟧ E Q := by
  simp_all [STHoare, THoare, SLP.pure_star_iff_and]

example : STHoare p env ⟦⟧ (zero?.fn.body _ h![] |>.body h![])
  fun (v : Tp.denote p .field) => v = 0 := by
  simp only [zero?, NEGONE]
  steps
  apply STHoare.pure_left_of_imp
  rintro rfl
  · apply STHoare.callDecl_intro (Q := fun v => v = -1)
    on_goal 5 => sl; intro; rfl
    on_goal 2 => simp [env]; rfl
    any_goals rfl
    simp only [NEGONE]
    steps
    simp_all
  steps
  simp_all
