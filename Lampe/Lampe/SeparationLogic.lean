import Lampe.ValHeap
import Lampe.Tactic.IntroCases


namespace Lampe

def SLP (p : Prime) : Type := ValHeap p → Prop

namespace SLP

def star {p} (lhs rhs : SLP p) : SLP p := fun st =>
  ∃ st₁ st₂, Finmap.Disjoint st₁ st₂ ∧ st = st₁ ∪ st₂ ∧ lhs st₁ ∧ rhs st₂

def lift {p} (pr : Prop) : SLP p := fun st => pr ∧ st = ∅

def singleton {p} (r : Ref) (v : AnyValue p) : SLP p := fun st => st = Finmap.singleton r v

def wand {p} (lhs rhs : SLP p) : SLP p :=
  fun st => ∀st', st.Disjoint st' → lhs st' → rhs (st ∪ st')

def top {p} : SLP p := fun _ => True

def entails {p} (a b : SLP p) := ∀st, a st → b st

def forall' {p} (f : α → SLP p) : SLP p := fun st => ∀v, f v st
def exists' {p} (f : α → SLP p) : SLP p := fun st => ∃v, f v st

instance {p}: Coe Prop (SLP p) := ⟨lift⟩

notation:max "⊤" => top

notation:max "⟦" x "⟧" => lift x

notation:max "⟦⟧" => ⟦True⟧

infixr:35 " ⋆ " => star

infixr:30 " -⋆ " => wand

infix:10 " ⊢ " => entails

notation:max "[" l " ↦ " r "]" => singleton l r

open Lean.TSyntax.Compat in
macro "∃∃" xs:Lean.explicitBinders ", " b:term : term => Lean.expandExplicitBinders ``exists' xs b

open Lean.TSyntax.Compat in
macro "∀∀" xs:Lean.explicitBinders ", " b:term : term => Lean.expandExplicitBinders ``forall' xs b

theorem entails_trans {p} {P Q R : SLP p}: (P ⊢ Q) → (Q ⊢ R) → (P ⊢ R) := by tauto

section basic

variable {p : Prime}

@[simp]
theorem apply_top : ⊤ st := by trivial

theorem forall_left {a} {P : α → SLP p} : (P a ⊢ Q) → ((∀∀a, P a) ⊢ Q) := by
  unfold forall'
  tauto

theorem forall_right {H' : α → SLP p}: (∀x, H ⊢ H' x) → (H ⊢ ∀∀x, H' x) := by
  unfold forall' entails
  tauto

theorem pure_left: (P → (H ⊢ H')) → (P ⋆ H ⊢ H') := by
  unfold star entails lift
  intro_cases
  simp_all

theorem pure_left' {P} {H : SLP p} : (P → (⟦⟧ ⊢ H)) → (P ⊢ H) := by
  unfold entails lift
  tauto

theorem pure_right: P → (H₁ ⊢ H₂) → (H₁ ⊢ P ⋆ H₂) := by
  unfold star entails lift
  intros
  repeat apply Exists.intro
  simp_all
  apply And.intro ?_
  apply And.intro ?_
  apply And.intro rfl
  apply_assumption
  assumption
  simp
  simp [Finmap.disjoint_empty]

theorem entails_self : H ⊢ H := by tauto

theorem entails_top : H ⊢ ⊤ := by tauto

@[simp]
theorem forall_unused {α : Type u} [Inhabited α] {P : SLP p} : (∀∀(_:α), P) = P := by
  funext
  unfold forall'
  rw [eq_iff_iff]
  apply Iff.intro
  · intro
    apply_assumption
    apply Inhabited.default
  · intros
    apply_assumption

end basic

section star

variable {p : Prime}

theorem star_comm {G H:SLP p} : (G ⋆ H) = (H ⋆ G) := by
  funext
  unfold star
  rw [eq_iff_iff]
  apply Iff.intro <;> {
    intro_cases
    repeat apply Exists.intro
    rw [Finmap.Disjoint.symm_iff]
    apply And.intro (by assumption)
    rw [Finmap.union_comm_of_disjoint (by rw [Finmap.Disjoint.symm_iff]; assumption)]
    tauto
  }

@[simp]
theorem true_star {H:SLP p} : (⟦⟧ ⋆ H) = H := by
  funext
  rw [eq_iff_iff]
  unfold lift star
  apply Iff.intro
  · simp_all
  · intro
    exists ∅, ?_
    simp_all [Finmap.disjoint_empty]

@[simp]
theorem star_true {H:SLP p} : (H ⋆ ⟦⟧) = H := by rw [star_comm]; simp

@[simp]
theorem star_assoc {F G H:SLP p} : ((F ⋆ G) ⋆ H) = (F ⋆ G ⋆ H) := by
  funext
  rw [eq_iff_iff]
  unfold star
  apply Iff.intro
  · intro_cases
    subst_vars
    rw [Finmap.union_assoc]
    simp only [Finmap.disjoint_union_left] at *
    cases_type And
    repeat apply Exists.intro
    apply And.intro ?_
    apply And.intro rfl
    apply And.intro (by assumption)
    repeat apply Exists.intro
    apply And.intro ?_
    apply And.intro rfl
    simp_all
    assumption
    simp_all [Finmap.disjoint_union_right]
  · intro_cases
    subst_vars
    rw [←Finmap.union_assoc]
    simp only [Finmap.disjoint_union_right] at *
    cases_type And
    repeat apply Exists.intro
    apply And.intro ?_
    apply And.intro rfl
    apply And.intro ?_ (by assumption)
    repeat apply Exists.intro
    apply And.intro ?_
    apply And.intro rfl
    simp_all
    assumption
    simp_all [Finmap.disjoint_union_left]

@[simp]
theorem ent_star_top {H : SLP p} : H ⊢ H ⋆ ⊤ := by
  intro _ _
  exists ?_, ∅
  rw [Finmap.Disjoint.symm_iff]
  simp_all [Finmap.disjoint_empty]

theorem star_mono_r : (P ⊢ Q) → (P ⋆ R ⊢ Q ⋆ R) := by
  unfold star entails
  tauto

theorem star_mono_l : (P ⊢ Q) → (R ⋆ P ⊢ R ⋆ Q) := by
  unfold star entails
  tauto

theorem star_mono_l' : (⟦⟧ ⊢ Q) → (P ⊢ P ⋆ Q) := by
  unfold star entails lift
  intros
  simp_all
  repeat apply Exists.intro
  apply And.intro ?_
  apply And.intro ?_
  tauto
  simp
  tauto

theorem star_mono : (H₁ ⊢ H₂) → (Q₁ ⊢ Q₂) → (H₁ ⋆ Q₁ ⊢ H₂ ⋆ Q₂) := by
  unfold star entails
  tauto

theorem forall_star {P : α → SLP p} : (∀∀x, P x) ⋆ Q ⊢ ∀∀x, P x ⋆ Q := by
  unfold star forall'
  tauto

theorem star_forall {P : α → SLP p} : Q ⋆ (∀∀x, P x) ⊢ ∀∀x, Q ⋆ P x := by
  unfold star forall'
  tauto

@[simp]
theorem top_star_top : (top (p := p) ⋆ ⊤) = ⊤ := by
  unfold top star
  funext x
  simp
  exists ∅, x
  simp [Finmap.disjoint_empty]

end star

section wand

variable {p : Prime}

@[simp]
theorem wand_self_star {H:SLP p}: (H -⋆ H ⋆ top) = top := by
  funext
  unfold wand star
  apply eq_iff_iff.mpr
  apply Iff.intro
  · intro
    simp [lift]
  · intros
    repeat apply Exists.intro
    apply And.intro ?_
    apply And.intro ?_
    apply And.intro (by assumption)
    simp
    rotate_left
    rotate_left
    rw [Finmap.union_comm_of_disjoint (by assumption)]
    rw [Finmap.Disjoint.symm_iff]
    assumption


theorem wand_intro {A B C : SLP p} : (A ⋆ B ⊢ C) → (A ⊢ B -⋆ C) := by
  unfold wand star entails
  intros
  intros
  apply_assumption
  tauto

theorem wand_cancel : (P ⋆ (P -⋆ Q)) ⊢ Q := by
  unfold star wand entails
  intro_cases
  subst_vars
  rename_i h
  rw [Finmap.union_comm_of_disjoint (by assumption)]
  apply_assumption
  tauto
  tauto

end wand

end SLP

end Lampe
