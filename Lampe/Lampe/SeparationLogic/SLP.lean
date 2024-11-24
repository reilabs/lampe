import Lampe.Tactic.IntroCases
import Lampe.SeparationLogic.LawfulHeap

namespace Lampe

def SLP (α) [LawfulHeap α] := α → Prop

namespace SLP

def star [LawfulHeap α] (lhs rhs : SLP α) : SLP α := fun st =>
  ∃ st₁ st₂, LawfulHeap.disjoint st₁ st₂ ∧ st = st₁ ∪ st₂ ∧ lhs st₁ ∧ rhs st₂

def lift [LawfulHeap α] (pr : Prop) : SLP α := fun st => pr ∧ st = ∅

def wand [LawfulHeap α] (lhs rhs : SLP α) : SLP α :=
  fun st => ∀st', LawfulHeap.disjoint st st' → lhs st' → rhs (st ∪ st')

def top [LawfulHeap α] : SLP α := fun _ => True

def entails [LawfulHeap α] (a b : SLP α) := ∀st, a st → b st

def forall' [LawfulHeap α] (f : β → SLP α) : SLP α := fun st => ∀v, f v st
def exists' [LawfulHeap α] (f : β → SLP α) : SLP α := fun st => ∃v, f v st

instance [LawfulHeap α]: Coe Prop (SLP α) := ⟨lift⟩

notation:max "⊤" => top

notation:max "⟦" x "⟧" => lift x

notation:max "⟦⟧" => ⟦True⟧

infixr:35 " ⋆ " => star

infixr:30 " -⋆ " => wand

infix:10 " ⊢ " => entails

open Lean.TSyntax.Compat in
macro "∃∃" xs:Lean.explicitBinders ", " b:term : term => Lean.expandExplicitBinders ``exists' xs b

open Lean.TSyntax.Compat in
macro "∀∀" xs:Lean.explicitBinders ", " b:term : term => Lean.expandExplicitBinders ``forall' xs b

theorem entails_trans [LawfulHeap α] {P Q R : SLP α}: (P ⊢ Q) → (Q ⊢ R) → (P ⊢ R) := by tauto

section basic

@[simp]
theorem apply_top [LawfulHeap α] {st : α} : ⊤ st := by trivial

theorem forall_left [LawfulHeap β] {P : α → SLP β} : (P a ⊢ Q) → ((∀∀(a : α), P a) ⊢ Q) := by
  unfold forall'
  tauto

theorem forall_right [LawfulHeap β] {H : SLP β} {H' : α → SLP β}: (∀x, H ⊢ H' x) → (H ⊢ ∀∀x, H' x) := by
  unfold forall' entails
  tauto

theorem pure_left [LawfulHeap β] {H H' : SLP β} : (P → (H ⊢ H')) → (P ⋆ H ⊢ H') := by
  unfold star entails lift
  intro_cases
  simp_all

theorem pure_left' [LawfulHeap α] {H : SLP α} : (P → (⟦⟧ ⊢ H)) → (P ⊢ H) := by
  unfold entails lift
  tauto

theorem pure_right [LawfulHeap α] {H₁ H₂ : SLP α} : P → (H₁ ⊢ H₂) → (H₁ ⊢ P ⋆ H₂) := by
  unfold star entails lift
  intros
  repeat apply Exists.intro
  simp_all
  apply And.intro ?_
  apply And.intro ?_
  apply And.intro rfl
  apply_assumption
  assumption
  . simp only [LawfulHeap_empty_union]
  . apply LawfulHeap.disjoint_empty

theorem entails_self [LawfulHeap α] {H : SLP α} : H ⊢ H := by tauto

theorem entails_top [LawfulHeap α] {H : SLP α} : H ⊢ ⊤ := by tauto

@[simp]
theorem forall_unused [LawfulHeap β] {α : Type u} [Inhabited α] {P : SLP β} : (∀∀ (_ : α), P) = P := by
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

theorem star_comm [LawfulHeap α] {G H : SLP α} : (G ⋆ H) = (H ⋆ G) := by
  funext
  unfold star
  rw [eq_iff_iff]
  apply Iff.intro <;> {
    intro_cases
    repeat apply Exists.intro
    rw [LawfulHeap.disjoint_symm_iff]
    apply And.intro (by assumption)
    rw [LawfulHeap_union_comm_of_disjoint (by rw [LawfulHeap.disjoint_symm_iff]; assumption)]
    tauto
  }

@[simp]
theorem true_star [LawfulHeap α] {H : SLP α} : (⟦⟧ ⋆ H) = H := by
  funext
  rw [eq_iff_iff]
  unfold lift star
  apply Iff.intro
  · simp_all
  · intro
    exists ∅, ?_
    simp_all [LawfulHeap.disjoint_empty]
    apply LawfulHeap.disjoint_empty

@[simp]
theorem star_true [LawfulHeap α] {H : SLP α} : (H ⋆ ⟦⟧) = H := by rw [star_comm]; simp

@[simp]
theorem star_assoc [LawfulHeap α] {F G H : SLP α} : ((F ⋆ G) ⋆ H) = (F ⋆ G ⋆ H) := by
  funext
  rw [eq_iff_iff]
  unfold star
  apply Iff.intro
  · intro_cases
    subst_vars
    rw [LawfulHeap_union_assoc]
    simp only [LawfulHeap_disjoint_union_left] at *
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
    simp_all [LawfulHeap_disjoint_union_right]
  · intro_cases
    subst_vars
    rw [←LawfulHeap_union_assoc]
    simp only [LawfulHeap_disjoint_union_right] at *
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
    simp_all [LawfulHeap_disjoint_union_left]

@[simp]
theorem ent_star_top [LawfulHeap α] {H : SLP α} : H ⊢ H ⋆ ⊤ := by
  intro _ _
  exists ?_, ∅
  rw [LawfulHeap.disjoint_symm_iff]
  simp_all [LawfulHeap.disjoint_empty]
  apply LawfulHeap.disjoint_empty

theorem star_mono_r [LawfulHeap α] {P Q R : SLP α} : (P ⊢ Q) → (P ⋆ R ⊢ Q ⋆ R) := by
  unfold star entails
  tauto

theorem star_mono_l [LawfulHeap α] {P Q R : SLP α} : (P ⊢ Q) → (R ⋆ P ⊢ R ⋆ Q) := by
  unfold star entails
  tauto

theorem star_mono_l' [LawfulHeap α] {P Q : SLP α} : (⟦⟧ ⊢ Q) → (P ⊢ P ⋆ Q) := by
  unfold star entails lift
  intros
  simp_all
  repeat apply Exists.intro
  apply And.intro ?_
  apply And.intro ?_
  tauto
  simp
  rw [LawfulHeap.disjoint_symm_iff]
  apply LawfulHeap.disjoint_empty

theorem star_mono [LawfulHeap α] {H₁ H₂ Q₁ Q₂ : SLP α} : (H₁ ⊢ H₂) → (Q₁ ⊢ Q₂) → (H₁ ⋆ Q₁ ⊢ H₂ ⋆ Q₂) := by
  unfold star entails
  tauto

theorem forall_star [LawfulHeap α] {P : α → SLP α} : (∀∀x, P x) ⋆ Q ⊢ ∀∀x, P x ⋆ Q := by
  unfold star forall'
  tauto

theorem star_forall [LawfulHeap β] {P : α → SLP β} {Q : SLP β} : Q ⋆ (∀∀x, P x) ⊢ ∀∀x, Q ⋆ P x := by
  unfold star forall'
  tauto

@[simp]
theorem top_star_top [LawfulHeap α] : (top ⋆ (⊤ : SLP α)) = (⊤ : SLP α) := by
  unfold top star
  funext x
  simp
  exists ∅, x
  simp [LawfulHeap.disjoint_empty]
  apply LawfulHeap.disjoint_empty

end star

section wand

variable {p : Prime}

@[simp]
theorem wand_self_star [LawfulHeap α] {H : SLP α}: (H -⋆ H ⋆ top) = top := by
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
    rw [LawfulHeap_union_comm_of_disjoint (by assumption)]
    rw [LawfulHeap.disjoint_symm_iff]
    assumption


theorem wand_intro [LawfulHeap α] {A B C : SLP α} : (A ⋆ B ⊢ C) → (A ⊢ B -⋆ C) := by
  unfold wand star entails
  intros
  intros
  apply_assumption
  tauto

theorem wand_cancel [LawfulHeap α] {P Q : SLP α} : (P ⋆ (P -⋆ Q)) ⊢ Q := by
  unfold star wand entails
  intro_cases
  subst_vars
  rename_i h
  rw [LawfulHeap_union_comm_of_disjoint (by assumption)]
  apply_assumption
  rw [LawfulHeap.disjoint_symm_iff]
  tauto
  tauto

end wand

end Lampe.SLP
