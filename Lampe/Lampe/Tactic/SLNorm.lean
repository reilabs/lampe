import Lampe.SeparationLogic.State
import Lampe.SeparationLogic.SLP

namespace Lampe.SLP

namespace Internal

theorem rot_singleton_pure {P : Prop} : ([a ↦ b] ⋆ P) = (P ⋆ [a ↦ b]) := by
  rw [star_comm]

theorem rot_singleton_pure_star {P : Prop} {Q : SLP (State p)} : ([a ↦ b] ⋆ P ⋆ Q) = (P ⋆ [a ↦ b] ⋆ Q) := by
  rw [SLP.star_comm, SLP.star_assoc]
  apply SLP.eq_of_iff <;> {apply SLP.star_mono_l; rw [SLP.star_comm]; apply SLP.entails_self}

theorem rot_forall_pure [LawfulHeap α] {P : Prop} {f : β → SLP α} : (SLP.forall' f ⋆ P) = (P ⋆ SLP.forall' f) := by
  simp [SLP.star_comm]

theorem rot_forall_pure_star [LawfulHeap α] {P : Prop} {f : β → SLP α} {Q : SLP α} :
    (SLP.forall' f ⋆ P ⋆ Q) = (P ⋆ SLP.forall' f ⋆ Q) := by
  rw [SLP.star_comm, SLP.star_assoc]
  apply SLP.eq_of_iff <;> {apply SLP.star_mono_l; rw [SLP.star_comm]; apply SLP.entails_self}

theorem rot_exists_pure [LawfulHeap α] {P : Prop} {f : β → SLP α} : (SLP.exists' f ⋆ P) = (P ⋆ SLP.exists' f) := by
  simp [SLP.star_comm]

theorem rot_exists_pure_star {P : Prop} {Q : SLP (State p)} : (SLP.exists' f ⋆ P ⋆ Q) = (P ⋆ SLP.exists' f ⋆ Q) := by
  rw [SLP.star_comm, SLP.star_assoc]
  apply SLP.eq_of_iff <;> {apply SLP.star_mono_l; rw [SLP.star_comm]; apply SLP.entails_self}

theorem exi_test! {P : α → SLP (State p)} {Q : SLP (State p)}: (∃∃x, P x ⋆ Q) = ((∃∃x, P x) ⋆ Q) := by
  apply SLP.eq_of_iff
  · unfold SLP.exists' SLP.star
    rintro st ⟨v, ⟨st₁, st₂, stdisj, stsum, P, Q⟩⟩
    exists st₁, st₂, stdisj, stsum
    apply And.intro _ Q
    exists v
  · unfold SLP.exists' SLP.star
    rintro st ⟨st₁, st₂, stdisj, stsum, ⟨v, P⟩, Q⟩
    exists v, st₁, st₂

theorem exi_test2 {P : α → SLP (State p)} {Q : SLP (State p)}: ((∃∃v, P v) ⊢ Q) ↔ (∀v, (P v ⊢ Q)) := by
  apply Iff.intro
  · unfold SLP.exists' SLP.entails
    intro hp v st P
    apply hp
    exists v
  · unfold SLP.exists' SLP.entails
    rintro h st ⟨v, P⟩
    apply h
    apply P

end Internal

macro "sl_norm" : tactic => `(tactic|(
  try simp only [
    star_assoc,
    star_true,
    true_star,
    exists_pure,
    exists_star,
    star_exists,
    Internal.rot_singleton_pure,
    Internal.rot_singleton_pure_star,
    Internal.rot_forall_pure,
    Internal.rot_forall_pure_star,
    Internal.rot_exists_pure,
    Internal.rot_exists_pure_star,
  ]
))

end Lampe.SLP
