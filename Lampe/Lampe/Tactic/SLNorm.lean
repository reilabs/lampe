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
