import Lampe.Tp

namespace Lampe

class SLH (α : Type _) where
  union : α → α → α
  disjoint : α → α → Prop
  empty : α

  union_empty {a : α} : union a empty = a
  union_assoc {s₁ s₂ s₃ : α} : union (union s₁ s₂) s₃ = union s₁ (union s₂ s₃)
  disjoint_symm_iff {a b : α} : disjoint a b ↔ disjoint b a
  union_comm_of_disjoint {s₁ s₂ : α} : disjoint s₁ s₂ → union s₁ s₂ = union s₂ s₁
  disjoint_union_left (x y z : α) : disjoint (union x y) z ↔ disjoint x z ∧ disjoint y z
  disjoint_union_right (x y z : α) : disjoint x (union y z) ↔ disjoint x y ∧ disjoint x z
  disjoint_empty (x : α) : disjoint empty x

instance [SLH α] : Union α := ⟨SLH.union⟩
instance [SLH α] : EmptyCollection α := ⟨SLH.empty⟩

theorem SLH_union_empty_commutative [SLH α] {a : α} :
  a ∪ ∅ = ∅ ∪ a := by
  have h := SLH.disjoint_empty a
  simp [Union.union, EmptyCollection.emptyCollection]
  rw [SLH.union_comm_of_disjoint h]

theorem SLH_union_comm_of_disjoint [SLH α] {s₁ s₂ : α}:
  SLH.disjoint s₁ s₂ → s₁ ∪ s₂ = s₂ ∪ s₁ := by
  simp [Union.union]
  exact SLH.union_comm_of_disjoint

@[simp]
theorem SLH_union_empty [SLH α] {a : α} :
  a ∪ ∅ = a := by
  apply SLH.union_empty

@[simp]
theorem SLH_empty_union [SLH α] {a : α} :
  ∅ ∪ a = a := by
  rw [←SLH_union_empty_commutative]
  apply SLH.union_empty

theorem SLH_union_assoc [SLH α] {s₁ s₂ s₃ : α} :
  s₁ ∪ s₂ ∪ s₃ = s₁ ∪ (s₂ ∪ s₃) := by
  simp [Union.union]
  apply SLH.union_assoc

theorem SLH_disjoint_union_left [SLH α] (x y z : α) :
  SLH.disjoint (x ∪ y) z ↔ SLH.disjoint x z ∧ SLH.disjoint y z := by
  simp [Union.union]
  apply SLH.disjoint_union_left

theorem SLH_disjoint_union_right [SLH α] (x y z : α) :
  SLH.disjoint x (y ∪ z) ↔ SLH.disjoint x y ∧ SLH.disjoint x z := by
  simp [Union.union]
  apply SLH.disjoint_union_right

end Lampe
