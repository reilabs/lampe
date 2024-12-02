import Lampe.Tp

namespace Lampe

class LawfulHeap (α : Type _) where
  union : α → α → α
  disjoint : α → α → Prop
  empty : α

  private thm_union_empty {a : α} : union a empty = a
  private thm_union_assoc {s₁ s₂ s₃ : α} : union (union s₁ s₂) s₃ = union s₁ (union s₂ s₃)
  private thm_disjoint_symm_iff {a b : α} : disjoint a b ↔ disjoint b a
  private thm_union_comm_of_disjoint {s₁ s₂ : α} : disjoint s₁ s₂ → union s₁ s₂ = union s₂ s₁
  private thm_disjoint_union_left (x y z : α) : disjoint (union x y) z ↔ disjoint x z ∧ disjoint y z
  private thm_disjoint_empty (x : α) : disjoint empty x

instance [LawfulHeap α] : Union α := ⟨LawfulHeap.union⟩
instance [LawfulHeap α] : EmptyCollection α := ⟨LawfulHeap.empty⟩

theorem LawfulHeap.disjoint_symm_iff [LawfulHeap α] {s₁ s₂ : α} :
  LawfulHeap.disjoint s₁ s₂ ↔ LawfulHeap.disjoint s₂ s₁ := by
  exact LawfulHeap.thm_disjoint_symm_iff

theorem LawfulHeap.union_comm_of_disjoint_ [LawfulHeap α] {s₁ s₂ : α} :
  LawfulHeap.disjoint s₁ s₂ → s₁ ∪ s₂ = s₂ ∪ s₁ := by
  simp [Union.union]
  exact LawfulHeap.thm_union_comm_of_disjoint

theorem LawfulHeap.union_empty_comm [LawfulHeap α] {a : α} :
  a ∪ ∅ = ∅ ∪ a := by
  have h := LawfulHeap.thm_disjoint_empty a
  simp [Union.union, EmptyCollection.emptyCollection]
  rw [LawfulHeap.thm_union_comm_of_disjoint h]

@[simp]
theorem LawfulHeap.union_empty [LawfulHeap α] {a : α} :
  a ∪ ∅ = a := by
  apply LawfulHeap.thm_union_empty

@[simp]
theorem LawfulHeap.empty_union [LawfulHeap α] {a : α} :
  ∅ ∪ a = a := by
  rw [←LawfulHeap.union_empty_comm]
  apply LawfulHeap.thm_union_empty

@[simp]
theorem LawfulHeap.disjoint_empty [LawfulHeap α] {a : α} :
  LawfulHeap.disjoint a ∅ := by
   rw [LawfulHeap.thm_disjoint_symm_iff]
   apply LawfulHeap.thm_disjoint_empty

@[simp]
theorem LawfulHeap.empty_disjoint [LawfulHeap α] {a : α} :
  LawfulHeap.disjoint ∅ a := by
   apply LawfulHeap.thm_disjoint_empty

theorem LawfulHeap.union_assoc [LawfulHeap α] {s₁ s₂ s₃ : α} :
  s₁ ∪ s₂ ∪ s₃ = s₁ ∪ (s₂ ∪ s₃) := by
  simp [Union.union]
  apply LawfulHeap.thm_union_assoc

theorem LawfulHeap.disjoint_union_left [LawfulHeap α] (x y z : α) :
  LawfulHeap.disjoint (x ∪ y) z ↔ LawfulHeap.disjoint x z ∧ LawfulHeap.disjoint y z := by
  simp [Union.union]
  apply LawfulHeap.thm_disjoint_union_left

theorem LawfulHeap.disjoint_union_right [LawfulHeap α] (x y z : α) :
  LawfulHeap.disjoint x (y ∪ z) ↔ LawfulHeap.disjoint x y ∧ LawfulHeap.disjoint x z := by
  conv =>
    lhs
    rw [LawfulHeap.thm_disjoint_symm_iff]
  conv =>
    rhs
    rw [LawfulHeap.thm_disjoint_symm_iff]
    rhs
    rw [LawfulHeap.thm_disjoint_symm_iff]
  apply LawfulHeap.thm_disjoint_union_left

end Lampe
