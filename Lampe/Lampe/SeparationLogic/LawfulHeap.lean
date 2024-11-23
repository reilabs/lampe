import Lampe.Tp

namespace Lampe

class LawfulHeap (α : Type _) where
  union : α → α → α
  disjoint : α → α → Prop
  empty : α

  union_empty {a : α} : union a empty = a
  union_assoc {s₁ s₂ s₃ : α} : union (union s₁ s₂) s₃ = union s₁ (union s₂ s₃)
  disjoint_symm_iff {a b : α} : disjoint a b ↔ disjoint b a
  union_comm_of_disjoint {s₁ s₂ : α} : disjoint s₁ s₂ → union s₁ s₂ = union s₂ s₁
  disjoint_union_left (x y z : α) : disjoint (union x y) z ↔ disjoint x z ∧ disjoint y z
  disjoint_empty (x : α) : disjoint empty x

instance [LawfulHeap α] : Union α := ⟨LawfulHeap.union⟩
instance [LawfulHeap α] : EmptyCollection α := ⟨LawfulHeap.empty⟩

theorem LawfulHeap_union_empty_commutative [LawfulHeap α] {a : α} :
  a ∪ ∅ = ∅ ∪ a := by
  have h := LawfulHeap.disjoint_empty a
  simp [Union.union, EmptyCollection.emptyCollection]
  rw [LawfulHeap.union_comm_of_disjoint h]

theorem LawfulHeap_union_comm_of_disjoint [LawfulHeap α] {s₁ s₂ : α}:
  LawfulHeap.disjoint s₁ s₂ → s₁ ∪ s₂ = s₂ ∪ s₁ := by
  simp [Union.union]
  exact LawfulHeap.union_comm_of_disjoint

@[simp]
theorem LawfulHeap_union_empty [LawfulHeap α] {a : α} :
  a ∪ ∅ = a := by
  apply LawfulHeap.union_empty

@[simp]
theorem LawfulHeap_empty_union [LawfulHeap α] {a : α} :
  ∅ ∪ a = a := by
  rw [←LawfulHeap_union_empty_commutative]
  apply LawfulHeap.union_empty

theorem LawfulHeap_union_assoc [LawfulHeap α] {s₁ s₂ s₃ : α} :
  s₁ ∪ s₂ ∪ s₃ = s₁ ∪ (s₂ ∪ s₃) := by
  simp [Union.union]
  apply LawfulHeap.union_assoc

theorem LawfulHeap_disjoint_union_left [LawfulHeap α] (x y z : α) :
  LawfulHeap.disjoint (x ∪ y) z ↔ LawfulHeap.disjoint x z ∧ LawfulHeap.disjoint y z := by
  simp [Union.union]
  apply LawfulHeap.disjoint_union_left

theorem LawfulHeap_disjoint_union_right [LawfulHeap α] (x y z : α) :
  LawfulHeap.disjoint x (y ∪ z) ↔ LawfulHeap.disjoint x y ∧ LawfulHeap.disjoint x z := by
  conv =>
    lhs
    rw [LawfulHeap.disjoint_symm_iff]
  conv =>
    rhs
    rw [LawfulHeap.disjoint_symm_iff]
    rhs
    rw [LawfulHeap.disjoint_symm_iff]
  apply LawfulHeap.disjoint_union_left

end Lampe
