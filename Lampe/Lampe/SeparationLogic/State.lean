import Lampe.SeparationLogic.SLH
import Lampe.SeparationLogic.ValHeap
import Lampe.Ast

namespace Lampe

abbrev Closures := Finmap fun _ : Ref => Lampe.Function

structure State (p : Prime) where
  vals : ValHeap p
  closures : Closures

instance : Membership Ref (State p) where
  mem := fun a e => e ∈ a.vals

instance : Coe (State p) (ValHeap p) where
  coe := fun s => s.vals

/-- Maps a condition on `State`s to a condition on `ValHeap`s by keeping the closures fixed -/
@[reducible]
def mapToValHeapCondition
  (closures : Finmap fun _ : Ref => Function)
  (Q : Option (State p × T) → Prop) : Option (ValHeap p × T) → Prop :=
  fun vv => Q (vv.map (fun (vals, t) => ⟨⟨vals, closures⟩, t⟩))

/-- Maps a condition on `ValHeap`s to a condition on `State`s -/
@[reducible]
def mapToStateCondition
  (Q : Option (ValHeap p × T) → Prop) : Option (State p × T) → Prop :=
  fun stv => Q (stv.map (fun (st, t) => ⟨st.vals, t⟩))

def State.insertVal (self : State p) (r : Ref) (v : AnyValue p) : State p :=
  ⟨self.vals.insert r v, self.closures⟩

theorem State.eq_parts :
  v = v' → c = c' → State.mk v c = State.mk v' c' := by
  intros
  subst_vars
  rfl

instance : SLH (State p) where
  union := fun a b => ⟨a.vals ∪ b.vals, a.closures ∪ b.closures⟩
  disjoint := fun a b => a.vals.Disjoint b.vals ∧ a.closures.Disjoint b.closures
  empty := ⟨∅, ∅⟩
  union_empty := by
    intros
    simp only [Finmap.union_empty]
  union_assoc := by
    intros
    simp only [Union.union]
    apply State.eq_parts
    . apply Finmap.union_assoc
    . apply Finmap.union_assoc
  disjoint_symm_iff := by tauto
  union_comm_of_disjoint := by
    intros
    simp only [Union.union]
    apply State.eq_parts
    . apply Finmap.union_comm_of_disjoint
      tauto
    . apply Finmap.union_comm_of_disjoint
      tauto
  disjoint_empty := by tauto
  disjoint_union_left := by
    intros x y z
    have h1 := (Finmap.disjoint_union_left x.vals y.vals z.vals)
    have h2 := (Finmap.disjoint_union_left x.closures y.closures z.closures)
    constructor
    intro h3
    simp only [Union.union] at h3
    constructor
    constructor
    cases h3
    tauto
    tauto
    tauto
    intro h3
    simp only [Union.union] at h3
    constructor
    tauto
    tauto
  disjoint_union_right := by
    intros x y z
    have h1 := (Finmap.disjoint_union_right x.vals y.vals z.vals)
    have h2 := (Finmap.disjoint_union_right x.closures y.closures z.closures)
    constructor
    intro h3
    simp only [Union.union] at h3
    constructor
    constructor
    cases h3
    tauto
    tauto
    tauto
    intro h3
    simp only [Union.union] at h3
    constructor
    tauto
    tauto

def State.singleton (r : Ref) (v : AnyValue p) : SLP (State p) := fun st => st.vals = Finmap.singleton r v

notation:max "[" l " ↦ " r "]" => State.singleton l r

theorem State.union_parts :
  (State.mk v c ∪ st₂ = State.mk (v ∪ st₂.vals) (c ∪ st₂.closures)) := by
  aesop

end Lampe
