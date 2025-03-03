import Lampe.SeparationLogic.LawfulHeap
import Lampe.SeparationLogic.ValHeap
import Lampe.Ast

namespace Lampe

abbrev Lambdas (p : Prime) := Finmap fun _ : Ref => Lambda (Tp.denote p)

structure State (p : Prime) where
  vals : ValHeap p
  lambdas : Lambdas p

instance : Membership Ref (State p) where
  mem := fun a e => e ∈ a.vals

@[simp]
theorem State.mem_iff_mem_val {a : State p} : e ∈ a ↔ e ∈ a.vals := by rfl

instance : Coe (State p) (ValHeap p) where
  coe := fun s => s.vals

/-- Maps a post-condition on `State`s to a post-condition on `ValHeap`s by keeping the lambdas fixed -/
@[reducible]
def mapToVHCond (lambdas : Lambdas p) (Q : Option (State p × T) → Prop) : Option (ValHeap p × T) → Prop :=
  fun vhv => Q (vhv.map (fun (vals, t) => ⟨⟨vals, lambdas⟩, t⟩))

@[simp]
theorem mapToVHCond_some_iff {Q : Option (State p × T) → Prop} :
  ((mapToVHCond lmbds Q) (some ⟨vh, v⟩)) ↔ (Q (some ⟨⟨vh, lmbds⟩, v⟩)) := by tauto

@[simp]
theorem mapToVHCond_none_iff {Q : Option (State p × T) → Prop} :
  ((mapToVHCond lmbds Q) none) ↔ (Q none) := by tauto

theorem mapToVHCond_iff_fun_match {Q : Option (State p × T) → Prop} :
(mapToVHCond lmbds Q) =
  (fun vhv => match vhv with
    | none => Q none
    | some (vh, v) => Q (some ⟨⟨vh, lmbds⟩, v⟩)) := by
    unfold mapToVHCond
    simp only
    funext vhv
    casesm Option (ValHeap _ × _) <;> rfl

def State.insertVal (self : State p) (r : Ref) (v : AnyValue p) : State p :=
  ⟨self.vals.insert r v, self.lambdas⟩

instance : LawfulHeap (State p) where
  union := fun a b => ⟨a.vals ∪ b.vals, a.lambdas ∪ b.lambdas⟩
  disjoint := fun a b => a.vals.Disjoint b.vals ∧ a.lambdas.Disjoint b.lambdas
  empty := ⟨∅, ∅⟩
  thm_union_empty := by
    intros
    simp only [Finmap.union_empty]
  thm_union_assoc := by
    intros
    simp only [Union.union, State.mk.injEq]
    apply And.intro <;> apply Finmap.union_assoc
  thm_disjoint_symm_iff := by tauto
  thm_union_comm_of_disjoint := by
    intros
    simp only [Union.union, State.mk.injEq]
    apply And.intro <;> { apply Finmap.union_comm_of_disjoint; tauto }
  thm_disjoint_empty := by tauto
  thm_disjoint_union_left := by
    intros x y z
    have h1 := (Finmap.disjoint_union_left x.vals y.vals z.vals)
    have h2 := (Finmap.disjoint_union_left x.lambdas y.lambdas z.lambdas)
    constructor
    intro h3
    simp only [Union.union] at h3
    constructor <;> constructor
    all_goals tauto

@[reducible]
def State.valSingleton (r : Ref) (v : AnyValue p) : SLP (State p) :=
  fun st => st.vals = Finmap.singleton r v

notation:max "[" l " ↦ " r "]" => State.valSingleton l r

@[reducible]
def State.lmbSingleton (r : Ref) (v : Lambda (Tp.denote p)) : SLP (State p) :=
  fun st => st.lambdas = Finmap.singleton r v

notation:max "[" "λ" l " ↦ " r "]" => State.lmbSingleton l r

@[simp]
theorem State.union_parts_left :
  (State.mk v c ∪ st₂ = State.mk (v ∪ st₂.vals) (c ∪ st₂.lambdas)) := by
  rfl

@[simp]
theorem State.union_parts_right :
  (st₂ ∪ State.mk v c = State.mk (st₂.vals ∪ v) (st₂.lambdas ∪ c)) := by
  rfl

@[simp]
theorem State.union_parts :
  st₁ ∪ st₂ = State.mk (st₁.vals ∪ st₂.vals) (st₁.lambdas ∪ st₂.lambdas) := by
  rfl

@[simp]
theorem State.union_vals {st₁ st₂ : State p} :
  (st₁ ∪ st₂).vals = (st₁.vals ∪ st₂.vals) := by rfl

@[simp]
theorem State.union_closures {st₁ st₂ : State p} :
  (st₁ ∪ st₂).lambdas = (st₁.lambdas ∪ st₂.lambdas) := by rfl

end Lampe
