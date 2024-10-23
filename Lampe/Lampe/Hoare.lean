import Lampe.Ast
-- import Lampe.Assignable
import Lampe.Tp
import Lampe.Data.Field
import Lampe.Tactic.IntroCases
import Lampe.Semantics
import Lampe.Syntax
import Lampe.State
import Mathlib

namespace Lampe

variable (p : Prime)

def SLP : Type := State p → Prop

def star {p} (lhs rhs : SLP p) : SLP p := fun st =>
  ∃ st₁ st₂, Finmap.Disjoint st₁ st₂ ∧ st = st₁ ∪ st₂ ∧ lhs st₁ ∧ rhs st₂

def lift {p} (pr : Prop) : SLP p := fun st => pr ∧ st = ∅

def singleton {p} (r : Ref) (v : AnyValue p) : SLP p := fun st => st = Finmap.singleton r v

def wand {p} (lhs rhs : SLP p) : SLP p :=
  fun st => ∀st', st.Disjoint st' → lhs st' → rhs (st ∪ st')

def top {p} : SLP p := fun _ => True

instance {p}: Coe Prop (SLP p) := ⟨lift⟩

notation "[|" x "|]" => lift x

notation l " ⋆ " r => star l r

notation l " -⋆ " r => wand l r

notation "[" l " ↦ " r "]" => singleton l r


def ent {p} (a b : SLP p) := ∀st, a st → b st

def exis (x : α → SLP p): SLP p := fun st => ∃ v, x v st

@[simp]
theorem true_star : ([|True|] ⋆ H) = H := by
  unfold Lampe.star
  unfold lift
  simp
  funext x
  simp only [eq_iff_iff]
  apply Iff.intro
  · rintro ⟨st1, st2, dis, x, y, z⟩
    subst_vars
    simp_all
  · intro
    repeat apply Exists.intro
    apply And.intro
    rotate_left
    apply And.intro
    rotate_left
    apply And.intro
    rfl
    assumption
    apply Finmap.disjoint_empty
    simp

theorem star_comm : (a ⋆ b) = (b ⋆ a) := by
  unfold Lampe.star
  funext st
  simp only [eq_iff_iff]
  apply Iff.intro
  · intro_cases
    repeat apply Exists.intro
    apply And.intro
    apply Finmap.Disjoint.symm
    assumption
    simp_all
    apply Finmap.union_comm_of_disjoint
    assumption
  · intro_cases
    repeat apply Exists.intro
    apply And.intro
    apply Finmap.Disjoint.symm
    assumption
    simp_all
    apply Finmap.union_comm_of_disjoint
    assumption

theorem star_assoc : ((a ⋆ b) ⋆ c) = (a ⋆ (b ⋆ c)) := by
  sorry

syntax (priority := low) term "⊢" term : term
macro_rules
| `($a ⊢ $b) => `(ent $a $b)


@[aesop safe]
theorem ent_self : H ⊢ H := by
  simp [ent]

theorem ent_self' (H : α → SLP p): H v ⊢ H v := by
  simp [ent]

def PHoare
    {tp : Tp}
    (Γ : Env)
    (P : SLP p)
    (e : Expr (Tp.denote p) tp)
    (Q : (tp.denote p) → SLP p): Prop :=
  ∀st st' v, P st → BigStep p Γ st e st' v → Q v st'

def SPHoare p Γ P e (Q : Tp.denote p tp → SLP p) := ∀H, PHoare p Γ (P ⋆ H) e (fun v => ((Q v) ⋆ H))

@[simp]
lemma top_st : top st := by trivial

lemma ent_star_top : H ⊢ (H ⋆ top) := by
  intro st h
  exists st
  exists ∅
  simp_all [Finmap.Disjoint.symm, Finmap.disjoint_empty]

@[aesop safe]
theorem var_intro':
    SPHoare p Γ (P n) (Expr.var n) P := by
  unfold SPHoare PHoare
  intros
  casesm BigStep _ _ _ _ _ _
  -- apply ent_star_top
  simp_all

@[aesop safe]
theorem var_intro :
    SPHoare p Γ [|True|] (Expr.var n) (fun v => [|v = n|]) := by
  unfold SPHoare PHoare
  intros
  casesm BigStep _ _ _ _ _ _
  -- apply ent_star_top
  simp_all

@[aesop safe]
theorem var_intro'':
    (H ⊢ Q v) → SPHoare p Γ H (Expr.var n) Q := by sorry

@[aesop safe]
theorem assert_intro {v:Bool}:
    SPHoare p Γ
    [|True|]
    (.call (argTypes := [.bool]) h![] .unit (.builtin .assert) h![v])
    (fun _ => [|v|]) := by
  intro H
  unfold PHoare
  intros
  casesm* BigStep _ _ _ _ _ _
  cases_type Builtin.assert
  -- apply ent_star_top
  simp_all

@[aesop safe]
theorem assert_intro' {v:Bool}:
    SPHoare p Γ
    ([|v|] -⋆ Q ())
    (.call (argTypes := [.bool]) h![] .unit (.builtin .assert) h![v])
    Q := by sorry
  -- intro H
  -- unfold PHoare
  -- intros
  -- casesm* BigStep _ _ _ _ _ _, BigStepBuiltin _ _ _ _ _ _
  -- simp_all

-- @[aesop unsafe 1%]
theorem conseq_frame:
    SPHoare p Γ P e Q →
    (P' ⊢ P ⋆ H) →
    (∀ v, (Q v ⋆ H) ⊢ Q' v) →
    SPHoare p Γ P' e Q' := by sorry

-- @[aesop unsafe 1%]
theorem conseq:
    SPHoare p Γ P e Q →
    (P' ⊢ P) →
    (∀ v, Q v ⊢ Q' v) →
    SPHoare p Γ P' e Q' := by sorry

@[aesop unsafe 1%]
theorem ramified_frame {Q Q₁ : Tp.denote p tp → SLP p}:
    SPHoare p Γ H₁ e Q₁ →
    (∀v, H ⊢ (H₁ ⋆ (Q₁ v -⋆ (Q v)))) →
    SPHoare p Γ H e Q := by sorry


@[aesop safe]
theorem letIn_intro:
    SPHoare p Γ P e₁ Q →
    (∀v, SPHoare p Γ (Q v) (e₂ v) R) →
    SPHoare p Γ P (Expr.letIn e₁ e₂) R := by
  unfold SPHoare PHoare
  intro he hb H
  intros
  casesm BigStep _ _ _ _ _ _
  have := (he H _ _ _ (by assumption) (by assumption))
  cases this
  casesm ∃ _, _
  casesm* _ ∧ _
  apply_assumption
  apply_assumption
  all_goals assumption

@[aesop safe]
theorem seq_intro:
    SPHoare p Γ P e₁ (fun _ => Q) →
    SPHoare p Γ Q e₂ R →
    SPHoare p Γ P (e₁.seq e₂) R := by
  unfold SPHoare PHoare
  intros
  cases_type BigStep
  apply_assumption
  apply_assumption
  assumption
  assumption
  assumption

@[simp]
theorem lift_star_lift {P Q : Prop} : ((lift P : SLP p) ⋆ [|Q|]) = [|P ∧ Q|] := by
  unfold Lampe.star lift
  funext
  rw [eq_iff_iff]
  apply Iff.intro
  · intro_cases; subst_vars; simp_all
  · intro_cases; exists ∅; exists ∅; simp_all [Finmap.disjoint_empty]

@[simp]
theorem ent_lift_iff_implies {P Q : Prop} : (lift (p:=p) P ⊢ [|Q|]) = (P → Q) := by
  unfold ent lift
  funext
  rw [eq_iff_iff]
  apply Iff.intro
  · intro_cases; simp_all
  · intro_cases; simp_all

@[simp]
theorem lift_wand_lift_eq_imp {P Q : Prop} : ((lift P : SLP p) -⋆ [|Q|]) = [|P → Q|] := by
  sorry

nr_def weirdEq<I>(x : I, y : I) -> Unit {
  let a = #fresh() : I;
  #assert(#eq(a, x) : bool) : Unit;
  #assert(#eq(a, y) : bool) : Unit;
}

nr_def assert<>(x : bool) -> Unit {
  #assert(x) : Unit;
}

nr_def assert2<>(x : bool, y: bool) -> Unit {
  #assert(x):Unit;
  #assert(y):Unit;
}


example : SPHoare p Γ True (assert.fn.body _ h![] h![v]) (fun _ => [|v|]) := by
  unfold assert
  simp only
  apply letIn_intro
  apply var_intro
  intro
  apply ramified_frame
  apply assert_intro
  aesop



  -- aesop

example : SPHoare p Γ True (assert2.fn.body _ h![] h![a, b]) (fun _ => [|a ∧ b|]) := by
  unfold assert2
  simp only
  apply seq_intro
  apply letIn_intro
  apply var_intro
  intro
  apply ramified_frame
  apply assert_intro
  rotate_left
  apply letIn_intro
  apply var_intro'
  apply assert_intro'
  aesop

lemma Finmap.insert_eq_singleton_union [DecidableEq α] {ref : α}:
    m.insert ref v = Finmap.singleton ref v ∪ m := by rfl

@[simp]
lemma Finmap.singleton_disjoint_of_not_mem (hp : ref ∉ s):
    Finmap.Disjoint (Finmap.singleton ref v) s := by
  simp_all [Finmap.Disjoint]


nr_def simple_rw<>(x : bool) -> bool {
  let mut y = x;
  y
}

theorem ref_intro:
    SPHoare p Γ
    [|True|]
    (.call h![] [tp] tp.ref (.builtin .ref) h![v])
    (fun r => [r ↦ ⟨tp, v⟩]) := by
  unfold SPHoare PHoare
  intros
  cases_type BigStep
  cases_type Builtin.ref
  simp
  unfold star
  apply Exists.intro
  apply Exists.intro
  rotate_right
  rotate_right
  rotate_right
  apply And.intro
  rotate_left
  rw [Finmap.insert_eq_singleton_union]
  apply And.intro
  rfl
  simp_all [singleton]
  simp_all

theorem readRef_intro (hp : Q ⊢ [r ↦ ⟨tp, v⟩]):
    SPHoare p Γ
    [r ↦ ⟨tp, v⟩]
    (.call h![] [tp.ref] tp (.builtin .readRef) h![r])
    (fun v' => [|v' = v|] ⋆ [r ↦ ⟨tp, v⟩]) := by sorry

theorem frame:
    SPHoare p Γ P e Q →
    SPHoare p Γ (P ⋆ H) e (fun v => Q v ⋆ H) := by sorry

theorem conseq_right:
    SPHoare p Γ P e Q →
    (∀v, Q v ⊢ Q' v) →
    SPHoare p Γ P e Q' := by sorry

theorem ent_forget:
    (P ⋆ Q) ⊢ P := by sorry

theorem ent_pure_l:
    (P → (Q ⊢ R)) → ((P ⋆ Q) ⊢ R) := by sorry

lemma wand_intro: ((A ⋆ H) ⊢ B) → (H ⊢ (A -⋆ B)) := by sorry

example : SPHoare p Γ [|True|] (simple_rw.fn.body _ h![] h![x]) fun v => [|v = x|] := by
  simp only [simple_rw, Lampe.Expr.letMutIn]
  apply letIn_intro
  apply letIn_intro
  apply var_intro
  intro
  apply ramified_frame
  apply ref_intro
  · intro
    simp
    apply wand_intro
    rw [star_comm]
    apply ent_pure_l
    intro
    subst_vars
    apply ent_self
  · intro
    apply ramified_frame
    apply readRef_intro
    apply ent_self
    rotate_left
    intro


  intro

  rotate_left
  intro
  apply readRef_intro
  rotate_left

  intro
  rotate_left
  intro
  apply ramified_frame
  apply readRef_intro
  rotate_left; rotate_left; rotate_left; rotate_left; rotate_left
  apply letIn_intro
  apply var_intro
  intro
  apply conseq_frame
  apply ref_intro
  simp; apply ent_self
  rotate_left
  apply ent_self
  apply ent_self














nr_def simple_muts<>(x : Field) -> Field {
  let mut y = x;
  let mut z = x;
  z = z;
  y = z;
  y
}

example : SPHoare p Γ [|True|] (simple_muts.fn.body _ h![] h![x]) fun v => [|v = x|] := by
  simp only [simple_muts]
  apply letMutIn_intro
  aesop
  intros
  apply letMutIn_intro
  aesop
  intros
  apply seq_intro









/---
  aesop

  aesop
  apply conseq_frame

  apply var_intro
  aesop
  intros
  apply seq_intro
