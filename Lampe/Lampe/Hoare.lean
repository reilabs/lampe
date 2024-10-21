import Lampe.Ast
-- import Lampe.Assignable
import Lampe.Tp
import Lampe.Data.Field
import Lampe.Tactic.IntroCases
import Lampe.Semantics
import Lampe.Syntax
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

def PHoare
    {tp : Tp}
    (Γ : Env)
    (P : SLP p)
    (e : Expr (Tp.denote p) tp)
    (Q : (tp.denote p) → SLP p): Prop :=
  ∀st st' v, P st → BigStep p Γ st e st' v → Q v st'

def PHoare.Builtin
    (tps : List Tp)
    (tp : Tp)
    (P : SLP p)
    (builtin : Builtin)
    (args : HList (Tp.denote p) tps)
    (Q : tp.denote p → SLP p)
    : Prop
  := ∀st v, P st → BigStepBuiltin p tps tp builtin args v → Q v st

namespace PHoare

@[aesop safe]
theorem var_intro:
    PHoare p Γ (P n) (Expr.var n) P := by
  unfold PHoare
  intros
  casesm* BigStep _ _ _ _ _ _
  simp_all

@[aesop unsafe 99%]
theorem var_intro':
    (∀ st, P st → Q n st) → PHoare p Γ P (Expr.var n) Q := by
  unfold PHoare
  intros
  casesm* BigStep _ _ _ _ _ _
  simp_all

-- @[aesop safe]
-- theorem var_intro' {n : Tp.denote p tp} {P}:
--     PHoare p Γ P (Expr.var n) (fun v st => v = n ∧ P st) := by
--   unfold PHoare
--   intros
--   casesm* BigStep _ _ _ _ _ _
--   simp_all

@[aesop safe]
theorem letIn_intro:
    PHoare p Γ P e₁ Q →
    (∀v, PHoare p Γ (Q v) (e₂ v) R) →
    PHoare p Γ P (Expr.letIn e₁ e₂) R := by
  intro he₁ he₂ st st' v hP hBS
  cases hBS
  repeat (first | apply_assumption | assumption)

@[aesop safe]
theorem seq_intro:
    PHoare p Γ P e₁ (fun _ => Q) →
    PHoare p Γ Q e₂ R →
    PHoare p Γ P (Expr.seq e₁ e₂) R := by
  intro hl hr st st' v hP hBS
  cases hBS
  apply hr
  apply hl
  all_goals assumption

theorem lit_u_intro {Q : U s → SLP p}:
    PHoare p Γ (Q ↑n) (Expr.lit (.u s) n) Q := by
  intro _; intros
  casesm* BigStep _ _ _ _ _ _
  simp_all

@[aesop safe]
theorem callBuiltin_intro:
    PHoare.Builtin p tps tp P builtin args Q →
    PHoare p Γ P (Expr.call HList.nil tp (.builtin builtin) args) Q := by
  unfold PHoare.Builtin PHoare
  intros
  casesm* BigStep _ _ _ _ _ _
  simp_all

@[aesop safe]
theorem Builtin.assert_intro' {v:Bool}:
    PHoare.Builtin p [.bool] .unit (fun st => v → P () st) Builtin.assert h![v] P := by
  unfold PHoare.Builtin
  intros
  casesm* BigStepBuiltin _ _ _ _ _ _
  simp_all

@[aesop safe]
theorem Builtin.eq_f_intro {a b}:
    PHoare.Builtin p [.field, .field] .bool (P (a == b)) Builtin.eq h![a,b] P := by
  unfold PHoare.Builtin
  intros
  casesm* BigStepBuiltin _ _ _ _ _ _
  simp_all

@[aesop unsafe 99%]
theorem Builtin.eq_f_intro' {a b}:
    (∀ st, P st → Q (a == b) st) →
    PHoare.Builtin p [.field, .field] .bool P Builtin.eq h![a,b] Q := by
  unfold PHoare.Builtin
  intros
  casesm* BigStepBuiltin _ _ _ _ _ _
  simp_all

@[aesop safe]
theorem Builtin.fresh_intro':
    PHoare.Builtin p [] tp P Builtin.fresh h![] (fun _ => P) := by
  unfold PHoare.Builtin
  intros
  casesm* BigStepBuiltin _ _ _ _ _ _
  apply_assumption

-- @[aesop safe]
theorem strengthen_pre:
    (∀st, P' st → P st) →
    PHoare p Γ P e Q →
    PHoare p Γ P' e Q := by
  unfold PHoare
  intros
  repeat apply_assumption

theorem Builtin.strengthen_pre {P P' : SLP p}:
    (∀ st, P' st → P st) →
    PHoare.Builtin p tps tp P builtin args Q →
    PHoare.Builtin p tps tp P' builtin args Q := by
  unfold PHoare.Builtin
  intros
  repeat apply_assumption

@[aesop unsafe 1%]
theorem Builtin.weaken_post {Q Q' : tp.denote p → SLP p}:
    PHoare.Builtin p tps tp P builtin args Q →
    (∀ v st, Q v st → Q' v st) →
    PHoare.Builtin p tps tp P builtin args Q' := by
  unfold PHoare.Builtin
  intros
  repeat apply_assumption

end PHoare

end Lampe

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

open Lampe

example : PHoare p Γ (fun _ => True) (assert.fn.body _ h![] h![v]) (fun _ _ => v) := by
  unfold assert
  aesop

example : PHoare p Γ (fun _ => True) (assert2.fn.body _ h![] h![a, b]) (fun _ _ => a ∧ b) := by
  unfold assert2
  aesop

example : PHoare p Γ (fun _ => True) (weirdEq.fn.body _ h![.field] h![a, b]) (fun _ _ => (a = b)) := by
  unfold weirdEq
  simp only
  apply PHoare.letIn_intro
  apply PHoare.callBuiltin_intro
  apply PHoare.Builtin.fresh_intro'
  intro
  apply PHoare.seq_intro
  repeat apply PHoare.letIn_intro
  apply PHoare.var_intro'
  rotate_left
  intro
  apply PHoare.letIn_intro
  apply PHoare.var_intro'
  rotate_left
  intro
  apply PHoare.callBuiltin_intro
  apply PHoare.Builtin.eq_f_intro
  rotate_left
  intro
  apply PHoare.callBuiltin_intro
  apply PHoare.Builtin.assert_intro'
  repeat apply PHoare.letIn_intro
  apply PHoare.var_intro
  intro
  repeat apply PHoare.letIn_intro
  apply PHoare.var_intro'
  rotate_left
  intro
  apply PHoare.callBuiltin_intro
  apply PHoare.Builtin.eq_f_intro
  rotate_left
  intro
  apply PHoare.callBuiltin_intro
  apply PHoare.Builtin.assert_intro'
  sorry



def SPHoare p Γ P e (Q : Tp.denote p tp → SLP p) := ∀H, PHoare p Γ (P ⋆ H) e (fun v => (Q v) ⋆ H)

@[aesop safe]
theorem var_intro':
    SPHoare p Γ (P n) (Expr.var n) P := by
  intro H
  have {n}: (P n ⋆ H) = (fun n => P n ⋆ H) n := by rfl
  rw [this]
  apply PHoare.var_intro (P := fun n => P n ⋆ H)

@[aesop safe]
theorem var_intro :
    SPHoare p Γ [|True|] (Expr.var n) (fun v => [|v = n|]) := by sorry

@[aesop safe]
theorem assert_intro {v:Bool}:
    SPHoare p Γ
    [|True|]
    (.call (argTypes := [.bool]) h![] .unit (.builtin .assert) h![v])
    (fun _ => [|v|]) := by
  intro H
  unfold PHoare
  intros
  casesm* BigStep _ _ _ _ _ _, BigStepBuiltin _ _ _ _ _ _
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
    (∀ v, H ⊢ (H₁ ⋆ (Q₁ v -⋆ Q v))) →
    SPHoare p Γ H e Q := by sorry

@[aesop safe]
theorem letIn_intro:
    SPHoare p Γ P e₁ Q →
    (∀v, SPHoare p Γ (Q v) (e₂ v) R) →
    SPHoare p Γ P (Expr.letIn e₁ e₂) R := by
  unfold SPHoare PHoare
  intros
  casesm BigStep _ _ _ _ _ _
  apply_assumption
  apply_assumption
  assumption
  assumption
  assumption

@[aesop safe]
theorem seq_intro:
    SPHoare p Γ P e₁ (fun _ => Q) →
    SPHoare p Γ Q e₂ R →
    SPHoare p Γ P (e₁.seq e₂) R := by
  unfold SPHoare
  intros
  apply PHoare.seq_intro <;> apply_assumption

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
  aesop
  aesop
  apply ramified_frame
  apply assert_intro
  rotate_left
  apply var_intro'
  apply assert_intro'
  aesop

lemma Finmap.insert_eq_singleton_union [DecidableEq α] {ref : α}:
    m.insert ref v = singleton ref v ∪ m := by rfl

@[simp]
lemma Finmap.singleton_disjoint_of_not_mem (hp : ref ∉ s):
    Finmap.Disjoint (singleton ref v) s := by
  simp_all [Disjoint]

@[aesop unsafe 99%]
theorem letMutIn_intro {e₁ : Expr (Tp.denote p) tp}:
    SPHoare p Γ P e₁ Q →
    (∀ v r, SPHoare p Γ (Q v ⋆ [r ↦ ⟨tp, v⟩]) (e₂ r) R) →
    SPHoare p Γ P (Expr.letMutIn e₁ e₂) R := by
  intro hE hR H
  unfold PHoare
  simp only
  intros
  casesm BigStep _ _ _ _ _ _
  rename_i ps ref hr v _ _
  apply hR v ref _ (ps.insert ref ⟨_, v⟩)
  · rw [star_assoc, star_comm, star_assoc]
    rw [Finmap.insert_eq_singleton_union]
    exists (Finmap.singleton ref ⟨_, v⟩)
    exists ps
    apply And.intro (by simp_all)
    apply And.intro (by rfl)
    apply And.intro (by rfl)
    rw [star_comm]
    apply hE <;> assumption
  · assumption

@[aesop unsafe 99%]
theorem writeRef_intro {e₁ : Expr (Tp.denote p) tp}:
    SPHoare p Γ (P ⋆ [ref ↦ v₀]) e₁ (fun v => Q v ⋆ [ref ↦ v₁]) →
    (∀ v, SPHoare p Γ (P ⋆ [ref ↦ v₀]) (Expr.writeRef)
-- theorem frame:
--     PHoare p Γ P e Q →


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
