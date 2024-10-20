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

instance {p}: Coe Prop (SLP p) := ⟨lift⟩

notation "[|" x "|]" => lift x

notation l " ⋆ " r => star l r

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

def PHoare.Args
    {tps : List Tp}
    (Γ : Env)
    (P : SLP p)
    (es : HList (Expr (Tp.denote p)) tps)
    (Q : HList (Tp.denote p) tps → SLP p): Prop :=
  ∀st st' vs, P st → BigStepArgs p Γ st es st' vs → Q vs st'

def PHoare.Builtin
    (tps : List Tp)
    (tp : Tp)
    (P :  HList (Tp.denote p) tps → SLP p)
    (builtin : Builtin)
    (Q : tp.denote p → SLP p)
    : Prop
  := ∀st args v, P args st → BigStepBuiltin p tps tp builtin args v → Q v st

namespace PHoare

@[aesop safe]
theorem Args.nil_intro {p Γ Q}:
    PHoare.Args p Γ (Q h![]) h![] Q := by
  unfold PHoare.Args
  intros
  casesm* _ ∧ _, BigStepArgs _ _ _ _ _ _
  simp_all

@[aesop safe]
theorem Args.nil_intro':
    PHoare.Args p Γ P h![] (fun _ => P) := by
  unfold PHoare.Args
  intros
  casesm* BigStepArgs _ _ _ _ _ _
  simp_all

theorem Args.nil_intro'':
    (∀ st, P st → Q h![] st) →
    PHoare.Args p Γ P h![] Q := by
  unfold PHoare.Args
  intros
  casesm* BigStepArgs _ _ _ _ _ _
  repeat apply_assumption

theorem Args.cons_intro (e : Expr (Tp.denote p) tp) (es : HList (Expr (Tp.denote p)) tps) {Γ P Q}:
    PHoare p Γ P e Q →
    (∀v, PHoare.Args p Γ (Q v) es (fun vs => R (HList.cons v vs))) →
    PHoare.Args p Γ P (HList.cons e es) R := by
  rintro he hes st st' vs hP hAs
  cases hAs
  simp only [Args] at hes
  apply hes
  simp only [PHoare] at he
  apply he
  all_goals assumption

@[aesop unsafe 99%]
theorem Args.cons_intro'
  (e : Expr (Tp.denote p) tp)
  (es : HList (Expr (Tp.denote p)) tps)
  {Γ P Q} {R : Tp.denote p tp → HList (Tp.denote p) tps → SLP p}:
    PHoare p Γ P e Q →
    (∀v, PHoare.Args p Γ (Q v) es (R v)) →
    PHoare.Args p Γ P (HList.cons e es) (fun (HList.cons v vs) => R v vs) := by
  rintro he hes st st' vs hP hAs
  cases hAs
  simp only [Args] at hes
  apply hes
  simp only [PHoare] at he
  apply he
  all_goals assumption


@[aesop safe]
theorem var_intro:
    PHoare p Γ (P n) (Expr.var n) P := by
  unfold PHoare
  intros
  casesm* BigStep _ _ _ _ _ _
  simp_all

@[aesop safe]
theorem var_intro':
    PHoare p Γ P (Expr.var n) (fun v st => v = n ∧ P st) := by
  unfold PHoare
  intros
  casesm* BigStep _ _ _ _ _ _
  simp_all

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
theorem callBuiltin_intro {R} {Q : HList (Tp.denote p) tps → SLP p}:
    PHoare.Args p Γ P es Q →
    PHoare.Builtin p tps tp Q builtin R →
    PHoare p Γ P (Expr.call HList.nil tp (.builtin builtin) es) R := by
  intro hA hB st st' v hP hBS
  cases hBS
  apply hB
  apply hA
  all_goals assumption

-- @[aesop safe]
theorem Builtin.assert_intro {P : HList (Tp.denote p) [.bool] → SLP p}:
    PHoare.Builtin p [.bool] .unit (fun args st => args = h![v] ∧ P args st) Builtin.assert (fun _ st => v = true ∧ P h![v] st) := by
  unfold PHoare.Builtin
  intros
  casesm* HList _ _
  casesm* BigStepBuiltin _ _ _ _ _ _
  simp_all

-- @[aesop safe]
theorem Builtin.assert_intro':
    PHoare.Builtin p [.bool] .unit (fun args st => args = h![v]) Builtin.assert (fun _ st => v = true) := by
  unfold PHoare.Builtin
  intros
  casesm* HList _ _
  casesm* BigStepBuiltin _ _ _ _ _ _
  simp_all

@[aesop safe]
theorem Builtin.assert_intro'' {P : HList (Tp.denote p) [.bool] → SLP p}:
    PHoare.Builtin p [.bool] .unit P Builtin.assert (fun _ => P h![true]) := by
  unfold PHoare.Builtin
  intros
  casesm* BigStepBuiltin _ _ _ _ _ _
  assumption

@[aesop unsafe 99%]
theorem Builtin.eq_f_intro {a b}:
    (∀ as st, P as st → as = h![a,b]) →
    PHoare.Builtin p [.field, .field] .bool P Builtin.eq (fun v _ => v = (a == b)) := by
  unfold PHoare.Builtin
  intro h
  intros
  casesm* BigStepBuiltin _ _ _ _ _ _
  have := h _ _ (by assumption)
  simp_all

@[aesop unsafe 99%]
theorem Builtin.eq_f_intro':
    PHoare.Builtin p [.field, .field] .bool (fun h![a, b] => Q (a == b)) .eq Q := by
  unfold PHoare.Builtin
  intros
  casesm* HList _ _
  casesm* BigStepBuiltin _ _ _ _ _ _
  simp_all

@[aesop safe]
theorem Builtin.fresh_intro:
    PHoare.Builtin p [] tp (fun _ st => ∀v, Q v st) Builtin.fresh Q := by
  unfold PHoare.Builtin
  intros
  casesm* HList _ _
  casesm* BigStepBuiltin _ _ _ _ _ _
  apply_assumption

@[aesop safe]
theorem Builtin.fresh_intro':
    PHoare.Builtin p [] tp P Builtin.fresh (fun _ => P h![]) := by
  unfold PHoare.Builtin
  intros
  casesm* HList _ _
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

theorem Builtin.strengthen_pre {P P' : HList (Tp.denote p) tps → SLP p}:
    (∀ args st, P' args st → P args st) →
    PHoare.Builtin p tps tp P builtin Q →
    PHoare.Builtin p tps tp P' builtin Q := by
  unfold PHoare.Builtin
  intros
  repeat apply_assumption

@[aesop unsafe 1%]
theorem Builtin.weaken_post {Q Q' : tp.denote p → SLP p}:
    PHoare.Builtin p tps tp P builtin Q →
    (∀ v st, Q v st → Q' v st) →
    PHoare.Builtin p tps tp P builtin Q' := by
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

example : PHoare p Γ (fun _ => True) (assert.fn.body _ h![] h![v]) (fun _ _ => v = true) := by
  unfold assert
  aesop

-- set_option trace.aesop true

example : PHoare p Γ (fun _ => True) (assert2.fn.body _ h![] h![a, b]) (fun _ _ => a ∧ b) := by
  unfold assert2
  aesop (add 10% cases HList) (config := {maxRuleApplications := 10})
  aesop (add 10% cases HList) (config := {maxRuleApplications := 10})
  aesop (add 10% cases HList) (config := {maxRuleApplications := 10})
  aesop (add 10% cases HList) (config := {maxRuleApplications := 10})
  aesop (add 10% cases HList) (config := {maxRuleApplications := 10})


example : PHoare p Γ (fun _ => True) (weirdEq.fn.body _ h![.field] h![a, b]) (fun _ _ => (a = b)) := by
  unfold weirdEq

  aesop (add 10% cases HList) (config := {maxRuleApplications := 10})
  aesop (add 10% cases HList) (config := {maxRuleApplications := 10})
  aesop (add 10% cases HList) (config := {maxRuleApplications := 10})
  apply PHoare.Args.cons_intro'
  aesop (add 10% cases HList) (config := {maxRuleApplications := 10})
  aesop (add 10% cases HList) (config := {maxRuleApplications := 10})
  apply PHoare.Builtin.eq_f_intro
  aesop (add 10% cases HList) (config := {maxRuleApplications := 10})
  aesop (add 10% cases HList) (config := {maxRuleApplications := 10})
  aesop (add 10% cases HList) (config := {maxRuleApplications := 10})
  aesop (add 10% cases HList) (config := {maxRuleApplications := 10})
  apply PHoare.Args.cons_intro'
  aesop (add 10% cases HList) (config := {maxRuleApplications := 10})
  aesop (add 10% cases HList) (config := {maxRuleApplications := 10})
  apply PHoare.Builtin.eq_f_intro
  aesop (add 10% cases HList) (config := {maxRuleApplications := 10})
  aesop (add 10% cases HList) (config := {maxRuleApplications := 10})
  aesop (add 10% cases HList) (config := {maxRuleApplications := 10})

def SPHoare p Γ P e (Q : Tp.denote p tp → SLP p) := ∀H, PHoare p Γ (P ⋆ H) e (fun v => (Q v) ⋆ H)
def SPHoare.Args p Γ P e (Q : HList (Tp.denote p) tps → SLP p) := ∀H, PHoare.Args p Γ (P ⋆ H) e (fun v => (Q v) ⋆ H)
def SPHoare.Builtin p tps tp (P: HList (Tp.denote p) tps → SLP p) e (Q : Tp.denote p tp → SLP p) := ∀H, PHoare.Builtin p tps tp (fun as => P as ⋆ H) e (fun v => Q v ⋆ H)

@[aesop safe]
theorem callBuiltin_intro {R} {Q : HList (Tp.denote p) tps → SLP p}:
    SPHoare.Args p Γ P es Q →
    SPHoare.Builtin p tps tp Q builtin R →
    SPHoare p Γ P (Expr.call HList.nil tp (.builtin builtin) es) R := by
  intro hA hB H
  aesop

@[aesop unsafe 99%]
theorem Args.cons_intro
  (e : Expr (Tp.denote p) tp)
  (es : HList (Expr (Tp.denote p)) tps)
  {Γ P Q} {R : Tp.denote p tp → HList (Tp.denote p) tps → SLP p}:
    SPHoare p Γ P e Q →
    (∀v, SPHoare.Args p Γ (Q v) es (R v)) →
    SPHoare.Args p Γ P (HList.cons e es) (fun (HList.cons v vs) => R v vs) := by
  intro hE hA H
  simp only
  have {x: HList (Tp.denote p) (tp :: tps)} :
      Lampe.star (match x with | HList.cons v vs => R v vs) H =
      (match x with | HList.cons v vs => Lampe.star (R v vs) H) := by
    cases x
    rfl
  simp_rw [this]
  aesop

-- @[aesop safe]
-- theorem var_intro:
--     SPHoare p Γ (P n) (Expr.var n) P := by
--   intro H
--   have {n}: (P n ⋆ H) = (fun n => P n ⋆ H) n := by rfl
--   rw [this]
--   apply PHoare.var_intro (P := fun n => P n ⋆ H)

@[aesop safe]
theorem var_intro:
    SPHoare p Γ True (Expr.var n) (fun v => [|v = n|]) := by
  intro H
  unfold PHoare
  intros
  casesm* BigStep _ _ _ _ _ _
  simp_all

@[aesop safe]
theorem nil_intro:
    SPHoare.Args p Γ [|True|] h![] (fun _ => [|True|]) := by
  intro H
  unfold PHoare.Args
  intros
  casesm* BigStepArgs _ _ _ _ _ _
  simp_all

@[aesop safe]
theorem Builtin.assert_intro {P : HList (Tp.denote p) [.bool] → SLP p}:
    SPHoare.Builtin p [.bool] .unit P Builtin.assert (fun _ => P h![true]) := by
  intro h
  unfold PHoare.Builtin
  intros
  casesm* BigStepBuiltin _ _ _ _ _ _
  assumption

@[aesop unsafe 1%]
theorem Args.conseq_frame:
    SPHoare.Args p Γ P e Q →
    (P' ⊢ P ⋆ H) →
    (∀ v, (Q v ⋆ H) ⊢ Q' v) →
    SPHoare.Args p Γ P' e Q' := by sorry

@[aesop unsafe 1%]
theorem conseq_frame:
    SPHoare p Γ P e Q →
    (P' ⊢ P ⋆ H) →
    (∀ v, (Q v ⋆ H) ⊢ Q' v) →
    SPHoare p Γ P' e Q' := by sorry

@[aesop unsafe 1%]
theorem SPHoare.Builtin.weaken_post:
    SPHoare.Builtin p tps tp P e Q →
    (∀ v, Q v ⊢ Q' v) →
    SPHoare.Builtin p tps tp P e Q' := by sorry

example : SPHoare p Γ True (assert.fn.body _ h![] h![v]) (fun _ => [|v|]) := by
  unfold assert
  aesop

lemma Finmap.insert_eq_singleton_union [DecidableEq α] {ref : α}:
    m.insert ref v = singleton ref v ∪ m := by rfl

@[simp]
lemma Finmap.singleton_disjoint_of_not_mem (hp : ref ∉ s):
    Finmap.Disjoint (singleton ref v) s := by
  simp_all [Disjoint]

@[aesop unsafe 99%]
theorem seq_intro:
    SPHoare p Γ P e₁ (fun _ => Q) →
    SPHoare p Γ Q e₂ R →
    SPHoare p Γ P (e₁.seq e₂) R := by
  unfold SPHoare
  intros
  apply PHoare.seq_intro <;> apply_assumption

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
    (∀ v, SPHoare p Γ (P ⋆ [ref ↦ v₀])
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
