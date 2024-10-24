import Lampe.Ast
-- import Lampe.Assignable
import Lampe.Tp
import Lampe.Data.Field
import Lampe.Tactic.IntroCases
import Lampe.Semantics
import Lampe.Syntax
import Lampe.State
import Lampe.SeparationLogic
import Mathlib

namespace Lampe

theorem omni_conseq:
    Omni p Γ st e Q →
    (∀ v, Q v → Q' v) →
    Omni p Γ st e Q' := by
  intro h
  induction h <;> try (
    intro
    constructor
    all_goals tauto
  )
  case callBuiltin =>
    cases_type Builtin
    tauto

def THoare
    {tp : Tp}
    (p : Prime)
    (Γ : Env)
    (P : SLP p)
    (e : Expr (Tp.denote p) tp)
    (Q : (tp.denote p) → SLP p): Prop :=
  ∀st, P st → Omni p Γ st e (fun r => match r with
    | none => True
    | some (st', v) => Q v st')

theorem THoare.consequence {p Γ tp}  {e : Expr (Tp.denote p) tp} {H₁ H₂ Q₁ Q₂}:
    (H₂ ⊢ H₁) →
    THoare p Γ H₁ e Q₁ →
    (∀ v, Q₁ v ⊢ Q₂ v) →
    THoare p Γ H₂ e Q₂ := by
  unfold THoare
  intros
  apply omni_conseq
  · tauto
  rintro (_ | _) <;> tauto

theorem THoare.var_intro {p Γ P tp} {n : Tp.denote p tp} {Q: Tp.denote p tp → SLP p}:
    (P ⊢ Q n) →
    THoare p Γ P (Expr.var n) Q := by
  unfold THoare SLP.entails
  tauto

theorem THoare.assert_intro {p Γ P} {v : Bool} {Q : Unit → SLP p}:
    (v ⋆ P ⊢ Q ()) → THoare p Γ P (.call h![] [.bool] .unit (.builtin .assert) h![v]) Q := by
  unfold THoare
  intros
  constructor
  unfold Builtin.assert
  cases v
  · constructor
    simp
  · constructor; apply_assumption; simp_all

def STHoare p Γ P e (Q : Tp.denote p tp → SLP p) := ∀H, THoare p Γ (P ⋆ H) e (fun v => ((Q v) ⋆ H) ⋆ ⊤)

theorem frame : STHoare p Γ P e Q → STHoare p Γ (P ⋆ H) e (fun v => Q v ⋆ H) := by
  unfold STHoare
  intro h H'
  have := h (H ⋆ H')
  simp_all [SLP.star_assoc]

theorem consequence_top {p tp} {e : Expr (Tp.denote p) tp} {H₁ H₂} {Q₁ Q₂ : Tp.denote p tp → SLP p}:
    (H₁ ⊢ H₂) → (∀ v, Q₂ v ⋆ ⊤ ⊢ Q₁ v ⋆ ⊤) → STHoare p Γ H₂ e Q₂ → STHoare p Γ H₁ e Q₁ := by
  unfold STHoare
  intro hHs hQs hE H
  apply THoare.consequence ?_ (hE H) ?_
  · apply SLP.star_mono_r
    tauto
  · intro
    rw [SLP.star_assoc, SLP.star_assoc]
    conv in (occs := *) (H ⋆ ⊤) => rw [SLP.star_comm]
    rw [←SLP.star_assoc, ←SLP.star_assoc]
    apply SLP.star_mono_r
    apply_assumption

@[aesop unsafe 1%]
theorem ramified_frame_top {Q₁ Q₂ : Tp.denote p tp → SLP p}:
    STHoare p Γ H₁ e Q₁ →
    (H₂ ⊢ (H₁ ⋆ (∀∀v, Q₁ v -⋆ Q₂ v ⋆ ⊤))) →
    STHoare p Γ H₂ e Q₂ := by
  intro hST hHE
  apply consequence_top
  rotate_left
  rotate_left
  apply frame
  rotate_left
  assumption
  apply_assumption
  intro v
  apply SLP.entails_trans
  rw [SLP.star_assoc, SLP.star_comm, SLP.star_assoc]
  exact SLP.forall_star
  apply SLP.forall_left
  rw [SLP.star_comm, SLP.star_assoc, SLP.star_comm]
  apply SLP.entails_trans
  apply SLP.star_mono_r
  apply SLP.wand_cancel
  rw [SLP.star_assoc]
  simp
  tauto

@[aesop unsafe 50%]
theorem var_intro :
    STHoare p Γ ⟦⟧ (Expr.var n) (fun v => v = n) := by
  intro
  apply THoare.var_intro
  simp

@[aesop safe]
theorem assert_intro {v:Bool}:
    STHoare p Γ
    ⟦⟧
    (.call (argTypes := [.bool]) h![] .unit (.builtin .assert) h![v])
    (fun _ => v) := by
  intro H
  apply THoare.assert_intro
  simp [←SLP.star_assoc]

theorem omni_frame {p Γ tp st₁ st₂} {e : Expr (Tp.denote p) tp} {Q}:
    Omni p Γ st₁ e Q →
    st₁.Disjoint st₂ →
    Omni p Γ (st₁ ∪ st₂) e (fun st => match st with
      | some (st', v) => ((fun st => Q (some (st, v))) ⋆ (fun st => st = st₂)) st'
      | none => Q none
    ) := by
  intro h
  induction h with
  | litField hq
  | litFalse hq
  | litTrue hq
  | var hq =>
    intro
    constructor
    repeat apply Exists.intro
    tauto
  | letIn _ _ hN ihE ihB =>
    intro
    constructor
    apply ihE
    assumption
    · intro _ _ h
      cases h
      casesm* ∃ _, _, _∧_
      subst_vars
      apply ihB
      assumption
      assumption
    · simp_all
  | callBuiltin hq =>
    cases_type Builtin
    tauto
  | callDecl _ _ _ _ _ ih =>
    intro
    constructor
    all_goals (try assumption)
    tauto

@[aesop safe]
theorem letIn_intro:
    STHoare p Γ P e₁ Q →
    (∀v, STHoare p Γ (Q v) (e₂ v) R) →
    STHoare p Γ P (Expr.letIn e₁ e₂) R := by
  unfold STHoare THoare
  intro he hb H
  intros
  constructor
  apply_assumption
  apply_assumption
  intro _ _ h
  simp only at h
  cases h
  casesm* ∃ _, _, _∧_
  subst_vars
  apply omni_conseq
  apply omni_frame
  apply_assumption
  apply_assumption
  apply_assumption
  intro v
  cases v with
  | none => simp
  | some v =>
    cases v
    simp only
    rintro ⟨_, _, _, _, h, _⟩
    rcases h with ⟨_, _, _, _, _, _⟩
    subst_vars
    apply Exists.intro
    apply Exists.intro
    apply And.intro
    rotate_left
    apply And.intro
    rotate_left
    apply And.intro
    assumption
    simp [SLP.top]
    rotate_left
    rotate_left
    rw [Finmap.union_assoc]
    intro _ h
    intro h₁
    cases Finmap.mem_union.mp h₁
    · simp only [Finmap.Disjoint] at *
      tauto
    · simp only [Finmap.Disjoint, Finmap.mem_union] at *
      tauto
  simp

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


example : STHoare p Γ True (assert.fn.body _ h![] h![v]) (fun _ => ⟦v⟧) := by
  unfold assert
  aesop
  aesop
  aesop
  simp only
  apply letIn_intro
  apply var_intro
  intro
  apply ramified_frame_top
  apply assert_intro
  aesop



  -- aesop

example : STHoare p Γ True (assert2.fn.body _ h![] h![a, b]) (fun _ => [|a ∧ b|]) := by
  unfold assert2
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


nr_def simple_rw<>(x : bool) -> bool {
  let mut y = x;
  y
}

theorem ref_intro:
    STHoare p Γ
    ⟦⟧
    (.call h![] [tp] tp.ref (.builtin .ref) h![v])
    (fun r => [r ↦ ⟨tp, v⟩]) := by
  unfold STHoare THoare
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

theorem ent_pure_l:
    (P → (Q ⊢ R)) → ((P ⋆ Q) ⊢ R) := by sorry

theorem ent_pure_r:
    (H ⊢ H') → P → (H ⊢ (H' ⋆ P)) := by sorry

lemma wand_intro: ((A ⋆ H) ⊢ B) → (H ⊢ (A -⋆ B)) := by sorry

lemma self_ent_self_star:
  (H₁ ⊢ H₂) → (True ⊢ (H₃)) → (H₁ ⊢ (H₂ ⋆ H₃)) := by sorry

lemma ent_self_top:
    (H₁ ⊢ (H₁ ⋆ top)) := by
  intro st h
  apply Exists.intro st
  apply Exists.intro ∅
  simp_all [Finmap.Disjoint.symm, Finmap.disjoint_empty]

lemma ent_top: H ⊢ top := by intro st; unfold top; tauto

example : STHoare p Γ ⟦⟧ (simple_rw.fn.body _ h![] h![x]) fun v => v = x := by
  simp only [simple_rw, Lampe.Expr.letMutIn]
  aesop
  aesop

  apply letIn_intro
  apply letIn_intro
  apply var_intro
  intro
  apply ramified_frame_top
  apply ref_intro
  · intro
    simp
    apply wand_intro
    rw [star_comm]
    apply ent_pure_l
    intro
    subst_vars
    apply ent_self_top
  · intro
    apply ramified_frame_top
    apply readRef_intro
    apply ent_self
    rotate_left
    intro
    apply self_ent_self_star
    apply ent_self
    apply wand_intro
    rw [star_assoc]
    apply ent_pure_l
    intro
    subst_vars
    simp
    apply ent_top

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
