import Lampe.Ast
import Lampe.Hoare.SepTotal
import Lampe.Hoare.Total
import Lampe.Semantics
import Lampe.Tactic.SL
import Lampe.Tp
import Batteries

namespace Lampe

namespace Env

@[simp]
lemma append_notation_eq {Γₗ Γᵣ : Env} : Γₗ ++ Γᵣ = Γₗ.append Γᵣ:= by
  rfl

@[trans]
lemma subset_transitive {Γ₁ Γ₂ Γ₃ : Env} : Γ₁ ⊆ Γ₂ → Γ₂ ⊆ Γ₃ → Γ₁ ⊆ Γ₃ := by
  rintro ⟨h₁, h₂⟩ ⟨h₃, h₄⟩
  constructor
  . trans Γ₂.functions
    assumption
    assumption
  . trans Γ₂.traits
    assumption
    assumption

lemma subset_append_left {Γₗ Γᵣ : Env} : Γₗ ⊆ Γₗ ++ Γᵣ := by
  constructor
  . simp [Env.append]
  . simp [Env.append]

lemma subset_append_right {Γₗ Γᵣ : Env} : Γᵣ ⊆ Γₗ ++ Γᵣ := by
  constructor
  . simp [Env.append]
  . simp [Env.append]

lemma subset_append_of_subset_left {Γᵢ Γₗ Γᵣ : Env} : Γᵢ ⊆ Γₗ → Γᵢ ⊆ Γₗ ++ Γᵣ := by
  rintro ⟨h₁, h₂⟩
  constructor
  . simp [Env.append, h₁]
  . simp [Env.append, h₂]

lemma subset_append_of_subset_right {Γᵢ Γₗ Γᵣ : Env} : Γᵢ ⊆ Γᵣ → Γᵢ ⊆ Γₗ ++ Γᵣ := by
  rintro ⟨h₁, h₂⟩
  constructor
  . simp [Env.append, h₁]
  . simp [Env.append, h₂]

lemma append_subset {Γ₁ Γ₂ Γ₃ : Env} : Γ₁ ++ Γ₂ ⊆ Γ₃ ↔ Γ₁ ⊆ Γ₃ ∧ Γ₂ ⊆ Γ₃ := by
  constructor
  . intro h
    constructor
    . have := @subset_append_left Γ₁ Γ₂
      apply subset_transitive this h
    . have := @subset_append_right Γ₁ Γ₂
      apply subset_transitive this h
  . rintro ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩
    simp [Env.append]
    constructor
    . simp_all
    . simp_all

lemma subset_left_subset_of_append {Γᵢ Γₗ Γᵣ : Env} : Γᵢ ⊆ Γₗ → Γᵢ ++ Γᵣ ⊆ Γₗ ++ Γᵣ := by
  intro h
  apply append_subset.mpr
  constructor
  . have := @subset_append_left Γₗ Γᵣ
    apply subset_transitive h this
  . apply subset_append_right

lemma subset_right_subset_of_append {Γᵢ Γₗ Γᵣ : Env} : Γᵢ ⊆ Γᵣ → Γᵣ ++ Γᵢ ⊆ Γₗ ++ Γᵣ := by
  intro h
  apply append_subset.mpr
  constructor
  . apply subset_append_right
  . have := @subset_append_right Γₗ Γᵣ
    apply subset_transitive h this

end Env

namespace Omni

theorem TraitResolvable.env_mono {Γ₁ Γ₂ : Env} (h_sub: Γ₁ ⊆ Γ₂) :
    TraitResolvable Γ₁ t → TraitResolvable Γ₂ t := by
  intro h
  induction h
  constructor
  · apply h_sub.2
    assumption
  all_goals assumption

theorem TraitResolution.env_mono {Γ₁ Γ₂ : Env} (h_sub: Γ₁ ⊆ Γ₂) :
    TraitResolution Γ₁ t impl → TraitResolution Γ₂ t impl := by
  intro h
  induction h
  constructor
  · apply h_sub.2
    assumption
  any_goals assumption
  · intros
    apply TraitResolvable.env_mono h_sub
    tauto

-- States that our any theorem over our Omnisemantics that is valid for any environment Γ₂ that
-- contains the environment Γ₁ for which the theorem was originally proven.
--
-- In detail:
--
-- - `p` is the value of the field prime under which the proof should hold.
-- - `Γ₁` is the "inner" environment, namely the one for which a proof of the Hoare triple already
--   exists, while `Γ₂` is the "outer" environment, the one for which we want our existing proof to
--   hold.
-- - `st` is the state of the program before execution of the provided `expr`.
-- - `expr` is the program expression to be "executed" in both cases.
-- - `Q` represents the postcondition for execution, where it is `some` after successful execution
--   and `none` otherwise. It is a predicate to help represent the explicit non-determinism of our
--   semantics. Our postcondition is now a _set_, modeled as a selector. The interpretation is that
--   we end up in `Q` no matter who controls the non-determinism.
--
-- See the documentation for `Omni` for more detail.
theorem is_monotonic
    {p : Prime}
    {Γ₁ Γ₂ : Env}
    {st : State p}
    {expr : Expr (Tp.denote p) tp}
    {Q : Option (State p × Tp.denote p tp) → Prop}
    (inner_sub_outer : Γ₁ ⊆ Γ₂)
  : Omni p Γ₁ st expr Q → Omni p Γ₂ st expr Q := by
  intro h
  induction h

  any_goals (constructor; (repeat (first | intro _ | apply_assumption)); done)

  case callLambda =>
    apply Omni.callLambda <;> repeat apply_assumption

  case loopNext =>
    apply Omni.loopNext <;> repeat apply_assumption

  case callDecl =>
    apply Omni.callDecl

    case _ : _ ∈ _ =>
      apply inner_sub_outer.1
      assumption

    all_goals repeat apply_assumption

  case callTrait =>
    apply Omni.callTrait
    assumption
    apply TraitResolution.env_mono inner_sub_outer
    any_goals repeat apply_assumption

end Omni

namespace STHoare

-- States that a given theorem on a Hoare Triple is valid for any environment Γ₂ that contains the
-- environment Γ₁ for which the theorem was originally proven.
--
-- In detail:
--
-- - `p` is the value of the field prime under which the proof should hold.
-- - `Γ₁` is the "inner" environment, namely the one for which a proof of the Hoare triple already
--   exists, while `Γ₂` is the "outer" environment, the one for which we want our existing proof to
--   hold.
-- - `pre` is the precondition for our Hoare triples, namely the state in which our program is
--   before executing `expr`.
-- - `expr` is the program expression to be "executed" in both cases.
-- - `post` is the postcondition for our Hoare triples, namely the state in which our program will
--   end up if `expr` evaluates.
--
-- See the documentation for `STHoare` for more detail.
theorem is_monotonic
    {p : Prime}
    {Γ₁ Γ₂ : Env}
    {pre : SLP (State p)}
    {expr : Expr (Tp.denote p) tp}
    {post : Tp.denote p tp → SLP (State p)}
    {innerSubOuter : Γ₁ ⊆ Γ₂}
  : STHoare p Γ₁ pre expr post → STHoare p Γ₂ pre expr post := by
  unfold STHoare THoare
  intro h
  intros
  apply Omni.is_monotonic <;> repeat apply_assumption


end STHoare

end Lampe
