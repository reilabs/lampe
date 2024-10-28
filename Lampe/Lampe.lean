-- This module serves as the root of the `Lampe` library.
-- Import modules here that should be built as part of the library.
-- import «Lampe».Basic
import Lampe.Hoare
import Lean.Meta.Tactic.Simp.Main

open Lampe

open Lean Elab.Tactic Parser.Tactic Lean.Meta Qq

theorem ref_intro' {p} {x : Tp.denote p tp} {Γ P}:
    STHoare p Γ P (ref x) fun v => [v ↦ ⟨tp, x⟩] ⋆ P := by
  apply ramified_frame_top
  apply ref_intro
  simp
  apply SLP.forall_right
  intro
  apply SLP.wand_intro
  rw [SLP.star_comm, ←SLP.star_assoc]
  apply SLP.ent_star_top


theorem Lampe.SLP.skip_fst : (R₁ ⊢ Q ⋆ X) → ([a ↦ b] ⋆ X ⊢ R₂) → ([a ↦ b] ⋆ R₁ ⊢ Q ⋆ R₂) := by
  intro h₁ h₂
  apply entails_trans
  rotate_left
  apply star_mono_l
  apply h₂
  apply entails_trans
  apply star_mono_l
  apply h₁
  rw [SLP.star_comm, SLP.star_assoc]
  apply star_mono_l
  rw [SLP.star_comm]
  apply entails_self

theorem Lampe.SLP.entails_star_true : H ⊢ H ⋆ ⟦⟧ := by
  simp [SLP.entails_self]

theorem SLP.eq_of_iff : (P ⊢ Q) → (Q ⊢ P) → P = Q := by
  intros
  apply funext
  intro
  apply eq_iff_iff.mpr
  apply Iff.intro <;> apply_assumption

theorem pluck_pure_l {P : Prop} : ([a ↦ b] ⋆ P) = (P ⋆ [a ↦ b]) := by simp [SLP.star_comm]
theorem pluck_pure_l_assoc { P : Prop } {Q : SLP p} : ([a ↦ b] ⋆ P ⋆ Q) = (P ⋆ [a ↦ b] ⋆ Q) := by
  rw [SLP.star_comm, SLP.star_assoc]
  apply SLP.eq_of_iff <;> {apply SLP.star_mono_l; rw [SLP.star_comm]; apply SLP.entails_self}

theorem SLP.pure_star_pure {p} { P Q : Prop }: (P ⋆ Q) = (⟦P ∧ Q⟧ : SLP p) := by
  unfold SLP.star SLP.lift
  funext st
  apply eq_iff_iff.mpr
  apply Iff.intro
  · intro_cases
    simp_all
  · intro_cases
    use ∅, ∅
    simp_all [Finmap.disjoint_empty]

macro "h_norm" : tactic => `(tactic|(
  try simp only [SLP.star_assoc, pluck_pure_l, pluck_pure_l_assoc, SLP.star_true, SLP.true_star, SLP.pure_star_pure];
  -- repeat (apply STHoare.pure_left; intro_cases);
  -- repeat (apply SLP.pure_left; intro_cases);
  subst_vars;
))

theorem SLP.pure_leftX : (P → (H ⊢ Q ⋆ R)) → (P ⋆ H ⊢ Q ⋆ P ⋆ R) := by
  intro
  apply SLP.pure_left
  intro
  rw [SLP.star_comm]
  rw [SLP.star_assoc]
  apply SLP.pure_right
  tauto
  rw [SLP.star_comm]
  tauto

/-- only finisher, will waste mvars for top! -/
theorem SLP.pure_ent_star_top : (P → Q) → ((P : SLP p) ⊢ Q ⋆ ⊤) := by
  intro h st hp
  rcases hp with ⟨_, rfl, hp⟩
  use ∅, ∅
  simp_all [Finmap.disjoint_empty, SLP.lift]

theorem star_mono_l_sing : (P ⊢ Q) → (v₁ = v₂) → ([r ↦ v₁] ⋆ P ⊢ [r ↦ v₂] ⋆ Q) := by
  intro h₁ h₂
  rw [h₂]
  apply SLP.star_mono_l
  apply h₁

theorem star_mono_l_sing' : (⟦⟧ ⊢ Q) → (v₁ = v₂) → ([r ↦ v₁] ⊢ [r ↦ v₂] ⋆ Q) := by
  intro h₁ h₂
  rw [h₂]
  apply SLP.star_mono_l'
  apply h₁

/-- for goals with mvars on RHS -/
syntax "sp_slp" : tactic
macro "sp_slp" : tactic => `(tactic|(
    repeat (
      h_norm
      ( first
        | apply SLP.entails_self
        | apply SLP.entails_star_true
        | with_reducible apply SLP.forall_right; intro _
        | apply SLP.pure_leftX; intro_cases; subst_vars
        -- | apply SLP.pure_leftX'; intro_cases; subst_vars -- TODO
        | apply star_mono_l_sing'
        | apply star_mono_l_sing
        | apply SLP.wand_intro
        | apply SLP.entails_top
        | apply SLP.skip_fst
      )
    )
))

/-- only for goals without mvars -/
syntax "sp_slp!" : tactic
macro "sp_slp!" : tactic => `(tactic|(
    repeat (
      h_norm
      ( first
        | apply SLP.entails_self
        | apply SLP.entails_star_true
        | with_reducible apply SLP.forall_right; intro _
        | apply SLP.wand_intro
        | apply SLP.pure_left; intro_cases; subst_vars
        | apply SLP.pure_ent_star_top
        -- | apply SLP.pure_left'; intro_cases; subst_vars -- TODO
        | apply SLP.pure_right;
        | apply SLP.entails_top
        | apply SLP.star_mono_l
        | apply star_mono_l_sing
        | apply SLP.star_mono_l'
        | apply star_mono_l_sing'
        | apply SLP.skip_fst
      )
    )
))


-- syntax "h_norm" : tactic


-- partial def handleSTHoare :


partial def extractTripleExpr (e: Expr): TacticM (Option Expr) := do
  if e.isAppOf ``STHoare then
    let args := e.getAppArgsN 5
    return args[3]?
  else return none

def isLetIn (e: Expr): Bool :=
  e.isAppOf ``Lampe.Expr.letIn

macro "stephelper1" : tactic => `(tactic|
  (first
    | apply fresh_intro
    | apply assert_intro
    | apply eqF_intro
    | apply var_intro
    | apply ref_intro
    | apply readRef_intro
    | apply writeRef_intro
    | apply sliceLen_intro
    | apply sliceIndex_intro
    | apply slicePushBack_intro
  )
)

macro "stephelper2" : tactic => `(tactic|(
  (first
    | apply consequence_frame_left fresh_intro
    | apply consequence_frame_left assert_intro
    | apply consequence_frame_left eqF_intro
    | apply consequence_frame_left var_intro
    | apply consequence_frame_left ref_intro
    | apply consequence_frame_left readRef_intro
    | apply consequence_frame_left writeRef_intro
    | apply consequence_frame_left sliceLen_intro
    | apply consequence_frame_left sliceIndex_intro
    | apply consequence_frame_left slicePushBack_intro
  )
  sp_slp
))

macro "stephelper3" : tactic => `(tactic|(
  (first
    | apply ramified_frame_top fresh_intro
    | apply ramified_frame_top assert_intro
    | apply ramified_frame_top eqF_intro
    | apply ramified_frame_top var_intro
    | apply ramified_frame_top ref_intro
    | apply ramified_frame_top readRef_intro
    | apply ramified_frame_top writeRef_intro
    | apply ramified_frame_top sliceLen_intro
    | apply ramified_frame_top sliceIndex_intro
    | apply ramified_frame_top slicePushBack_intro
  )
  sp_slp!
))


partial def steps (mvar : MVarId) : TacticM (List MVarId) := do
  let target ← mvar.instantiateMVarsInType
  match ←extractTripleExpr target with
  | some body => do
    if isLetIn body then
      if let [fst, snd, trd] ← mvar.apply (←mkConstWithFreshMVarLevels ``letIn_intro)
      then
        let snd ← if let [snd] ← evalTacticAt (←`(tactic|intro)) snd
          then pure snd
          else throwError "couldn't intro in letIn"
        let fstGoals ← try steps fst catch _ => return [fst, snd, trd]
        let sndGoals ← do
          try steps snd
          catch _ => pure [snd]
        return fstGoals ++ sndGoals ++ [trd]
      else return [mvar]
    else
      try evalTacticAt (←`(tactic|stephelper1)) mvar
      catch _ => try evalTacticAt (←`(tactic|stephelper2)) mvar
      catch _ => try evalTacticAt (←`(tactic|stephelper3)) mvar
      catch _ => throwTacticEx (`steps) mvar "Can't solve"
  | _ => dbg_trace "not a thing" ; return [mvar]


syntax "steps" : tactic
elab "steps" : tactic => do
  let newGoals ← steps (← getMainGoal)
  replaceMainGoal newGoals

syntax "loop_inv" term : tactic
macro "loop_inv" inv:term : tactic => `(tactic|
  (first
    | apply loop_inv_intro $inv
    | apply consequence_frame_left; apply loop_inv_intro $inv ?_
    | apply ramified_frame_top; apply loop_inv_intro $inv
  )
)


example : STHoare p Γ ⟦⟧ (simple_muts_anf_body x) fun v => v = x := by
  simp only [simple_muts_anf_body]
  steps

example {self that : Tp.denote P (.slice tp)} : STHoare P Γ ⟦⟧ (sliceAppendBody self that) fun v => v = self ++ that := by
  simp only [sliceAppendBody]
  steps
  rename Tp.denote P tp.slice.ref => selfRef
  loop_inv (fun i _ _ => [selfRef ↦ ⟨.slice tp, self ++ that.take i.val⟩])
  · intro i _ _
    steps
    have : (i + 1).val = i.val + 1 := by
      casesm* (Tp.denote P (.u 32))
      simp_all [Fin.add_def, Fin.lt_def]
      linarith
    rw [this]
    simp only [List.take_succ, List.append_assoc]
    congr
    rename some _ = _ => hp
    simp at hp
    simp [←hp]
  · simp
  · sp_slp
    simp
  steps
  simp_all [Nat.mod_eq_of_lt]
  sp_slp!

def weirdEq {P} (x y : Tp.denote P .field): Lampe.Expr (Tp.denote P) .unit :=
  .letIn (fresh .field) fun z =>
  .letIn (eqF z x) fun eqzx =>
  .letIn (assert eqzx) fun _ =>
  .letIn (eqF z y) fun eqzy =>
  .letIn (assert eqzy) fun r =>
  .var r

example {P} {x y : Tp.denote P .field} : STHoare P Γ ⟦⟧ (weirdEq x y) fun _ => x = y := by
  simp only [_root_.weirdEq]
  steps
  aesop
