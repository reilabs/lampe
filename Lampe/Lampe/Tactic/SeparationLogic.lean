import Lampe.SeparationLogic
import Lampe.Hoare.SepTotal
import Lampe.Syntax

import Lean.Meta.Tactic.Simp.Main

open Lampe

open Lean Elab.Tactic Parser.Tactic Lean.Meta Qq Lampe.STHoare

inductive SLTerm where
| top : SLTerm
| star : Expr → SLTerm → SLTerm → SLTerm
| lift : Expr → SLTerm
| singleton : Expr → Expr → SLTerm
| mvar : Expr → SLTerm
| all : Expr → SLTerm
| exi : Expr → SLTerm
| wand : SLTerm → SLTerm → SLTerm
| unrecognized : Expr → SLTerm

def SLTerm.toString : SLTerm → String
| top => "⊤"
| wand a b => s!"{a.toString} -⋆ {b.toString}"
| exi e => s!"∃∃ {e}"
| all e => s!"∀∀ {e}"
| star _ a b => s!"({a.toString} ⋆ {b.toString})"
| lift e => s!"⟦{e.dbgToString}⟧"
| singleton e₁ _ => s!"[{e₁.dbgToString} ↦ _]"
| mvar e => s!"MV{e.dbgToString}"
| unrecognized e => s!"<unrecognized: {e.dbgToString}>"

def SLTerm.isMVar : SLTerm → Bool
| SLTerm.mvar _ => true
| _ => false

def SLTerm.isTop : SLTerm → Bool
| SLTerm.top => true
| _ => false

instance : ToString SLTerm := ⟨SLTerm.toString⟩

instance : Inhabited SLTerm := ⟨SLTerm.top⟩

theorem star_exists {Q : α → SLP p} : ((∃∃x, Q x) ⋆ P) = (∃∃x, Q x ⋆ P) := by
  unfold SLP.exists' SLP.star
  funext st
  simp
  tauto

theorem exists_star {Q : α → SLP p} : ((∃∃x, Q x) ⋆ P) = (∃∃x, P ⋆ Q x) := by
  rw [star_exists]
  simp [SLP.star_comm]

theorem Lampe.STHoare.litU_intro: STHoare p Γ ⟦⟧ (.lit (.u s) n) fun v => v = n := by
  -- apply litU_intro
  unfold STHoare THoare
  intro H st hp
  constructor
  simp only
  apply SLP.ent_star_top
  assumption

theorem ref_intro' {p} {x : Tp.denote p tp} {Γ P}:
    STHoare p Γ P (.ref x) fun v => [v ↦ ⟨tp, x⟩] ⋆ P := by
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

theorem Lampe.SLP.skip_fst' : (⟦⟧ ⊢ Q ⋆ X) → ([a ↦ b] ⋆ X ⊢ R₂) → ([a ↦ b] ⊢ Q ⋆ R₂) := by
  intro h₁ h₂
  rw [←SLP.star_true (H:=[a ↦ b])]
  apply Lampe.SLP.skip_fst
  assumption
  assumption

theorem Lampe.SLP.entails_star_true : H ⊢ H ⋆ ⟦⟧ := by
  simp [SLP.entails_self]

theorem SLP.eq_of_iff : (P ⊢ Q) → (Q ⊢ P) → P = Q := by
  intros
  apply funext
  intro
  apply eq_iff_iff.mpr
  apply Iff.intro <;> apply_assumption

theorem pluck_pure_l {P : Prop} : ([a ↦ b] ⋆ P) = (P ⋆ [a ↦ b]) := by simp [SLP.star_comm]
theorem pluck_pure_all_l {P : Prop} : (SLP.forall' f ⋆ P) = (P ⋆ SLP.forall' f) := by simp [SLP.star_comm]
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
  try simp only [SLP.star_assoc, pluck_pure_l, pluck_pure_l_assoc, pluck_pure_all_l, SLP.star_true, SLP.true_star, star_exists, exists_star];
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

partial def extractTripleExpr (e: Expr): TacticM (Option Expr) := do
  if e.isAppOf ``STHoare then
    let args := e.getAppArgsN 5
    return args[3]?
  else return none

def isLetIn (e: Expr): Bool :=
  e.isAppOf ``Lampe.Expr.letIn

partial def parseSLExpr (e: Expr): TacticM SLTerm := do
  if e.isAppOf ``SLP.star then
    let args := e.getAppArgs
    let fst ← parseSLExpr (←args[1]?)
    let snd ← parseSLExpr (←args[2]?)
    return SLTerm.star e fst snd
  if e.isAppOf ``SLP.singleton then
    let args := e.getAppArgs
    let fst ←args[1]?
    let snd ← args[2]?
    return SLTerm.singleton fst snd
  else if e.isAppOf ``SLP.top then
    return SLTerm.top
  else if e.isAppOf ``SLP.lift then
    let args := e.getAppArgs
    return SLTerm.lift (←args[1]?)
  else if e.isMVar then
    return SLTerm.mvar e
  else if e.isAppOf ``SLP.forall' then
    let args := e.getAppArgs
    return SLTerm.all (←args[2]?)
  else if e.isAppOf ``SLP.exists' then
    let args := e.getAppArgs
    return SLTerm.exi (←args[2]?)
  else if e.isAppOf ``SLP.wand then
    let args := e.getAppArgs
    let lhs ← parseSLExpr (←args[1]?)
    let rhs ← parseSLExpr (←args[2]?)
    return SLTerm.wand lhs rhs
  -- else if e.isAppOf ``SLTerm.lift then
  --   let args := e.getAppArgs
  --   return SLTerm.lift args[0]
  -- else if e.isAppOf ``SLTerm.singleton then
  --   let args := e.getAppArgs
  --   return SLTerm.singleton args[0] args[1]
  -- else if e.isAppOf ``SLTerm.mvar then
  --   let args := e.getAppArgs
  --   return SLTerm.mvar args[0]
  else pure $ .unrecognized e

partial def parseEntailment (e: Expr): TacticM (SLTerm × SLTerm) := do
  if e.isAppOf ``SLP.entails then
    let args := e.getAppArgs
    let pre ← parseSLExpr (←args[1]?)
    let post ← parseSLExpr (←args[2]?)
    return (pre, post)
  else throwError "not an entailment"

theorem star_top_of_star_mvar : (H ⊢ Q ⋆ R) → (H ⊢ Q ⋆ ⊤) := by
  intro h
  apply SLP.entails_trans
  assumption
  apply SLP.star_mono_l
  apply SLP.entails_top

theorem solve_left_with_leftovers : (H ⊢ Q ⋆ R) → (R ⊢ P) → (H ⊢ Q ⋆ P) := by
  intros
  apply SLP.entails_trans
  assumption
  apply SLP.star_mono_l
  assumption

theorem solve_with_true : (H ⊢ Q) → (H ⊢ Q ⋆ ⟦⟧) := by
  aesop
-- partial def solveNonMVarEntailment (goal : MVarId) (lhs : SLTerm) (rhs : SLTerm): TacticM (List MVarId × SLTerm) := do

theorem pure_ent_pure_star_mv: (P → Q) → ((P : SLP p) ⊢ Q ⋆ ⟦⟧) := by
  intro h
  apply SLP.pure_left'
  intro
  apply SLP.pure_right
  tauto
  tauto

theorem pure_star_H_ent_pure_star_mv: (P → (H ⊢ Q ⋆ R)) → (P ⋆ H ⊢ Q ⋆ P ⋆ R) := by
  intro
  apply SLP.pure_left
  intro
  rw [SLP.star_comm, SLP.star_assoc]
  apply SLP.pure_right
  assumption
  rw [SLP.star_comm]
  tauto

theorem skip_left_ent_star_mv : (R ⊢ P ⋆ H) → (L ⋆ R ⊢ P ⋆ L ⋆ H) := by
  intro h
  apply SLP.entails_trans
  apply SLP.star_mono_l
  assumption
  rw [SLP.star_comm, SLP.star_assoc]
  apply SLP.star_mono_l
  rw [SLP.star_comm]
  apply SLP.entails_self

theorem skip_evidence_pure : Q → (H ⊢ Q ⋆ H) := by
  intro
  apply SLP.pure_right
  tauto
  tauto

theorem SLP.exists_intro { Q : α → SLP p } {a} : (H ⊢ Q a) → (H ⊢ ∃∃a, Q a) := by
  intro h st H
  unfold SLP.exists'
  exists a
  tauto

theorem exi_prop {Q : P → SLP p} : (H ⊢ P ⋆ ⊤) → (∀(p:P), H ⊢ Q p) → (H ⊢ ∃∃p, Q p) := by
  intro h₁ h₂
  unfold SLP.entails at *
  intro st hH
  rcases h₁ st hH with ⟨_, _, _, _, h, _⟩
  rcases h
  apply Exists.intro
  apply_assumption
  apply_assumption
  assumption

theorem exi_prop_l {H : P → SLP p} : ((x:P) → ((P ⋆ H x) ⊢ Q)) → ((∃∃x, H x) ⊢ Q) := by
  intro h st
  unfold SLP.entails SLP.exists' at *
  rintro ⟨v, hH⟩
  apply h
  use ∅, st
  simp_all [Finmap.disjoint_empty, SLP.lift]
  simp_all

theorem use_right : (R ⊢ G ⋆ H) → (L ⋆ R ⊢ G ⋆ L ⋆ H) := by
  intro
  apply SLP.entails_trans
  apply SLP.star_mono_l
  assumption
  rw [SLP.star_comm, SLP.star_assoc]
  apply SLP.star_mono_l
  rw [SLP.star_comm]
  apply SLP.entails_self

theorem singleton_congr {p} {r} {v₁ v₂ : AnyValue p} : (v₁ = v₂) → ([r ↦ v₁] ⊢ [r ↦ v₂]) := by
  intro h
  rw [h]
  apply SLP.entails_self

theorem singleton_congr_mv {p} {r} {v₁ v₂ : AnyValue p} : (v₁ = v₂) → ([r ↦ v₁] ⊢ [r ↦ v₂] ⋆ ⟦⟧) := by
  rintro rfl
  simp
  apply SLP.entails_self

theorem singleton_star_congr {p} {r} {v₁ v₂ : AnyValue p} {R} : (v₁ = v₂) → ([r ↦ v₁] ⋆ R ⊢ [r ↦ v₂] ⋆ R) := by
  rintro rfl
  apply SLP.entails_self

def canSolveSingleton (lhs : SLTerm) (rhsV : Expr): Bool :=
  match lhs with
  | SLTerm.singleton v _ => v == rhsV
  | SLTerm.star _ l r => canSolveSingleton l rhsV || canSolveSingleton r rhsV
  | _ => false

partial def solveSingletonStarMV (goal : MVarId) (lhs : SLTerm) (rhs : Expr): TacticM (List MVarId) := do
  match lhs with
  | SLTerm.singleton v _ =>
    if v == rhs then
      let newGoals ← goal.apply (←mkConstWithFreshMVarLevels ``singleton_congr_mv)
      let newGoal ← newGoals[0]?
      let newGoal ← try newGoal.refl; pure []
        catch _ => pure [newGoal]
      pure $ newGoal ++ newGoals
    else throwError "not equal"
  | SLTerm.star _ l r =>
    match l with
    | SLTerm.singleton v _ => do
      if v == rhs then
        -- [TODO] This should use EQ, not ent_self
        let newGoals ← goal.apply (←mkConstWithFreshMVarLevels ``singleton_star_congr)
        let newGoal ← newGoals[0]?
        let newGoal ← try newGoal.refl; pure []
          catch _ => pure [newGoal]
        pure $ newGoal ++ newGoals
      else
        let newGoals ← goal.apply (←mkConstWithFreshMVarLevels ``use_right)
        let newGoal ← newGoals[0]?
        let new' ← solveSingletonStarMV newGoal r rhs
        return new' ++ newGoals
    | SLTerm.lift _ =>
      let goals ← goal.apply (←mkConstWithFreshMVarLevels ``pure_star_H_ent_pure_star_mv)
      let g ← goals[0]?
      let (_, g) ← g.intro1
      let ng ← solveSingletonStarMV g r rhs
      return ng ++ goals
    | _ =>
      let newGoals ← goal.apply (←mkConstWithFreshMVarLevels ``use_right)
      let newGoal ← newGoals[0]?
      let new' ← solveSingletonStarMV newGoal r rhs
      return new' ++ newGoals
  | _ => throwError "not a singleton {lhs}"

partial def solvePureStarMV (goal : MVarId) (lhs : SLTerm): TacticM (List MVarId) := do
  match lhs with
  | .lift _ => goal.apply (←mkConstWithFreshMVarLevels ``pure_ent_pure_star_mv)
  | .star _ l r => do
    match l with
    | .lift _ =>
      let goals ← goal.apply (←mkConstWithFreshMVarLevels ``pure_star_H_ent_pure_star_mv)
      let g ← goals[0]?
      let (_, g) ← g.intro1
      let ng ← solvePureStarMV g r
      return ng ++ goals
    | _ =>
      let goals ← goal.apply (←mkConstWithFreshMVarLevels ``skip_left_ent_star_mv)
      let g ← goals[0]?
      let ng ← solvePureStarMV g l
      return ng ++ goals
  | .singleton _ _ =>
      goal.apply (←mkConstWithFreshMVarLevels ``skip_evidence_pure)
  | _ => throwError "not a lift {lhs}"

partial def solveStarMV (goal : MVarId) (lhs : SLTerm) (rhsNonMv : SLTerm): TacticM (List MVarId) := do
  match rhsNonMv with
  | .singleton v _ => solveSingletonStarMV goal lhs v
  | .lift _ => solvePureStarMV goal lhs
  | _ => throwError "not a singleton srry {rhsNonMv}"

partial def solveEntailment (goal : MVarId): TacticM (List MVarId) := do
  let newGoal ← evalTacticAt (←`(tactic|h_norm)) goal
  let goal ← newGoal[0]?
  let target ← goal.instantiateMVarsInType
  let (pre, post) ← parseEntailment target

  match pre with
  | SLTerm.exi _ => do
    let newGoals ← goal.apply (←mkConstWithFreshMVarLevels ``exi_prop_l)
    let newGoal ← newGoals[0]?
    let (_, newGoal) ← newGoal.intro1
    let gls ← solveEntailment newGoal
    return gls ++ newGoals
  | SLTerm.top => do
    let newGoals ← goal.apply (←mkConstWithFreshMVarLevels ``SLP.entails_top)
    return newGoals
  | _ => pure ()

  match post with
  | SLTerm.mvar _ => goal.apply (←mkConstWithFreshMVarLevels ``SLP.entails_self)
  | SLTerm.star _ l r =>
    -- [TODO] left can be mvar – should be rotated back
    if r.isMVar then
      let newGoals ← solveStarMV goal pre l
      return newGoals
    else if r.isTop then
      let g ← goal.apply (←mkConstWithFreshMVarLevels ``star_top_of_star_mvar)
      let g' ← g[0]?
      let ng ← solveEntailment g'
      pure $ ng ++ g
    else throwError "todo {l} {r}"
  | SLTerm.singleton _ _ =>
    -- [TODO] handle pure on the left
    goal.apply (←mkConstWithFreshMVarLevels ``SLP.entails_self)
  | SLTerm.all _ => do
    let new ← goal.apply (←mkConstWithFreshMVarLevels ``SLP.forall_right)
    let new' ← new[0]?
    let (_, g) ← new'.intro1
    solveEntailment g
  | SLTerm.wand _ _ =>
    let new ← goal.apply (←mkConstWithFreshMVarLevels ``SLP.wand_intro)
    let new' ← new[0]?
    solveEntailment new'
  | SLTerm.exi _ =>
    -- [TODO] this only works for prop existential - make the others an error
    let new ← goal.apply (←mkConstWithFreshMVarLevels ``exi_prop)
    let newL ← solveEntailment (←new[0]?)
    let (_, newR) ← (←new[1]?).intro1
    let newR ← solveEntailment newR
    return newL ++ newR
  | _ => throwError "unknown rhs {post}"

syntax "sl" : tactic
elab "sl" : tactic => do
  let target ← getMainGoal
  let newGoals ← solveEntailment target
  replaceMainGoal newGoals

macro "stephelper1" : tactic => `(tactic|(
  (first
    | apply Lampe.STHoare.litU_intro
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
))

macro "stephelper2" : tactic => `(tactic|(
  (first
    | apply consequence_frame_left fresh_intro
    | apply consequence_frame_left Lampe.STHoare.litU_intro
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
  repeat sl
))

macro "stephelper3" : tactic => `(tactic|(
  (first
    | apply ramified_frame_top fresh_intro
    | apply ramified_frame_top Lampe.STHoare.litU_intro
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
  repeat sl
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
    else if body.isAppOf ``Lampe.Expr.ite then
      if let [fGoal, tGoal] ← mvar.apply (← mkConstWithFreshMVarLevels ``ite_intro) then
        let fGoal ← if let [fGoal] ← evalTacticAt (←`(tactic|intro)) fGoal then pure fGoal
          else throwError "couldn't intro into false branch"
        let tGoal ← if let [tGoal] ← evalTacticAt (←`(tactic|intro)) tGoal then pure tGoal
          else throwError "couldn't intro into true branch"
        let fSubGoals ← try steps fGoal catch _ => pure [fGoal]
        let tSubGoals ← try steps tGoal catch _ => pure [tGoal]
        return fSubGoals ++ tSubGoals
      else return [mvar]
    else
      try evalTacticAt (←`(tactic|stephelper1)) mvar
      catch _ => try evalTacticAt (←`(tactic|stephelper2)) mvar
      catch _ => try evalTacticAt (←`(tactic|stephelper3)) mvar
      catch _ => throwTacticEx (`steps) mvar "Can't solve"
  | _ => return [mvar]

syntax "steps" : tactic
elab "steps" : tactic => do
  let newGoals ← steps (← getMainGoal)
  replaceMainGoal newGoals

syntax "loop_inv" term : tactic
macro "loop_inv" inv:term : tactic => `(tactic|(
  (first
    | apply loop_inv_intro $inv ?_
    | apply consequence_frame_left; apply loop_inv_intro $inv ?_
    | apply ramified_frame_top; apply loop_inv_intro $inv ?_
  )
  on_goal 2 => sl
))
