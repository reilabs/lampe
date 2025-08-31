import Lampe.SeparationLogic.State
import Lampe.SeparationLogic.SLP
import Lampe.Tactic.SLNorm
import Lampe.Tactic.SL.Term
import Lampe.Syntax

import Lean.Meta.Tactic.Simp.Main

open Lampe

open Lampe.SL

open Lean Elab.Tactic Parser.Tactic Lean.Meta Qq

initialize
  Lean.registerTraceClass `Lampe.SL

namespace Internal

theorem singleton_congr_star_mv {p} {r} {v₁ v₂ : AnyValue p}  (heq: v₁ = v₂): ([r ↦ v₁] ⊢ [r ↦ v₂] ⋆ ⟦⟧) := by
  cases heq
  simp
  apply SLP.entails_self

theorem lmbSingleton_congr_star_mv {argTps outTp p} (r : FuncRef argTps outTp) (f : HList (Tp.denote p) argTps → Expr (Tp.denote p) outTp):
    ([λr ↦ f] ⊢ [λr ↦ f] ⋆ ⟦⟧) := by
  simp
  apply SLP.entails_self

theorem entails_self_true {p} {R : SLP (State p)} : R ⊢ R ⋆ ⟦⟧ := by
  simp
  apply SLP.entails_self

theorem exists_singleton_congr_mv {p} {r} {v₁ : AnyValue p} {v₂ : α → AnyValue p} (heq: ∀a, v₁ = v₂ a):
    ((∃∃a, [r ↦ v₂ a]) ⊢ [r ↦ v₁] ⋆ ⟦⟧) := by
  intro h
  simp
  apply SLP.exists_intro_l
  intro a
  rw [←heq _]
  apply SLP.entails_self

theorem singleton_congr_star {p} {r} {v₁ v₂ : AnyValue p} {R} (h: v₁ = v₂): [r ↦ v₁] ⋆ R ⊢ [r ↦ v₂] ⋆ R := by
  cases h
  apply SLP.entails_self

theorem exists_singleton_congr_star {p r} {R : SLP (State p)} {v₁ : AnyValue p} {v₂ : α → AnyValue p} : (∀a, v₁ = v₂ a) →
    ((∃∃a, [r ↦ v₂ a]) ⋆ R ⊢ [r ↦ v₁] ⋆ R) := by
  intro h
  simp only [←SLP.exists_star]
  apply SLP.exists_intro_l
  intro a
  rw [SLP.star_comm]
  apply SLP.star_mono_r
  rw [←h _]
  apply SLP.entails_self

theorem skip_impure_evidence [LawfulHeap α] {R L G H : SLP α} : (R ⊢ G ⋆ H) → (L ⋆ R ⊢ G ⋆ L ⋆ H) := by
  intro
  apply SLP.entails_trans
  apply SLP.star_mono_l
  assumption
  rw [SLP.star_comm, SLP.star_assoc]
  apply SLP.star_mono_l
  rw [SLP.star_comm]
  apply SLP.entails_self

theorem skip_pure_evidence [LawfulHeap α] {H Q R : SLP α} :
  (P → (H ⊢ Q ⋆ R)) → (P ⋆ H ⊢ Q ⋆ P ⋆ R) := by
  intro
  apply SLP.pure_left
  intro
  rw [SLP.star_comm, SLP.star_assoc]
  apply SLP.pure_right
  assumption
  rw [SLP.star_comm]
  tauto

theorem skip_evidence_and_solve_pure [LawfulHeap α] {H : SLP α} : Q → (H ⊢ Q ⋆ H) := by
  intro
  apply SLP.pure_right
  tauto
  tauto

theorem solve_pure_ent_pure_star_mv [LawfulHeap α] : (P → Q) → ((P : SLP α) ⊢ Q ⋆ P) := by
  intro h
  apply SLP.pure_left'
  intro
  apply SLP.pure_right
  tauto
  simp [*, SLP.entails_self]

theorem solve_exi_prop_l [LawfulHeap α] {P : Prop} {H : P → SLP α} {Q : SLP α} :
  ((x : P) → ((P ⋆ H x) ⊢ Q)) → ((∃∃x, H x) ⊢ Q) := by
  intro h st
  unfold SLP.entails SLP.exists' at *
  rintro ⟨v, hH⟩
  apply h
  use ∅, st
  refine ⟨?_, ?_, ?_, ?_⟩
  apply LawfulHeap.empty_disjoint
  all_goals simp_all [LawfulHeap.disjoint_empty, SLP.lift]

theorem star_top_of_star_mvar [LawfulHeap α] {H Q R : SLP α} : (H ⊢ Q ⋆ R) → (H ⊢ Q ⋆ ⊤) := by
  intro h
  apply SLP.entails_trans
  assumption
  apply SLP.star_mono_l
  apply SLP.entails_top

theorem solve_exi_prop [LawfulHeap α] {P : Prop} {H : SLP α} {Q : P → SLP α} :
  (H ⊢ P ⋆ ⊤) → (∀(p : P), H ⊢ Q p) → (H ⊢ ∃∃p, Q p) := by
  intro h₁ h₂
  unfold SLP.entails at *
  intro st hH
  rcases h₁ st hH with ⟨_, _, _, _, h, _⟩
  rcases h
  apply Exists.intro
  apply_assumption
  apply_assumption
  assumption

lemma solve_exi_prop_star_mv {p} {P R : SLP (State p)} {Q : H → SLP (State p)} : (P ⊢ ⟦H⟧ ⋆ ⊤) → (∀(h : H), P ⊢ Q h ⋆ R) → (P ⊢ (∃∃h, Q h) ⋆ R) := by
  simp only [←SLP.exists_star, ←SLP.star_exists]
  intros
  apply solve_exi_prop
  assumption
  simp_all [SLP.star_comm]

lemma solve_compose [LawfulHeap α] {P Q R S : SLP α} (h₁ : P ⊢ Q ⋆ R) (h₂ : R ⊢ S): P ⊢ Q ⋆ S := by
  apply SLP.entails_trans
  assumption
  apply SLP.star_mono_l
  assumption

theorem solve_pure_ent_pure [LawfulHeap α] {P Q : Prop} :
  (P → Q) → ((⟦P⟧ : SLP α) ⊢ ⟦Q⟧) := by
  unfold SLP.lift
  unfold SLP.entails
  simp only [and_imp, forall_eq_apply_imp_iff, and_true, imp_self]

theorem ent_congr {p} {P P' Q Q' : SLP (State p)} (h₁ : P = P') (h₂ : Q = Q') : (P' ⊢ Q') → (P ⊢ Q) := by
  cases h₁
  cases h₂
  exact id

end Internal

structure SLGoals where
  entailments : List MVarId
  props : List MVarId
  implicits : List MVarId

def SLGoals.flatten (g : SLGoals): List MVarId := g.entailments ++ g.props ++ g.implicits

instance : Append SLGoals where
  append g₁ g₂ := { entailments := g₁.entailments ++ g₂.entailments, props := g₁.props ++ g₂.props, implicits := g₁.implicits ++ g₂.implicits }

def Lean.MVarId.apply' (m: MVarId) (e: Expr): TacticM (List MVarId) := do
  trace[Lampe.SL] "Applying {e}"
  m.apply e

/--
Solves goals of the form `P ⊢ [r ↦ v] ⋆ ?_`, trying to copy as much evidence as possible to the MVar on the right
-/
partial def solveSingletonStarMV (goal : MVarId) (lhs : SLTerm) (rhs : Expr): TacticM SLGoals := do
  match lhs with
  | SLTerm.singleton _ v _ =>
    if v == rhs then
      let heq :: impl ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.singleton_congr_star_mv) | throwError "unexpect goals in singleton_congr_star_mv"
      let heq ← try heq.refl; pure []
        catch _ => pure [heq]
      pure $ SLGoals.mk [] heq impl
    else throwError "final singleton is not equal"
  | SLTerm.lmbSingleton _ v _ =>
    if (← goal.withContext $ isDefEq v rhs) then
      let impl ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.lmbSingleton_congr_star_mv)
      pure $ SLGoals.mk [] [] impl
    else throwError "final lmb singleton is not equal"
  | SLTerm.exi _ _ =>
    if (←solvesSingleton lhs rhs) then
      let heq :: impl ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.exists_singleton_congr_mv) | throwError "unexpect goals in exists_singleton_congr_mv"
      let heq ← try (←heq.intro1).2.refl; pure []
        catch _ => pure [heq]
      pure $ SLGoals.mk [] heq impl
    else
      throwError "existential cannot solve the singleton"
  | SLTerm.star _ l r =>
    match l with
    | SLTerm.singleton _ v _ => do
      if v == rhs then
        let heq :: impl ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.singleton_congr_star) | throwError "unexpect goals in singleton_congr_star"
        let heq ← try heq.refl; pure []
          catch _ => pure [heq]
        pure $ SLGoals.mk [] heq impl
      else
        let hent :: impl ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.skip_impure_evidence) | throwError "unexpect goals in skip_impure_evidence"
        let goals ← solveSingletonStarMV hent r rhs
        pure $ goals ++ SLGoals.mk [] [] impl
    | SLTerm.lift _ =>
      let hEnt :: impl ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.skip_pure_evidence) | throwError "unexpect goals in skip_pure_evidence"
      let (_, hEnt) ← hEnt.intro1
      let goals ← solveSingletonStarMV hEnt r rhs
      pure $ goals ++ SLGoals.mk [] [] impl
    | SLTerm.exi _ _ =>
      if (←solvesSingleton l rhs) then
        let hent :: impl ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.exists_singleton_congr_star) | throwError "unexpect goals in exists_singleton_congr_star"
        let hent ← try (←hent.intro1).2.refl; pure []
          catch _ => pure [hent]
        pure $ SLGoals.mk [] hent impl
      else
        let hEnt :: impl ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.skip_impure_evidence) | throwError "unexpect goals in skip_impure_evidence"
        let goals ← solveSingletonStarMV hEnt r rhs
        pure $ goals ++ SLGoals.mk [] [] impl
    | _ =>
      let hEnt :: impl ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.skip_impure_evidence) | throwError "unexpect goals in skip_impure_evidence"
      let goals ← solveSingletonStarMV hEnt r rhs
      pure $ goals ++ SLGoals.mk [] [] impl
  | _ => throwError "unrecognized shape in solveSingletonStarMV"


/--
Solves goals of the form `P ⊢ ⟦Q⟧ ⋆ ?_`, trying to copy as much evidence as possible to the MVar on the right
-/
partial def solvePureStarMV (goal : MVarId) (lhs : SLTerm): TacticM SLGoals := withTraceNode `Lampe.SL (fun e => return f!"solvePureStarMV {Lean.exceptEmoji e}") do
  match lhs with
  | .lift _ =>
    let g :: impls ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.solve_pure_ent_pure_star_mv) | throwError "unexpected goals in solve_pure_ent_pure_star_mv"
    let (_, g) ← g.intro1
    pure $ SLGoals.mk [] [g] impls
  | .star _ l r => do
    match l with
    | .lift _ =>
      let hEnt :: impl ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.skip_pure_evidence) | throwError "unexpect goals in skip_pure_evidence"
      let (_, hEnt) ← hEnt.intro1
      let goals ← solvePureStarMV hEnt r
      pure $ goals ++ SLGoals.mk [] [] impl
    | _ =>
      let hEnt :: impl ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.skip_impure_evidence) | throwError "unexpect goals in skip_impure_evidence"
      let goals ← solvePureStarMV hEnt r
      pure $ goals ++ SLGoals.mk [] [] impl
  | .singleton _ _ _
  | .lmbSingleton _ _ _
  | .exi _ _ =>
      let final :: impl ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.skip_evidence_and_solve_pure) | throwError "unexpected goals in skip_evidence_and_solve_pure"
      pure $ SLGoals.mk [] [final] impl
  | _ => throwError "Unrecognized shape in solvePureStarMV"

/--
Solves goals of the form `⟦P⟧ ⊢ ⟦Q⟧` by transforming it to a goal of the form `P → Q` and trying
-/
def solvePureEntailMV (goal : MVarId) (preExpr : Lean.Expr) : TacticM SLGoals := withTraceNode `Lampe.SL (fun e => return f!"solvePureEntailMV {Lean.exceptEmoji e}") do
  let g :: impls ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.solve_pure_ent_pure) | throwError "unexpected goals in solve_pure_ent_pure"
  let gs ← evalTacticAt (←`(tactic|try tauto)) g
  if gs.isEmpty then
    return SLGoals.mk [] [] impls
  else
    -- If we are left in a `True → P` goal state then replace this with `P`
    if preExpr.isAppOf' ``True then
      let mut (trueVar, g) ← g.intro1
      g ← g.clear trueVar
      return SLGoals.mk [] [g] impls
    return SLGoals.mk [] [g] impls

def solveExactStarMV (goal: MVarId) (lhs : SLTerm) (rhs : Expr): TacticM SLGoals := withTraceNode `Lampe.SL (fun e => return f!"solveExactStarMV {Lean.exceptEmoji e}") do
  match lhs with
  | SLTerm.unrecognized expr =>
    if (←isDefEq expr rhs) then
      let impl ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.entails_self_true)
      pure $ SLGoals.mk [] [] impl
    else throwError "final unrecognized is not equal"
  | SLTerm.star _ l r => do
    match l with
    | SLTerm.unrecognized expr =>
      if (←isDefEq expr rhs) then
        let impl ← goal.apply' (←mkConstWithFreshMVarLevels ``SLP.entails_self)
        pure $ SLGoals.mk [] [] impl
      else
        let hent :: impl ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.skip_impure_evidence) | throwError "unexpect goals in skip_impure_evidence"
        let goals ← solveExactStarMV hent r rhs
        pure $ goals ++ SLGoals.mk [] [] impl
    | SLTerm.lift _ => do
      let hEnt :: impl ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.skip_pure_evidence) | throwError "unexpect goals in skip_pure_evidence"
      let (_, hEnt) ← hEnt.intro1
      let goals ← solveExactStarMV hEnt r rhs
      pure $ goals ++ SLGoals.mk [] [] impl
    | _ => do
      let hEnt :: impl ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.skip_impure_evidence) | throwError "unexpect goals in skip_impure_evidence"
      let goals ← solveExactStarMV hEnt r rhs
      pure $ goals ++ SLGoals.mk [] [] impl
  | _ => throwError "Unrecognized shape in solveExactStarMV"

mutual

/--
Solves goals of the form `P ⊢ Q ⋆ ?_`, trying to copy as much evidence as possible to the MVar on the right
-/
partial def solveStarMV (goal : MVarId) (lhs : SLTerm) (rhsNonMv : SLTerm): TacticM SLGoals := withTraceNode `Lampe.SL (fun e => return f!"solveStarMV {Lean.exceptEmoji e}") do
  match rhsNonMv with
  | .singleton _ v _ => solveSingletonStarMV goal lhs v
  | .lmbSingleton _ v _ => solveSingletonStarMV goal lhs v
  | .lift _ => solvePureStarMV goal lhs
  | .exi _ _ =>
    -- solve_exi_prop_star_mv
    let ent₁ :: ent₂ :: impls ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.solve_exi_prop_star_mv) | throwError "unexpected goals in solve_exi_prop_star_mv"
    let gent₁ ← solveEntailment ent₁
    let (_, ent₂) ← ent₂.intro1
    let gent₂ ← solveEntailment ent₂
    return gent₁ ++ gent₂ ++ SLGoals.mk [] [] impls
  | .unrecognized expr => solveExactStarMV goal lhs expr
  | _ => throwError "Unrecognized shape in solveStarMV"

partial def solveEntailment (goal : MVarId): TacticM SLGoals := goal.withContext $ withTraceNode `Lampe.SL (tag := "solveEntailment") (fun e => return f!"solveEntailment {Lean.exceptEmoji e}") do
  let target ← goal.instantiateMVarsInType
  let (pre, post) ← parseEntailment target
  let (pre, preEq) ← Lampe.SL.norm pre
  let (post, postEq) ← Lampe.SL.norm post
  let newGoalTp ← mkAppM ``SLP.entails #[pre.expr, post.expr]
  let nextGoal ← mkFreshMVarId
  let goalExpr ← mkFreshExprMVarWithId nextGoal (some newGoalTp)
  let congr ← mkAppM ``Internal.ent_congr #[preEq, postEq, goalExpr]
  goal.assign congr
  let goal := nextGoal

  trace[Lampe.SL] "Current goal: {pre.printShape} ⊢ {post.printShape}"
  trace[Lampe.SL] (←Lean.PrettyPrinter.ppExpr target)

  goal.withContext do
    match pre with
    | SLTerm.exi _ _ => do
    -- solve_exi_prop_l
      let g :: impls ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.solve_exi_prop_l) | throwError "unexpected goals in solve_exi_prop_l"
      let (_, g) ← g.intro1
      let newGoals ← solveEntailment g
      return newGoals ++ SLGoals.mk [] [] impls
    | SLTerm.top _ => do
      let impls ← goal.apply' (←mkConstWithFreshMVarLevels ``SLP.entails_top)
      return SLGoals.mk [] [] impls
    | SLTerm.lift expr => do
      if let SLTerm.lift _ := post then
        return ← solvePureEntailMV goal expr
    | _ => pure ()

    match post with
    | SLTerm.mvar _ =>
      let impls ← goal.apply' (←mkConstWithFreshMVarLevels ``SLP.entails_self)
      return SLGoals.mk [] [] impls
    | SLTerm.top _ =>
      let impls ← goal.apply' (←mkConstWithFreshMVarLevels ``SLP.entails_top)
      return SLGoals.mk [] [] impls
    | SLTerm.star _ l r =>
      -- [TODO] left can be mvar – should be rotated back
      if r.isMVar then
        let newGoals ← solveStarMV goal pre l
        return newGoals
      else if r.isTop then
        let g :: impls ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.star_top_of_star_mvar) | throwError "unexpected goals in star_top_of_star_mvar"
        let ng ← solveEntailment g
        return ng ++ SLGoals.mk [] [] impls
      else
        let g₁ :: g₂ :: impls ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.solve_compose) | throwError "unexpected goals in solve_compose"
        let ng₁ ← solveEntailment g₁
        let ng₂ ← solveEntailment g₂
        return ng₁ ++ ng₂ ++ SLGoals.mk [] [] impls
    | SLTerm.singleton _ _ _ =>
      -- [TODO] handle pure on the left
      let impls ← goal.apply' (←mkConstWithFreshMVarLevels ``SLP.entails_self)
      return SLGoals.mk [] [] impls
    | SLTerm.all _ _ => do
      let new ← goal.apply' (←mkConstWithFreshMVarLevels ``SLP.forall_right)
      let new' ← liftOption new[0]?
      let (_, g) ← new'.intro1
      solveEntailment g
    | SLTerm.wand _ _ _ =>
      let new ← goal.apply' (←mkConstWithFreshMVarLevels ``SLP.wand_intro)
      let new' ← liftOption new[0]?
      solveEntailment new'
    | SLTerm.exi _ _ =>
      -- [TODO] this only works for prop existential - make the others an error
      let ent₁ :: ent₂ :: impls ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.solve_exi_prop) | throwError "unexpected goals in solve_exi_prop"
      let gent₁ ← solveEntailment ent₁
      let (_, ent₂) ← ent₂.intro1
      let gent₂ ← solveEntailment ent₂
      return gent₁ ++ gent₂ ++ SLGoals.mk [] [] impls
    | _ => throwError "unknown rhs {post}"

end

syntax "sl" : tactic
elab "sl" : tactic => do
  let target ← getMainGoal
  let newGoals ← solveEntailment target
  replaceMainGoal newGoals.flatten


-- set_option trace.Lampe.SL true

example : (⟦⟧ : SLP (State p)) ⊢ ⟦⟧ := by
  apply SLP.entails_trans
  sl
  sl
