import Lampe.SeparationLogic.State
import Lampe.SeparationLogic.SLP
import Lampe.Tactic.SLNorm
import Lampe.Tactic.SL.Term
import Lampe.Tactic.SL.Init
import Lampe.Syntax

import Lean.Meta.Tactic.Simp.Main

open Lampe

open Lampe.SL

open Lean Elab.Tactic Parser.Tactic Lean.Meta Qq

namespace Internal

theorem shift_exists_to_mvar [LawfulHeap β] {P R : α → SLP β}: (∀x, (P x ⊢ Q ⋆ R x)) → ((∃∃x, P x) ⊢ Q ⋆ (∃∃x, R x)) := by
  intro
  apply SLP.exists_intro_l
  intro
  rw [SLP.star_comm, ←SLP.star_exists]
  apply SLP.exists_intro_r
  rw [SLP.star_comm]
  apply_assumption

theorem solve_unit_star_mv {P : SLP (State p)} : (P ⊢ ⟦⟧ ⋆ P) := by
  simp
  apply SLP.entails_self

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

theorem lmbSingleton_congr_star {p} {r : FuncRef i o} {v₁ v₂ : HList (Tp.denote p) i → Lampe.Expr (Tp.denote p) o} {R} (h: v₁ = v₂): [λr ↦ v₁] ⋆ R ⊢ [λr ↦ v₂] ⋆ R := by
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

theorem skip_final_pure_evidence [LawfulHeap α] {Q R : SLP α}:
  (P → (⟦⟧ ⊢ Q ⋆ R)) → (P ⊢ Q ⋆ P ⋆ R) := by
  intro
  have : (P : SLP α) = (P ⋆ ⟦⟧) := by simp
  rw [this, SLP.star_assoc]
  apply skip_pure_evidence
  simp
  assumption

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

theorem solve_pure_of_unit_star_mv [LawfulHeap α] : Q → ((P : SLP α) ⊢ Q ⋆ P) := by
  intro h
  apply SLP.pure_right
  tauto
  apply SLP.entails_self

theorem apply_exi_star [LawfulHeap α] {P : β → SLP α} {H R Q : SLP α} {v}: (H ⊢ R ⋆ P v ⋆ Q) → (H ⊢ (∃∃v, P v) ⋆ R ⋆ Q) := by
  intro
  simp only [←SLP.exists_star]
  apply SLP.exists_intro_r (a := v)
  simp only [SLP.star_assoc]
  conv => rhs; arg 2; rw [SLP.star_comm]
  assumption

theorem apply_exi [LawfulHeap α] {P : β → SLP α} {H Q: SLP α} {v}: (H ⊢ P v ⋆ Q) → (H ⊢ (∃∃v, P v) ⋆ Q) := by
  intro h
  simp only [←SLP.exists_star]
  apply SLP.exists_intro_r (a := v)
  rw [SLP.star_comm]
  assumption

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

lemma solve_exi_prop_star_mv {p} {P R : SLP (State p)} {Q : α → SLP (State p)} {v} : (P ⊢ Q v ⋆ R) → (P ⊢ (∃∃h, Q h) ⋆ R) := by
  simp only [←SLP.exists_star, ←SLP.star_exists]
  intros
  apply SLP.exists_intro_r
  rw [SLP.star_comm]
  assumption

lemma solve_compose [LawfulHeap α] {P Q R S : SLP α} (h₁ : P ⊢ Q ⋆ R) (h₂ : R ⊢ S): P ⊢ Q ⋆ S := by
  apply SLP.entails_trans
  assumption
  apply SLP.star_mono_l
  assumption

lemma solve_compose_with_sinks {α} [LawfulHeap α] {P Q R S T : SLP α} (h₁ : P ⊢ Q ⋆ R) (h₂ : R ⊢ S ⋆ T) : P ⊢ (Q ⋆ S) ⋆ T := by
  simp only [SLP.star_assoc]
  apply solve_compose <;> assumption

lemma rotate_to_sinks {α} [LawfulHeap α] {P Q R S : SLP α} (h : P ⊢ R ⋆ (Q ⋆ S)): P ⊢ (Q ⋆ R) ⋆ S := by
  conv => rhs; arg 1; rw [SLP.star_comm]
  simp_all

theorem solve_pure_ent_pure [LawfulHeap α] {P Q : Prop} :
  (P → Q) → ((⟦P⟧ : SLP α) ⊢ ⟦Q⟧) := by
  unfold SLP.lift
  unfold SLP.entails
  simp only [and_imp, forall_eq_apply_imp_iff, and_true, imp_self]

theorem ent_congr {p} {P P' Q Q' : SLP (State p)} (h₁ : P = P') (h₂ : Q = Q') : (P' ⊢ Q') → (P ⊢ Q) := by
  cases h₁
  cases h₂
  exact id

theorem move_to_sinks {p} {P Q : SLP (State p)} : (P ⊢ Q) → (P ⊢ (⟦⟧ ⋆ Q)) := by
  simp

end Internal

structure SLGoals where
  entailments : List MVarId
  props : List MVarId
  implicits : List MVarId

def SLGoals.flatten (g : SLGoals): List MVarId := g.entailments ++ g.props ++ g.implicits

instance : Append SLGoals where
  append g₁ g₂ := { entailments := g₁.entailments ++ g₂.entailments, props := g₁.props ++ g₂.props, implicits := g₁.implicits ++ g₂.implicits }

instance : Inhabited SLGoals where
  default := { entailments := [], props := [], implicits := [] }

def Lean.MVarId.apply' (m: MVarId) (e: Expr): TacticM (List MVarId) := do
  trace[Lampe.SL] "Applying {e}"
  m.apply e

/--
Solves goals of the form `P ⊢ [r ↦ v] ⋆ ?_`, trying to copy as much evidence as possible to the MVar on the right
-/
partial def solveSingletonStarMV (goal : MVarId) (lhs : SLTerm) (rhs : Expr): TacticM SLGoals := goal.withContext $ withTraceNode `Lampe.SL (fun e => return f!"solveSingletonStarMV {Lean.exceptEmoji e}") $ do
  match lhs with
  | SLTerm.singleton _ v _ =>
    if v == rhs then
      let heq :: impl ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.singleton_congr_star_mv) | throwError "unexpect goals in singleton_congr_star_mv"
      let heq ← try heq.refl; pure []
        catch _ => pure [heq]
      pure $ SLGoals.mk [] heq impl
    else throwError "final singleton is not equal"
  | SLTerm.lmbSingleton _ v _ =>
    if (←isDefEq v rhs) then
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
    | SLTerm.lmbSingleton _ v _ => do
      if v == rhs then
        let heq :: impl ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.lmbSingleton_congr_star) | throwError "unexpect goals in lmbSingleton_congr_star"
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
  | e => throwError "unrecognized shape in solveSingletonStarMV {e.printShape}"


/--
Solves goals of the form `P ⊢ ⟦Q⟧ ⋆ ?_`, trying to copy as much evidence as possible to the MVar on the right
-/
partial def solvePureStarMV (goal : MVarId) (lhs : SLTerm): TacticM SLGoals := withTraceNode `Lampe.SL (fun e => return f!"solvePureStarMV {Lean.exceptEmoji e}") do
  match lhs with
  | .lift _ =>
    let g :: impls ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.solve_pure_ent_pure_star_mv) | throwError "unexpected goals in solve_pure_ent_pure_star_mv"
    let (_, g) ← g.intro1
    pure $ SLGoals.mk [] [g] impls
  | .unit _ =>
    let g :: impls ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.solve_pure_of_unit_star_mv) | throwError "unexpected goals in solve_pure_of_unit_star_mv"
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
  | .exi _ _
  | .unrecognized _ =>
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
    if (←withNewMCtxDepth $ isDefEq expr rhs) then
      let impl ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.entails_self_true)
      pure $ SLGoals.mk [] [] impl
    else throwError "final unrecognized is not equal"
  | SLTerm.star _ l r => do
    match l with
    | SLTerm.unrecognized expr =>
      if (←withNewMCtxDepth $ isDefEq expr rhs) then
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

partial def rewriteSides (goal : MVarId) (newPre newPost : Expr) (eqPre eqPost : Expr) : TacticM MVarId := do
  let newGoalTp ← mkAppM ``SLP.entails #[newPre, newPost]
  let nextGoal ← mkFreshMVarId
  let goalExpr ← mkFreshExprMVarWithId nextGoal (some newGoalTp)
  let congr ← mkAppM ``Internal.ent_congr #[eqPre, eqPost, goalExpr]
  goal.assign congr
  pure nextGoal

partial def normalizePre (goal : MVarId) (pre post : SLTerm) : TacticM (SLTerm × MVarId) := do
  let (pre', preEq) ← Lampe.SL.norm pre
  let postEq ← mkAppM ``Eq.refl #[post.expr]
  let goal ← rewriteSides goal pre'.expr post.expr preEq postEq
  pure (pre', goal)

partial def normalizeSides (goal : MVarId) (pre post : SLTerm) : TacticM (SLTerm × SLTerm × MVarId) := do
  let (pre', preEq) ← Lampe.SL.norm pre
  let (post', postEq) ← Lampe.SL.norm post
  let goal ← rewriteSides goal pre'.expr post'.expr preEq postEq
  pure (pre', post', goal)

-- partial def exi_no_confusion (exi : Expr): TacticM Bool := do
--   match exi with
--   | .lam _ bType _ _ =>
--     let sub ← mkAppM ``Subsingleton #[bType]
--     let inst ← synthInstance? sub
--     -- in the future, we should also do a check for occurences:
--     -- that is, if the body uses the value unambigously (e.g. only on RHS of a ↦),
--     -- it is also save to intro without confusion.
--     pure $ if inst.isSome then true else false
--   | _ => pure false

partial def solveGoal (goal : MVarId) (pre post : SLTerm) : TacticM SLGoals := withTraceNode `Lampe.SL (tag := "solveGoal") (fun e => return f!"solveGoal {Lean.exceptEmoji e}") do
  match post with
  | .singleton _ v _ => solveSingletonStarMV goal pre v
  | .lmbSingleton _ v _ => solveSingletonStarMV goal pre v
  | .lift _ => solvePureStarMV goal pre
  | .unit _ =>
    let impls ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.solve_unit_star_mv)
    pure $ SLGoals.mk [] [] impls
  | .unrecognized expr => solveExactStarMV goal pre expr
  | _ => throwError "Unrecognized shape in solveGoal"

-- Solves all goals, or moves them to sinks if unable to close.
-- If this returns (pre, sinks, goal), we have `goal : pre ⊢ sinks`, with both sides normalized
partial def solveGoals (goal : MVarId) (pre goals sinks : SLTerm) : TacticM (SLGoals × SLTerm × SLTerm × MVarId) := withTraceNode `Lampe.SL (tag := "solveGoals") (fun e => return f!"solveGoals {Lean.exceptEmoji e}") do
  match goals with
  | .unit _ =>
    trace[Lampe.SL] "Finished working through goals"
    let [goal] ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.move_to_sinks) | throwError "unexpected goals in move_to_sinks"
    let (pre, post, goal) ← normalizeSides goal pre sinks
    pure (default, pre, post, goal)
  | .star _ l r => do
    try
      let itemG :: restG :: impls ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.solve_compose_with_sinks) | throwError "unexpected goals in solve_compose_with_sinks"
      let goals ← solveGoal itemG pre l
      let restGExpr ← restG.instantiateMVarsInType
      let (pre, post) ← parseEntailment restGExpr
      let (pre, restG) ← normalizePre restG pre post
      let (moreGoals, pre, sinks, goal) ← solveGoals restG pre r sinks
      pure (goals ++ moreGoals ++ SLGoals.mk [] [] impls, pre, sinks, goal)
    catch e =>
      trace[Lampe.SL] "{crossEmoji} Failed to solve goal: {l.printShape} with message {←e.toMessageData.toString}"
      let [restG] ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.rotate_to_sinks) | throwError "unexpected goals in rotate_to_sinks"
      let newSink ← mkAppM ``SLP.star #[l.expr, sinks.expr]
      solveGoals restG pre r (SLTerm.star newSink l sinks)
  | other => do
    try
      let itemG :: restG :: impls ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.solve_compose) | throwError "unexpected goals in solve_compose"
      let goals ← solveGoal itemG pre other
      let restGExpr ← restG.instantiateMVarsInType
      let (pre, post) ← parseEntailment restGExpr
      let (pre, post, restG) ← normalizeSides restG pre post
      pure (goals ++ SLGoals.mk [] [] impls, pre, post, restG)
    catch e =>
      trace[Lampe.SL] "{crossEmoji} Failed to solve goal: {other.printShape} with message {←e.toMessageData.toString}"
      let gExpr ← goal.instantiateMVarsInType
      let (pre, post) ← parseEntailment gExpr
      let (pre, post, goal) ← normalizeSides goal pre post
      trace[Lampe.SL] "Reparsed goal: {←ppExpr pre.expr} ⊢ ({←ppExpr post.expr})"
      pure (default, pre, post, goal)

partial def doPullWith (pre : SLTerm) (goal : MVarId) (puller finalPuller : Expr): TacticM (MVarId × List MVarId) := goal.withContext $ do
  match pre with
  | .star _ (.lift _) r =>
    let goal :: impls ← goal.apply' puller | throwError "unexpected goals in doPullWith"
    let (fv, goal) ← goal.intro1
    trace[Lampe.SL] "Pulled out: {fv.name}"
    let (g, gs) ← doPullWith r goal puller finalPuller
    pure (g, impls ++ gs)
  | .lift _ =>
    let goal :: impls ← goal.apply' finalPuller | throwError "unexpected goals in doPullWith"
    let (_, goal) ← goal.intro1
    pure (goal, impls)
  | _ => pure (goal, [])

partial def pullPures (goal : MVarId) (pre post : SLTerm): TacticM (MVarId × List MVarId) := goal.withContext $ withTraceNode `Lampe.SL (tag := "pullPures") (fun e => return f!"pullPures {Lean.exceptEmoji e}") do
  let (goal, puller, finalPuller) ← if post.hasMVars then
    let (p, pmv, postEqMVars) ← Lampe.SL.split_by (fun t => match t with
      | SLTerm.mvar _ => pure .right
      | _ => pure .left
    ) post
    match pmv with
    | .mvar _ => pure ()
    | _ => throwError "unexpected result in pullPures"
    let newPost ← mkAppM ``SLP.star #[p.expr, pmv.expr]
    let preEq ← mkAppM ``Eq.refl #[pre.expr]
    let goal ← rewriteSides goal pre.expr newPost preEq postEqMVars
    pure (goal, ←mkConstWithFreshMVarLevels ``Internal.skip_pure_evidence, ←mkConstWithFreshMVarLevels ``Internal.skip_final_pure_evidence)
  else
    pure (goal, ←mkConstWithFreshMVarLevels ``Lampe.SLP.pure_left, ←mkConstWithFreshMVarLevels ``Lampe.SLP.pure_left')
  doPullWith pre goal puller finalPuller

partial def doApplyExis (goal : MVarId) (postExis : SLTerm) : TacticM (MVarId × List MVarId) := do
  match postExis with
  | SLTerm.exi _ _ =>
    let goal :: goals ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.apply_exi) | throwError "unexpected goals in apply_exi"
    pure (goal, goals)
  | SLTerm.star _ _ r => do
    let goal :: goals ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.apply_exi_star) | throwError "unexpected goals in apply_exi_star"
    let (goal, g₂) ← doApplyExis goal r
    pure (goal, goals ++ g₂)
  | _ => pure (goal, [])

partial def applyExis (goal : MVarId) (pre post : SLTerm): TacticM (MVarId × List MVarId) := goal.withContext do
  let (p, pmv, postEqMVars) ← Lampe.SL.split_by (fun t => match t with
    | SLTerm.exi _ _ => pure .left
    | _ => pure .right
  ) post
  let newPost ← mkAppM ``SLP.star #[p.expr, pmv.expr]
  let preEq ← mkAppM ``Eq.refl #[pre.expr]
  let goal ← rewriteSides goal pre.expr newPost preEq postEqMVars
  doApplyExis goal p

mutual

partial def solveSinks (goal : MVarId) (pre post : SLTerm): TacticM SLGoals := goal.withContext $ withTraceNode `Lampe.SL (tag := "solveSinks") (fun e => return f!"solveSinks {Lean.exceptEmoji e}") do
  trace[Lampe.SL] "Current goal: {←ppExpr pre.expr} ⊢ ({←ppExpr post.expr})"
  match post with
  | .mvar _ =>
    let impls ← goal.apply' (←mkConstWithFreshMVarLevels ``SLP.entails_self)
    return SLGoals.mk [] [] impls
  | .top _ =>
    let impls ← goal.apply' (←mkConstWithFreshMVarLevels ``SLP.entails_top)
    return SLGoals.mk [] [] impls
  | _ => pure $ SLGoals.mk [goal] [] []

partial def pullExisLoop (goal : MVarId): TacticM (MVarId × List MVarId) := goal.withContext do
  let tp ← goal.instantiateMVarsInType
  let (l, _) ← parseEntailment tp
  match l with
  | .exi _ _ =>
    let goal :: impls ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.shift_exists_to_mvar) | throwError "unexpected goals in shift_exists_to_mvar"
    goal.withContext do
      let (_, goal) ← goal.intro1
      let (r, rs) ← pullExisLoop goal
      pure $ (r, impls ++ rs)
  | _ => pure (goal, [])

partial def pullExis (pre post : SLTerm) (goal : MVarId): TacticM (MVarId × List MVarId) := goal.withContext do
  let (goals, sink, postEq) ← Lampe.SL.split_by (fun t => match t with
  | SLTerm.mvar _ => pure .right
  | SLTerm.top _ => pure .right
  | _ => pure .left
  ) post
  let newPost ← mkAppM ``SLP.star #[goals.expr, sink.expr]
  let (pre, preEq) ← Lampe.SL.surfaceExis pre
  let goal ← rewriteSides goal pre newPost preEq postEq
  let (goal, impls) ← match sink with
  | .mvar _ => pure (goal, [])
  | .top _ =>
    let g :: impls ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.star_top_of_star_mvar) | throwError "unexpected goals in star_top_of_star_mvar"
    pure (g, impls)
  | _ => throwError "unsupported sink shape"
  let (g, r) ← pullExisLoop goal
  pure (g, r ++ impls)

partial def parseAndNormalizeEntailment (goal : MVarId): TacticM (SLTerm × SLTerm × MVarId) := goal.withContext do
  let target ← goal.instantiateMVarsInType
  let (pre, post) ← parseEntailment target
  let (pre, post, goal) ← normalizeSides goal pre post
  return (pre, post, goal)

partial def solveEntailment (goal : MVarId): TacticM SLGoals := goal.withContext $ withTraceNode `Lampe.SL (tag := "solveEntailment") (fun e => return f!"solveEntailment {Lean.exceptEmoji e}") do
  let (pre, post, goal) ← parseAndNormalizeEntailment goal
  trace[Lampe.SL] "Initial goal: {←ppExpr pre.expr} ⊢ ({←ppExpr post.expr})"
  let (goal, impls₁) ← pullExis pre post goal
  let (pre, post, goal) ← parseAndNormalizeEntailment goal
  let (goal, impls₂) ← pullPures goal pre post
  let (pre, post, goal) ← parseAndNormalizeEntailment goal
  let (goal, exiGoals) ← applyExis goal pre post

  goal.withContext do
    let target ← goal.instantiateMVarsInType
    let (pre, post) ← parseEntailment target
    let (pre, preEq) ← Lampe.SL.norm pre
    let (post, postEq) ← Lampe.SL.norm post
    let (goals, sinks, postEqSplit) ← Lampe.SL.split_by (fun t => match t with
      | SLTerm.mvar _ => pure .right
      | SLTerm.top _ => pure .right
      | _ => pure .left
    ) post
    let postExpr ← mkAppM ``SLP.star #[goals.expr, sinks.expr]
    let postEqTotal ← mkAppM ``Eq.trans #[postEq, postEqSplit]
    let goal ← rewriteSides goal pre.expr postExpr preEq postEqTotal

    trace[Lampe.SL] "Current goal: {←ppExpr pre.expr} ⊢ ({←ppExpr goals.expr}) ⋆ ({←ppExpr sinks.expr})"

    let (moreGoals, pre, post, goal) ← solveGoals goal pre goals sinks
    let res ← solveSinks goal pre post
    pure $ res ++ moreGoals ++ SLGoals.mk [] exiGoals (impls₁ ++ impls₂)

end

syntax "sl" : tactic
elab "sl" : tactic => do
  let target ← getMainGoal
  let newGoals ← solveEntailment target
  replaceMainGoal newGoals.flatten


set_option trace.Lampe.SL true

-- example : (⟦⟧ : SLP (State p)) ⊢ ⟦⟧ := by
--   apply SLP.entails_trans
--   sl
--   sl

-- example {R : α → SLP (State p)} : (Q ⋆ (∃∃x, R x) ⊢ Q ⋆ (∃∃x, R x)) := by
--   apply SLP.entails_trans
--   · sl
--     simp
--     apply SLP.entails_self
--   -- ·



-- example {Q : α → SLP (State p)} : Q x ⋆ [λ f ↦ fb ] ⊢ ⟦True⟧ ⋆ ∀∀ v, ⟦v = some x⟧ -⋆ ((∃∃h, Q (v.get h)) ⋆ [λ f ↦ fb ]) ⋆ ⊤ := by
--   sl <;> simp_all
