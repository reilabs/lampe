import Lampe.SeparationLogic.State
import Lampe.Hoare.SepTotal
import Lampe.Hoare.Builtins
import Lampe.Syntax

open Lean Elab.Tactic Parser.Tactic Lean.Meta Qq

partial def applyImpl (goal : MVarId) (impl : TSyntax `term) : TacticM $ List MVarId := do
  let newGoals ← evalTacticAt (←`(tactic|
    apply Lampe.TraitResolution.ok (impl := $impl) (implGenerics := h![]) (h_mem := by tauto) <;> (first | rfl | tauto)
  )) goal
  pure newGoals

syntax "apply_impl" term : tactic
elab "apply_impl" impl:term : tactic => do
  let mainGoal ← getMainGoal
  let newGoals ← applyImpl mainGoal impl
  replaceMainGoal newGoals

partial def tryImpls (allImpls : List $ TSyntax `term) : TacticM Unit := do
  let oldState ← saveState
  let mainGoal ← getMainGoal
  match allImpls with
  | impl :: impls => do
    let subGoals ← applyImpl mainGoal impl
    if subGoals.length > 0 then
      oldState.restore
      tryImpls impls
    else
      replaceMainGoal subGoals
      return ()
  | [] => throwError "no impl applies"

syntax "try_impls" "[" term,* "]" : tactic
elab "try_impls" "[" impls:term,* "]" : tactic => do
  tryImpls impls.getElems.toList

partial def extractImpls (expr : Lean.Expr) : TacticM $ List (TSyntax `term) := match expr with
  | (.app (.const `List.nil _) _) => pure []
  | (.const ident r) => do
    let mkExpr ← whnf (.const ident r)
    extractImpls mkExpr
  | .app (.app (.const `Lampe.Env.mk _) _) impls => do
    let impls ← whnf impls
    extractImpls impls
  | .app (.app (.app (.const `List.cons _) _) (.const implName _)) rem => do
    let implSyn ← `($(mkIdent implName).2)
    let rem ← whnf rem
    pure (implSyn :: (← extractImpls rem))
  | _ => throwError s!"failed to match with {expr}"

syntax "try_impls_all" term : tactic
elab "try_impls_all" envSyn:term : tactic => do
  let envExpr ← elabTerm envSyn none
  let impls ← extractImpls envExpr
  tryImpls impls
