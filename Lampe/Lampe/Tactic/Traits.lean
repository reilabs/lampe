import Lampe.SeparationLogic.State
import Lampe.Hoare.SepTotal
import Lampe.Hoare.Builtins
import Lampe.Syntax

import Lean.Meta.Tactic.Simp.Main

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
