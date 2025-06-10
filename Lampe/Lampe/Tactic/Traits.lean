import Lampe.SeparationLogic.State
import Lampe.Hoare.SepTotal
import Lampe.Hoare.Builtins
import Lampe.Syntax

open Lean Elab.Tactic Parser.Tactic Lean.Meta Qq

def applyImpl (goal : MVarId) (impl : TSyntax `term) (generics : List $ TSyntax `term) : TacticM $ List MVarId := do
  let generics ← Lampe.mkHListLit generics
  let newGoals ← evalTacticAt (←`(tactic|
    apply Lampe.TraitResolution.ok (impl := $impl) (implGenerics := $generics) (h_mem := by tauto) <;> (first | rfl | tauto)
  )) goal
  pure newGoals

def tryImpls (allImpls : List $ TSyntax `term) (generics : List $ TSyntax `term) : TacticM Unit := do
  let oldState ← saveState
  let mainGoal ← getMainGoal
  match allImpls with
  | impl :: impls => do
    let subGoals ← applyImpl mainGoal impl generics
    if subGoals.length > 0 then
      oldState.restore
      tryImpls impls generics
    else
      replaceMainGoal subGoals
      return ()
  | [] => throwError "no impl applies"

partial def extractImpl (expr : Lean.Expr) : TacticM $ TSyntax `term := match expr with
| .const name us => do extractImpl (← whnf (.const name us))
| .app (.app (.app (.const `Prod.snd _) _) _) implPairExpr => extractImpl implPairExpr
| .app (.app (.app (.app (.const `Prod.mk _) _) _) _) implExpr => extractImpl implExpr
| .app (.app (.app (.app (.app (.app (.const `Lampe.TraitImpl.mk _) _) _) _) _) _) _ => do `($(← expr.toSyntax))
| _ => throwError s!"failed to match with {expr} in impl extraction"

partial def extractImpls (expr : Lean.Expr) : TacticM $ List (TSyntax `term) := match expr with
  | .const name us => do extractImpls (← whnf (.const name us))
  | .app (.const `Lampe.Env.traits _) envExpr => extractImpls envExpr
  | .app (.app (.const `Lampe.Env.mk _) _) implsExpr => extractImpls implsExpr
  | .app (.app (.app (.const `List.cons _) _) implExpr) rem => do
    let implSyn ← extractImpl implExpr
    pure (implSyn :: (← extractImpls rem))
  | .app (.const `List.nil _) _ => pure []
  | _ => throwError s!"failed to match with {expr}"

syntax "apply_impl" "[" term,* "]" term : tactic
syntax "try_impls" "[" term,* "]" "[" term,* "]" : tactic
syntax "try_impls_all" "[" term,* "]" term : tactic

/--
`apply_impl` applies a given trait implementation `TraitImpl` to the main goal, which must be a `TraitResolution`.

Example:
```
apply_impl [Tp.field] t1 -- applies `t1` with impl generics instantiated to `h![Tp.field]`
```
-/
elab "apply_impl" "[" generics:term,* "]" impl:term : tactic => do
  let mainGoal ← getMainGoal
  let newGoals ← applyImpl mainGoal impl generics.getElems.toList
  replaceMainGoal newGoals

/--
`try_impls` takes a comma separated sequence of `TraitImpl`s in square brackets,
and it tries them one by one by calling `apply_impl` until one of them succeeds.

Example:
```
try_impls [Tp.field] [t1, t2] -- tries `t1` and `t2` with impl generics instantiated to `h![Tp.field]`
```
-/
elab "try_impls" "[" generics:term,* "]" "[" impls:term,* "]" : tactic => do
  tryImpls impls.getElems.toList generics.getElems.toList

/--
`try_impls_all` takes an `Lampe.Env`, and tries all the trait impls one by one to solve the main `TraitResolution` goal.

Example:
```
def env : Lampe.Env := ⟨[], [⟨"TraitName", t1⟩, ⟨"TraitName", t2⟩]⟩

try_impls_all [Tp.field] env -- tries `t1` and `t2` with impl generics instantiated to `h![Tp.field]`
```
-/
elab "try_impls_all" "[" generics:term,* "]" envSyn:term : tactic => do
  let envExpr ← elabTerm envSyn none
  let impls ← extractImpls envExpr
  tryImpls impls generics.getElems.toList
