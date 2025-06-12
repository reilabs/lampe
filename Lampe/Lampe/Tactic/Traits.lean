import Lampe.SeparationLogic.State
import Lampe.Hoare.SepTotal
import Lampe.Hoare.Builtins
import Lampe.Syntax

open Lean Elab.Tactic Parser.Tactic Lean.Meta Qq

initialize
  registerTraceClass `Lampe.Traits

/-- Extract all the `TraitImpl`s from a `Lampe.Env` -/
partial def extractAllImpls (envExpr : Expr) : TacticM $ List (Expr × Expr) := do
  let traitsListExpr ← mkAppM `Lampe.Env.traits #[envExpr]
  let reducedTraitsListExpr ← withAtLeastTransparency .all (whnf traitsListExpr)

  let rec go (listExpr : Expr) : TacticM $ List (Expr × Expr) := do
    let currentExpr ← withAtLeastTransparency .all <| whnf listExpr

    if currentExpr.isAppOfArity ``List.cons 3 then
      let args := currentExpr.getAppArgs
      let headExpr ← whnf args[1]!
      let tailExpr := args[2]!
      let_expr Prod.mk _ _ name impl := headExpr
        | throwError m!"unable to extract {← ppExpr headExpr} from environment {← ppExpr envExpr}"
      let restImpls ← go tailExpr
      return (name, impl) :: restImpls

    else if currentExpr.isAppOfArity ``List.nil 1 then
      return []

    else if currentExpr.isAppOfArity ``List.append 3 then
      let args := currentExpr.getAppArgs
      let list1Expr := args[1]!
      let list2Expr := args[2]!
      let impls1 ← go list1Expr
      let impls2 ← go list2Expr
      return impls1 ++ impls2

    else
      throwError m!"unable to match on {← ppExpr currentExpr} in environment {← ppExpr envExpr}"

  go reducedTraitsListExpr

open Lampe in
theorem callTrait_direct_intro {impls : List $ Lampe.Ident × Function}
    (h_trait : TraitResolution Γ ⟨⟨traitName, traitKinds, traitGenerics⟩, selfTp⟩ impls)
    (h_fn : impls.find? (fun (n, _) => n = fnName) = some (fnName, func))
    (hkc : func.generics = kinds)
    (htci : (func.body _ (hkc ▸ generics) |>.argTps) = argTps)
    (htco : (func.body _ (hkc ▸ generics) |>.outTp) = outTp)
    (h_hoare: STHoare p Γ H (htco ▸ (func.body _ (hkc ▸ generics) |>.body (htci ▸ args))) Q) :
    STHoare p Γ H (Expr.call argTps outTp (.trait (some selfTp) traitName traitKinds traitGenerics fnName kinds generics) args) Q := by
  apply STHoare.callTrait_intro (selfTp := selfTp) (traitName := traitName) (traitKinds := traitKinds) (traitGenerics := traitGenerics) (fnName := fnName) (outTp := outTp) (generics := generics)
  · simp [SLP.entails_top]
  · exact h_trait
  · simp only [Option.eq_some_iff_get_eq] at h_fn
    cases h_fn
    rename_i h
    rw [←h]
    simp [List.get_find?_mem]
  · assumption
  · assumption
  · assumption


/--
Tactic to make progress on goals of the form `Expr.call (FuncRef.trait ...)` by trying all of the
trait implementations in a given environment

Usage: `try_all_traits <generics> <environment>`
* generics: A list of values to instantiate the generic type parameters
* environment: The environment to search the trait implementation
-/
elab "try_all_traits" "[" generics:term,* "]" env:term : tactic => do
  let envExpr ← elabTerm env none
  let impls ← extractAllImpls envExpr
  let generics ← Lampe.mkHListLit generics.getElems.toList
  let oldState ← saveState
  let mainGoal ← getMainGoal

  for (name, impl) in impls do
    trace[Lampe.Traits] m!"attempting trait {← ppExpr name}"

    let implExprImpls ← mkAppM `Lampe.TraitImpl.impl #[impl]
    let funcList ←
      (withAtLeastTransparency .all (whnf (mkApp implExprImpls (← elabTerm generics none))))

    let some (_, funcs) := funcList.listLit? |
      throwError m!"unable to match on {← ppExpr funcList} in trait implementation {← ppExpr impl}"

    for func in funcs do
      let funcArgs := func.getAppArgs
      let funcFunc := funcArgs.reverse[0]!
      let funcName := funcArgs.reverse[1]!

      trace[Lampe.Traits] m!"  attempting function {← ppExpr funcName}"
      -- In order for the metavariables to unify in the right way, we need to run these
      -- tactics in this order as otherwise `tauto` is overly eager to fill in data
      -- incorrectly
      try
        -- `callTrait_direct_intro` on the main goal
        let callDirectGoals ← evalTacticAt (←`(tactic|
          apply callTrait_direct_intro (func := $(←funcFunc.toSyntax))
        )) mainGoal

        let traitResGoal := callDirectGoals[0]!
         -- start filling in the `TraitResolution` goal
        let traitResGoals ← evalTacticAt (←`(tactic|
          apply Lampe.TraitResolution.ok (impl := $(← impl.toSyntax)) (implGenerics := $generics) (h_mem := by tauto)
        )) traitResGoal

        -- solve the `callTrait_direct_intro` goals first
        for goal in callDirectGoals.drop 1 do
          let newGoals ← evalTacticAt (← `(tactic|
            first | try tauto | try with_unfolding_all rfl
          )) goal
          pushGoals newGoals

        -- finally solve the `TraitResolution` goals
        for goal in traitResGoals do
          let goals ← evalTacticAt (←`(tactic| first | try tauto | with_unfolding_all rfl)) goal
          pushGoals goals

        if (← getUnsolvedGoals).length == 1 then
          -- one last `simp only` call to clean up the goal state
          evalTactic (← `(tactic| simp only))
          return
        else
          oldState.restore
      catch _ =>
        oldState.restore

  oldState.restore
  throwError m!"no matching trait implementation found in environment {← ppExpr envExpr}"

