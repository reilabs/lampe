import Lampe.SeparationLogic.State
import Lampe.Hoare.SepTotal
import Lampe.Hoare.Builtins
import Lampe.Syntax

open Lean Elab.Tactic Parser.Tactic Lean.Meta Qq

partial def extractImpl (expr : Lean.Expr) : TacticM $ TSyntax `term := do
  match_expr expr with
  | Prod.mk _ _ _name impl => return ← impl.toSyntax
  | _ => throwError "Didn't expect that..."

partial def extractAllImpls (envExpr : Expr) : TacticM $ List (TSyntax `term) := do
  let traitsListExpr ← mkAppM `Lampe.Env.traits #[envExpr]
  let reducedTraitsListExpr ← withAtLeastTransparency .all <| whnf traitsListExpr

  let rec go (listExpr : Expr) : TacticM $ List (TSyntax `term) := do
    dbg_trace "-------------------------------"
    dbg_trace "RUNNING ON: listExpr {listExpr}"
    dbg_trace "-------------------------------"

    let currentExpr ← withAtLeastTransparency .all <| whnf listExpr
    if currentExpr.isAppOfArity ``List.cons 3 then
      dbg_trace "CONS CASE"
      let args := currentExpr.getAppArgs
      let headExpr ← whnf args[1]! -- head
      let tailExpr := args[2]! -- tail
      if headExpr.isAppOfArity ``Prod.mk 4 then
        dbg_trace "EXTRACTING : {headExpr}"
        let implSyntax ← extractImpl headExpr
        let restImpls ← go tailExpr
        return implSyntax :: restImpls
      else
        throwError s!"extractAllImpls: expected Prod.mk in List.cons, got {headExpr}"
    else if currentExpr.isAppOfArity ``List.nil 1 then
      dbg_trace "NIL CASE"
      return []
    else if currentExpr.isAppOfArity ``List.append 3 then
      dbg_trace "APPEND CASE"
      let args := currentExpr.getAppArgs
      let list1Expr := args[1]! -- first list
      let list2Expr := args[2]! -- second list
      let impls1 ← go list1Expr
      let impls2 ← go list2Expr
      return impls1 ++ impls2
    else if currentExpr.isSorry then
      dbg_trace s!"extractAllImpls: encountered sorry at {currentExpr}, treating as empty list part."
      return []
    else
      throwError s!"extractAllImpls: unhandled expression form {currentExpr}"

  go reducedTraitsListExpr

def trait1 : Lampe.TraitImpl := sorry
def trait2 : Lampe.TraitImpl := sorry
def trait3 : Lampe.TraitImpl := sorry
def trait4 : Lampe.TraitImpl := sorry
def trait5 : Lampe.TraitImpl := sorry
def trait6 : Lampe.TraitImpl := sorry
def trait7 : String × Lampe.TraitImpl := ("Trait7", trait6)


def env1 : Lampe.Env := ⟨[], [("Trait1", trait1), ("Trait2", trait2)]⟩
def env2 : Lampe.Env := ⟨[], [("Trait3", trait3), ("Trait4", trait4)]⟩
def env3 : Lampe.Env := ⟨[], [trait7]⟩
def env4 : Lampe.Env := ⟨[], [("Trait5", trait5)]⟩
def env5 := env4
def env6 := env5

def env7 := env1 ++ env2 ++ env3 ++ env6

elab "testing" env:term : tactic => do
  let xs ← extractAllImpls (← elabTerm env none)
  dbg_trace "ALL OF THE REST: {← xs.mapM $ (elabTerm · none)}"
  return ()

example : Prop := by
  testing env7
  sorry

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

elab "try_all_traits" "[" generics:term,* "]" env:term : tactic => do
  let envExpr ← elabTerm env none
  let impls ← extractAllImpls envExpr
  let generics ← Lampe.mkHListLit generics.getElems.toList
  let oldState ← saveState
  let mainGoal ← getMainGoal

  for impl in impls do
    let implExpr ← elabTerm impl none
    let implExprImpls ← whnf (← mkAppM `Lampe.TraitImpl.impl #[implExpr])
    let funcList ← (withAtLeastTransparency .all (whnf (mkApp implExprImpls (← elabTerm generics
    none))))

    let (_, funcs) ← liftOption funcList.listLit?
    dbg_trace "trying impl"

    for func in funcs do
      dbg_trace "trying func"
      let funcArgs := func.getAppArgs
      let funcFunc := funcArgs.reverse[0]!

      try
        dbg_trace "1: {(← getUnsolvedGoals).length}"
        let callDirectGoals ← evalTacticAt (←`(tactic|
          apply callTrait_direct_intro (func := $(←funcFunc.toSyntax))
        )) mainGoal

        dbg_trace "2: {(← getUnsolvedGoals).length}"
        let traitResGoal := callDirectGoals[0]!
        let traitResGoals ← evalTacticAt (←`(tactic|
          apply Lampe.TraitResolution.ok (impl := $impl) (implGenerics := $generics) (h_mem := by tauto)
        )) traitResGoal

        dbg_trace "3: {(← getUnsolvedGoals).length}"
        for goal in callDirectGoals.drop 1 do
          let newGoals ← evalTacticAt (← `(tactic|
            first | try tauto | try with_unfolding_all rfl
          )) goal
          pushGoals newGoals

        dbg_trace "4: {(← getUnsolvedGoals).length}"
        for goal in traitResGoals do
          let goals ← evalTacticAt (←`(tactic| first | try tauto | with_unfolding_all rfl)) goal
          pushGoals goals

        dbg_trace "5: {(← getUnsolvedGoals).length}"
        if (← getUnsolvedGoals).length == 1 then
          dbg_trace "Success!"
          return
        else
          oldState.restore
          dbg_trace "unsolved: {(← getUnsolvedGoals).length}"
      catch _ =>
        oldState.restore

  oldState.restore
  throwError "No trait implementation could be applied successfully"
